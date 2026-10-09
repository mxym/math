from pathlib import Path
import concurrent.futures,hashlib,json,subprocess,re,shutil,xml.etree.ElementTree as ET
from PIL import Image,ImageOps,ImageDraw
import argparse
if not __debug__: raise SystemExit('Run without -O or -OO')
parser=argparse.ArgumentParser(description='Render audited distributed PDFs and check text bounds.')
parser.add_argument('--output',type=Path,required=True)
args=parser.parse_args()
BASE=args.output.resolve()
ROOT=Path(__file__).resolve().parents[2]
report=json.loads((BASE/'BUILD_AND_SOURCE_AUDIT.json').read_text())

def render(item):
    out=BASE/item['key'];pages=out/'rendered';pages.mkdir(exist_ok=True)
    previous={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in pages.glob('page-*.png')}
    for old in pages.glob('page-*.png'): old.unlink()
    source=ROOT/item['source_root']/'paper.pdf'
    shutil.copy2(source,out/'paper.pdf')
    bbox=subprocess.check_output(['pdftotext','-bbox',str(source),'-'],text=True)
    (out/'bbox.html').write_text(bbox)
    subprocess.run(['pdftoppm','-r','85','-png',str(out/'paper.pdf'),str(pages/'page')],check=True,capture_output=True)
    images=sorted(pages.glob('page-*.png'));assert len(images)==item['pages']
    raw=(out/'bbox.html').read_text()
    # Poppler exports some math glyph encodings as XML-forbidden controls.
    # Remove those character tokens only; preserve every numeric text box.
    cleaned=re.sub(r'[\x00-\x08\x0b\x0c\x0e-\x1f]','',raw)
    tree=ET.fromstring(cleaned);ns={'h':'http://www.w3.org/1999/xhtml'}
    bounds=[]
    for num,page in enumerate(tree.findall('.//h:page',ns),1):
        w,h=float(page.attrib['width']),float(page.attrib['height'])
        words=page.findall('.//h:word',ns);assert words,(item['key'],'blank page',num)
        lo_x=min(float(x.attrib['xMin']) for x in words);hi_x=max(float(x.attrib['xMax']) for x in words)
        lo_y=min(float(x.attrib['yMin']) for x in words);hi_y=max(float(x.attrib['yMax']) for x in words)
        assert lo_x>=0 and hi_x<=w and lo_y>=0 and hi_y<=h,(item['key'],'cropped text',num)
        bounds.append({'page':num,'words':len(words),'min_x':lo_x,'max_x':hi_x,'min_y':lo_y,'max_y':hi_y})
    contacts=[]
    for first in range(0,len(images),6):
        chosen=images[first:first+6];sheet=Image.new('RGB',(1100,2200),'#e5e7eb');draw=ImageDraw.Draw(sheet)
        for j,path in enumerate(chosen):
            with Image.open(path) as im:thumb=ImageOps.contain(im,(530,690))
            x=(j%2)*550+10;y=(j//2)*730+28
            sheet.paste(thumb,(x,y));draw.text((x,y-20),item['key']+' / page '+str(first+j+1),fill='black')
        target=out/('contact-%02d.png'%(first//6+1));sheet.save(target);contacts.append(str(Path(item['key'])/target.name))
    result={'key':item['key'],'pdf_sha256':item['distributed_pdf_sha256'],'render_dpi':85,
            'xml_control_glyph_tokens_removed_for_parser':len(raw)-len(cleaned),
            'pages':len(images),'text_inside_media_box':True,'page_bounds':bounds,
            'render_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in images},
            'contact_sheets':contacts,'same_render_as_inspected_rebuild':previous=={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in images},'scope':'Full-page renders and media-box text bounds. Contact-sheet inspection assesses layout, not mathematical correctness or every formula glyph.'}
    (out/'VISUAL_LAYOUT.json').write_text(json.dumps(result,indent=2)+'\n')
    print('RENDERED',item['key'],len(images),'pages',flush=True)
    return result

with concurrent.futures.ThreadPoolExecutor(max_workers=3) as ex:results=list(ex.map(render,report['papers']))
(BASE/'VISUAL_LAYOUT_AUDIT.json').write_text(json.dumps({'status':'PASS','papers':results},indent=2)+'\n')
