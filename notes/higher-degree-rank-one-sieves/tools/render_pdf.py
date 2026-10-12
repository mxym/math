#!/usr/bin/env python3
"""Optional deterministic reading-copy renderer; requires ReportLab."""
from html import escape
from pathlib import Path
import re
from reportlab.lib import colors
from reportlab.lib.enums import TA_CENTER
from reportlab.lib.styles import ParagraphStyle, getSampleStyleSheet
from reportlab.lib.pagesizes import letter
from reportlab.platypus import SimpleDocTemplate, Paragraph, Preformatted, Spacer

ROOT = Path(__file__).resolve().parents[1]


def inline(text):
    # Escape content before adding only renderer-owned markup.
    text = escape(text, quote=False)
    text = re.sub(r'\[([^\]]+)\]\((https://[^\s)]+)\)',
                  lambda m: '<link href="' + escape(m.group(2), quote=True) + '" color="#225b93">' + m.group(1) + '</link>', text)
    text = re.sub(r'`([^`]+)`', r'<font name="Courier" size="8.5">\1</font>', text)
    text = re.sub(r'\*\*([^*]+)\*\*', r'<b>\1</b>', text)
    return text


def footer(canvas, doc):
    canvas.saveState()
    canvas.setFont('Helvetica', 8)
    canvas.setFillColor(colors.HexColor('#66717e'))
    canvas.drawString(54, 32, 'Higher-degree arithmetic sieves | 7 October 2026')
    canvas.drawRightString(letter[0] - 54, 32, str(doc.page))
    canvas.restoreState()


def main():
    source = (ROOT / 'paper.md').read_text()
    if source.startswith('---\n'):
        source = source.split('---\n', 2)[2]
    styles = getSampleStyleSheet()
    styles.add(ParagraphStyle(name='PaperBody', fontName='Times-Roman', fontSize=10,
        leading=13.1, spaceAfter=6, textColor=colors.HexColor('#1c2630')))
    styles.add(ParagraphStyle(name='PaperH1', parent=styles['Heading1'], fontName='Helvetica-Bold',
        fontSize=13, leading=16, spaceBefore=14, spaceAfter=7, keepWithNext=True,
        textColor=colors.HexColor('#173856')))
    styles.add(ParagraphStyle(name='PaperH2', parent=styles['Heading2'], fontName='Helvetica-Bold',
        fontSize=11, leading=14, spaceBefore=10, spaceAfter=6, keepWithNext=True,
        textColor=colors.HexColor('#243e54')))
    styles.add(ParagraphStyle(name='PaperCode', fontName='Courier', fontSize=8.4,
        leading=11, spaceBefore=4, spaceAfter=8, leftIndent=10))
    styles.add(ParagraphStyle(name='PaperBullet', parent=styles['PaperBody'], leftIndent=11,
        firstLineIndent=-9, spaceAfter=4))
    styles.add(ParagraphStyle(name='PaperBulletNext', parent=styles['PaperBullet'], keepWithNext=True))
    styles.add(ParagraphStyle(name='PaperLabel', parent=styles['PaperBody'], keepWithNext=True))
    styles.add(ParagraphStyle(name='PaperTitle', fontName='Helvetica-Bold', fontSize=23,
        leading=27, alignment=TA_CENTER, textColor=colors.HexColor('#173856'), spaceAfter=10))
    styles.add(ParagraphStyle(name='PaperSubtitle', fontName='Helvetica', fontSize=12,
        leading=16, alignment=TA_CENTER, spaceAfter=6))
    story = [Paragraph('Higher-degree arithmetic sieves', styles['PaperTitle']),
        Paragraph('Rank-one completion, restoration, and exact cubic certificates', styles['PaperSubtitle']),
        Paragraph('Arithmetic sieve supplement | 7 October 2026', styles['PaperSubtitle']), Spacer(1, 12)]
    lines = source.splitlines()
    i = 0
    while i < len(lines):
        line = lines[i]
        if not line.strip():
            i += 1
            continue
        if line.startswith('### '):
            story.append(Paragraph(inline(line[4:]), styles['PaperH2']))
            i += 1
        elif line.startswith('## '):
            story.append(Paragraph(inline(line[3:]), styles['PaperH1']))
            i += 1
        elif line.startswith('    '):
            block = []
            while i < len(lines) and (lines[i].startswith('    ') or not lines[i].strip()):
                block.append(lines[i][4:] if lines[i].startswith('    ') else '')
                i += 1
            while block and not block[-1]:
                block.pop()
            story.append(Preformatted('\n'.join(block), styles['PaperCode']))
        else:
            block = [line]
            i += 1
            while i < len(lines) and lines[i].strip() and not lines[i].startswith(('## ', '### ', '    ', '- ')) and not re.match(r'^\d+\. ', lines[i]):
                block.append(lines[i].strip())
                i += 1
            text = ' '.join(block)
            if text.startswith('- '):
                text = '&#8226; ' + inline(text[2:])
                next_nonempty = next((x for x in lines[i:] if x.strip()), '')
                style = styles['PaperBulletNext' if next_nonempty.startswith('- ') else 'PaperBullet']
            else:
                text = inline(text)
                style = styles['PaperLabel' if text in ('Established:', 'Not established:') else 'PaperBody']
            story.append(Paragraph(text, style))
    pdf = SimpleDocTemplate(str(ROOT / 'paper.pdf'), pagesize=letter,
        rightMargin=54, leftMargin=54, topMargin=48, bottomMargin=48,
        title='Higher-degree arithmetic sieves',
        author='Arithmetic sieve supplement',
        subject='Rank-one completion, restoration and exact cubic certificates',
        invariant=1)
    pdf.build(story, onFirstPage=footer, onLaterPages=footer)

if __name__ == '__main__':
    main()
