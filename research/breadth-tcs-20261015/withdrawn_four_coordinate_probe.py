"""Bounded exact search for a smaller collision of one withdrawn compressor."""
from pathlib import Path
import hashlib,json,time
from withdrawn_compressor_repair_probe import find_collision
R=Path(__file__).parent
start=time.monotonic();found=None;count=0
for bitset in range(1,1<<16):
    if time.monotonic()-start>120:break
    C=[c for c in range(16) if (bitset>>c)&1]
    found=find_collision(4,C);count+=1
    if found:break
record={'n':4,'nonempty_classes_processed_in_numeric_bitset_order':count,'all_nonempty_classes_completed':count==(1<<16)-1,'collision':found,'elapsed_seconds':time.monotonic()-start,'scope':'Only this prescribed withdrawn compressor under canonical increasing coordinate order; no statement about existence of other schemes. A time limit would leave the remaining classes unchecked.','source_sha256':{p:hashlib.sha256((R/p).read_bytes()).hexdigest() for p in ['withdrawn_four_coordinate_probe.py','withdrawn_compressor_repair_probe.py']}}
(R/'WITHDRAWN_FOUR_COORDINATE_CONTROL.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
print(json.dumps(record,indent=2))
