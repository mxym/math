"""All fixed global orders for the prescribed withdrawn compressor on Warmuth C."""
from pathlib import Path
import itertools,json,hashlib
from withdrawn_compressor_repair_probe import find_collision
R=Path(__file__).parent
C=[3,6,11,12,13,17,21,22,24,26]
records=[]
for perm in itertools.permutations(range(5)):
    Cp=[sum(((c>>old)&1)<<new for new,old in enumerate(perm)) for c in C]
    got=find_collision(5,Cp)
    records.append({'coordinate_order':perm,'collision_found':got is not None,'witness':got})
res={'scope':'All 120 global coordinate orders of one prescribed compressor on this single Warmuth class, with actual partial-sample search in each call until a collision. Not every possible compression scheme.','orders_checked':120,'orders_with_collision':sum(x['collision_found'] for x in records),'records':records,'source_sha256':{p:hashlib.sha256((R/p).read_bytes()).hexdigest() for p in ['withdrawn_all_orders_controls.py','withdrawn_compressor_repair_probe.py']},'new_major_results':0}
(R/'WITHDRAWN_ALL_ORDERS_CONTROL.json').write_text(json.dumps(res,indent=2)+'\n',encoding='utf-8')
print({'orders_checked':120,'orders_with_collision':res['orders_with_collision']})
