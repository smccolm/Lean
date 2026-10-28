from pathlib import Path
import shutil,json
p=Path(__file__).parent
mods=['SourceComplexWedgeStokes','SourceComplexWedgeLocalLog','SourceComplexWedgeDisc','SourceComplexWedgeIntegral','SourceGammaOneUntwistWedgeIntegral']
ev={m:m for m in mods};ev['SourceComplexWedgeLocalLog']='SourceComplexWedgeLocalLog872c';ev['SourceComplexWedgeDisc']='SourceComplexWedgeDisc872b'
d=p/'wedge-stokes-superseded-874a';d.mkdir()
for m in mods:
 f=p/(m+'.lean');shutil.copy2(f,d/(f.name+'.txt'))
 for ext in ['.log','.exit']:
  q=p/(ev[m]+ext);shutil.copy2(q,d/q.name)
f=p/'SourceComplexWedgeStokes.lean';t=f.read_text(encoding='utf-8')
a=t.index('theorem mul_eq_of_tsupport_subset');b=t.index('theorem fderiv_apply_props',a)
f.write_text(t[:a]+t[b:],encoding='utf-8',newline='\n')
with (p/'wedge-minimal-route-review-874a.json').open('x',encoding='utf-8') as f:json.dump(dict(change='Deferred the unconsumed support-multiplication helper before auditing the actual untwist consumer. All five final theorem interfaces otherwise unchanged; earlier successful source and compile evidence preserved.',removed='Dubon2026.SourceComplexReciprocity.Wedge.mul_eq_of_tsupport_subset'),f,indent=2)
