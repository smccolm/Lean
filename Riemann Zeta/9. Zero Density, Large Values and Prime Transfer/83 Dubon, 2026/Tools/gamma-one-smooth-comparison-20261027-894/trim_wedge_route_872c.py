from pathlib import Path
import shutil,json
p=Path(__file__).parent
loc=p/'SourceComplexWedgeLocalLog.lean'
d=p/'wedge-local-log-superseded-872b';d.mkdir()
shutil.copy2(loc,d/(loc.name+'.txt'))
for ext in ['.log','.exit']:shutil.copy2(p/('SourceComplexWedgeLocalLog872b'+ext),d/('SourceComplexWedgeLocalLog872b'+ext))
t=loc.read_text(encoding='utf-8')
a=t.index('include hE hk hkr in\n\ntheorem D_vEk')
b=t.index('include hΨ hΨ1 hΨa hΦ in',a)
t=t[:a]+t[b:]
loc.write_text(t,encoding='utf-8',newline='\n')
disc=p/'SourceComplexWedgeDisc.lean'
d=p/'wedge-disc-failed-872a';d.mkdir()
shutil.copy2(disc,d/(disc.name+'.txt'))
for ext in ['.log','.exit']:shutil.copy2(disc.with_suffix(ext),d/disc.with_suffix(ext).name)
t=disc.read_text(encoding='utf-8')
assert t.count('D_vEk hE hk hkr, ')==1
disc.write_text(t.replace('D_vEk hE hk hkr, ',''),encoding='utf-8',newline='\n')
with (p/'wedge-minimal-route-review-872c.json').open('x',encoding='utf-8') as f:json.dump(dict(change='Removed the unused D_vEk simp entry and unconsumed helper theorem. The actual local wedge identity is unchanged; its proof already expands D and uses fderiv_vEk. Preserved both earlier successful local proof and failed warning-producing disc evidence.',deferred='D_vEk formula is incidental to this dependency closure.'),f,indent=2)
