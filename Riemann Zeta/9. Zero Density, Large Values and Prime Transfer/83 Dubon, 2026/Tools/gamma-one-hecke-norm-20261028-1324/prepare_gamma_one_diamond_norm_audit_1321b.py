from pathlib import Path
import ast,json,re
p=Path(__file__).parent
oldstem='source-gamma-one-diamond-norm-1';newstem='source-gamma-one-diamond-norm-2'
c=json.loads((p/(oldstem+'-audit-config.json')).read_text(encoding='utf-8'))
names=['Dubon2026.SourceFunctionField.GammaOne.'+n for n in ['qbarDiamondAlgebraic','qbarNormAlgebraic']]
for n in names:
 assert n in c['constructions'] and n not in c['theorems']
 c['constructions'].remove(n);c['theorems'].append(n)
c['queries']=c['theorems']+c['constructions']
assert (len(c['theorems']),len(c['constructions']),len(c['queries']),len(c['proofEdges']))==(24,5,29,88)
def write(n,s):
 f=p/n;assert not f.exists(),f;f.write_text(s,encoding='utf-8')
write(newstem+'-audit-config.json',json.dumps(c,indent=2)+'\n')
arr=lambda xs:'#['+', '.join(chr(96)+x for x in xs)+']'
for old,new in [('SourceGammaOneDiamondNormAudit1','SourceGammaOneDiamondNormAudit2'),
 ('SourceGammaOneDiamondNormDependencyAudit1','SourceGammaOneDiamondNormDependencyAudit2'),
 ('SourceGammaOneDiamondNormScratchOwnership1321','SourceGammaOneDiamondNormScratchOwnership1321b')]:
 s=(p/(old+'.lean')).read_text(encoding='utf-8')
 if old.endswith('NormAudit1'):
  s=re.sub(r'(#print axioms [^\n]+\n)+',''.join('#print axioms '+x+'\n' for x in c['queries']),s,count=1)
  for k in ['theorems','constructions']:
   s=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(c[k]),s)
 write(new+'.lean',s)
route=json.loads((p/'source-gamma-one-diamond-norm-audit-route-1321.json').read_text(encoding='utf-8'))
route['auditCorrection']='The first audit correctly rejected two Prop-valued local instances registered as constructions. Lean elaborates them as theorem declarations. The successor registers both as theorems and retains all queries, exhaustive checks, linters and proof-value edges. No mathematical source or verification requirement changes.'
write('source-gamma-one-diamond-norm-audit-route-1321b.json',json.dumps(route,indent=2)+'\n')
for old,new in [('record_gamma_one_diamond_norm_1321.py','record_gamma_one_diamond_norm_1321b.py'),
 ('audit_gamma_one_diamond_norm_1321.ps1','audit_gamma_one_diamond_norm_1321b.ps1')]:
 s=(p/old).read_text(encoding='utf-8')
 for a,b in [(oldstem,newstem),('SourceGammaOneDiamondNormAudit1','SourceGammaOneDiamondNormAudit2'),
  ('SourceGammaOneDiamondNormDependencyAudit1','SourceGammaOneDiamondNormDependencyAudit2'),
  ('SourceGammaOneDiamondNormScratchOwnership1321','SourceGammaOneDiamondNormScratchOwnership1321b'),
  ('source-gamma-one-diamond-norm-audit-route-1321.json','source-gamma-one-diamond-norm-audit-route-1321b.json'),
  ('record_gamma_one_diamond_norm_1321.py','record_gamma_one_diamond_norm_1321b.py')]:s=s.replace(a,b)
 if new.endswith('.py'):ast.parse(s)
 write(new,s)
print(json.dumps(dict(theorems=len(c['theorems']),constructions=len(c['constructions']),queries=len(c['queries']),proofEdges=len(c['proofEdges']),sourceChanged=False)))
