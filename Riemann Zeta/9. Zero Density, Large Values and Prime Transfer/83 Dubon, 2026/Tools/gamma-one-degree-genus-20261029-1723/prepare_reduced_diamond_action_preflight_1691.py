from pathlib import Path
import re,json,hashlib
s=Path(__file__).parent
versions={
 'SourceIntegralDiamondReduction':'1670b','SourceIntegralDiamondZeroForward':'1671a',
 'SourceIntegralDiamondZeroEquivalence':'1672a','SourceIntegralDiamondWitness':'1673a',
 'SourceIntegralDiamondNormalizedReduction':'1674a','SourceIntegralDiamondChosenReduction':'1675a',
 'SourceIntegralDiamondSeriesOperations':'1676b','SourceIntegralDiamondReducedOperations':'1677b',
 'SourceIntegralDiamondRatioRelation':'1678b','SourceIntegralDiamondAdditiveSeries':'1679b',
 'SourceIntegralDiamondRatioClosure':'1681b','SourceIntegralDiamondReducedAddition':'1682b',
 'SourceIntegralDiamondFieldPull':'1683c','SourceIntegralDiamondFieldRange':'1684a',
 'SourceIntegralDiamondFieldConstants':'1685b','SourceIntegralDiamondFieldOperations':'1686a',
 'SourceIntegralDiamondComposition':'1687b','SourceIntegralDiamondFieldComposition':'1688b',
 'SourceIntegralDiamondFieldIdentity':'1689a','SourceIntegralDiamondFieldAction':'1690a'}
mods=[m+v for m,v in versions.items()];ths=[];defs=[]
for m in mods:
 f=s/(m+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 c=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',f.read_text(encoding='utf-8'),flags=re.S))
 ns=re.search(r'^namespace (\S+)',c,re.M)[1]+'.'
 ths += [ns+x for x in re.findall(r'^(?:theorem|lemma)\s+([\w.\x27]+)',c,re.M)]
 defs += [ns+x for x in re.findall(r'^(?:noncomputable )?def\s+([\w.\x27]+)',c,re.M)]
 for x in re.findall(r'^structure\s+([\w.\x27]+)',c,re.M):defs += [ns+x,ns+x+'.mk']
assert len(set(ths+defs))==len(ths+defs)
ns='Dubon2026.SourceFunctionField.IntegralDiamond.'
roots=[ns+n for n in ['reducedFieldAction','reducedFieldAction_apply',
 'reducedFieldAction_eq_one_of_signed_gammaOne','reducedDiamond_ratio_eq',
 'reducedDiamond_zero_iff','coe_reducedFieldPullHom']]
upcfg=json.loads((s/'source-even-weight-integral-diamond-1-audit-config.json').read_text(encoding='utf-8'))
edges=ths+defs+upcfg['proofEdges']+[
 'Dubon2026.SourceFunctionField.GammaOne.exists_even_integral_ratio',
 'Dubon2026.SourceFunctionField.IntegralTrace.slash_neg_even',
 'Dubon2026.SourceFunctionField.GammaOne.mem_plusMinus_iff']
edges=list(dict.fromkeys(edges))
up=[]
for fname in ['even-weight-fricke-trace-versions-1643.json','even-weight-fricke-uniform-versions-1653.json','even-weight-full-slash-versions-1661.json']:
 up+=list(json.loads((s/fname).read_text(encoding='utf-8')))
v=json.loads((s/'even-weight-integral-diamond-versions-1669.json').read_text(encoding='utf-8'))
up += [m+ver for m,ver in v.items()]
cfg=dict(modules=mods,theorems=ths,constructions=defs,roots=roots,proofEdges=edges,localModules=mods+up)
arr=lambda xs:'#['+', '.join(chr(96)+x for x in xs)+']'
def write(n,t):
 f=s/n;assert not f.exists(),f;f.write_text(t,encoding='utf-8')
write('reduced-diamond-action-versions-1691.json',json.dumps(versions,indent=2)+'\n')
write('reduced-diamond-action-preflight-config-1691.json',json.dumps(cfg,indent=2)+'\n')
for a,b in [('SourceEvenWeightIntegralDiamondPreflight1668','SourceReducedDiamondActionPreflight1691'),('SourceEvenWeightIntegralDiamondValuePreflight1668','SourceReducedDiamondActionValuePreflight1691')]:
 c=(s/(a+'.lean')).read_text(encoding='utf-8')
 c='\n'.join('import '+m for m in mods)+'\nimport Mathlib.Tactic\n'+c[c.index('\nopen Lean'):]
 if 'Value' not in a:
  c=re.sub(r'(#print axioms [^\n]+\n)+',''.join('#print axioms '+x+'\n' for x in ths+defs),c,count=1)
  for k,v in [('modules',mods),('theorems',ths),('constructions',defs)]:c=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),c)
  c=re.sub(r'#lint in [^\n]+\n','',c).rstrip()+'\n\n'+''.join('#lint in '+m+'\n' for m in mods)
  c=c.replace('Siegel expansion','Reduced diamond action')
 else:
  for k,v in [('roots',roots),('localModules',cfg['localModules']),('required',edges)]:c=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),c)
  start=c.index(' occur in the ');end=c.index('; DUB17--20 OPEN.',start)
  c=c[:start]+' occur in the proof value closure of the actual original reduced-field action and its explicit representative, zero and signed-kernel consumers. Actual integral diamond witnesses, all ratio relations, field operations and composition are proved. Exact kernel equality, full-base fixation, degree/genus and higher continuation remain open'+c[end:]
 c=c.replace('EVEN WEIGHT INTEGRAL DIAMOND PREFLIGHT','REDUCED DIAMOND ACTION PREFLIGHT')
 write(b+'.lean',c)
 c=(s/('audit_'+a+'_1668.ps1')).read_text(encoding='utf-8').replace(a,b)
 write('audit_'+b+'_1691.ps1',c)
c=(s/'audit_even_weight_integral_diamond_preflight_1668.ps1').read_text(encoding='utf-8').replace('1668','1691').replace('EvenWeightIntegralDiamond','ReducedDiamondAction')
write('audit_reduced_diamond_action_preflight_1691.ps1',c)
print(json.dumps(dict(modules=len(mods),theorems=len(ths),constructions=len(defs),edges=len(edges))))
