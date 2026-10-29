from pathlib import Path
import re,json
s=Path(__file__).parent
versions={
'SourceSiegelJacobiFiniteProducts':'1557a','SourceSiegelJacobiGaussProduct':'1558a',
'SourceSiegelJacobiFiniteIdentity':'1559a','SourceSiegelJacobiProductBounds':'1560a',
'SourceSiegelJacobiDominatedLimit':'1561a','SourceSiegelJacobiRangeLimit':'1562a',
'SourceSiegelJacobiProductIdentity':'1563a','SourceSiegelFunction':'1564a',
'SourceSiegelProductCore':'1565a','SourceSiegelThetaIdentification':'1566a',
'SourceSiegelHolomorphic':'1567a','SourceSiegelEtaTransform':'1568a',
'SourceSiegelThetaTransform':'1569a','SourceSiegelInversion':'1570a',
'SourceSiegelSL2Transformation':'1571a','SourceSiegelLevelShiftFactors':'1572a',
'SourceSiegelLevelShifts':'1573a','SourceSiegelResidueReduction':'1574b',
'SourceSiegelProductTransformation':'1575b'}
mods=[m+v for m,v in versions.items()];ths=[];defs=[]
for m in mods:
 f=s/(m+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 c=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',f.read_text(encoding='utf-8'),flags=re.S));ns=re.search(r'^namespace (\S+)',c,re.M)[1]+'.'
 ths += [ns+x for x in re.findall(r'^(?:theorem|lemma)\s+([\w.\x27]+)',c,re.M)]
 defs += [ns+x for x in re.findall(r'^(?:noncomputable )?def\s+([\w.\x27]+)',c,re.M)]
assert len(set(ths+defs))==len(ths+defs)
ns='Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.'
roots=[ns+'Siegel.mdifferentiable_siegelFun',ns+'Siegel.prod_siegelFun_pow_specialLinearGroup_smul']
edges=ths+defs+['ModularForm.multipliable_one_sub_pow','ModularForm.eta_tprod_ne_zero','ModularForm.differentiableAt_eta_tprod','ModularForm.eta_comp_eq_csqrt_I_inv','jacobiTheta₂_functional_equation','hasFDerivAt_jacobiTheta₂','summable_jacobiTheta₂_term_iff','SpecialLinearGroup.SL2Z_generators','tendsto_tsum_of_dominated_convergence']
cfg=dict(modules=mods,theorems=ths,constructions=defs,roots=roots,proofEdges=edges)
arr=lambda xs:'#['+', '.join(chr(96)+x for x in xs)+']'
def write(n,t):
 f=s/n;assert not f.exists();f.write_text(t,encoding='utf-8')
write('siegel-function-versions-1577.json',json.dumps(versions,indent=2)+'\n')
write('siegel-function-preflight-config-1577.json',json.dumps(cfg,indent=2)+'\n')
for a,b in [('SourceIntegralTraceAudit1','SourceSiegelFunctionPreflight1577'),('SourceIntegralTraceDependencyAudit1','SourceSiegelFunctionValuePreflight1577')]:
 c=(s/(a+'.lean')).read_text(encoding='utf-8')
 c='\n'.join('import '+m for m in mods)+'\nimport Mathlib.Tactic\n'+c[c.index('\nopen Lean'):]
 if a=='SourceIntegralTraceAudit1':
  c=re.sub(r'(#print axioms [^\n]+\n)+',''.join('#print axioms '+x+'\n' for x in ths+defs),c,count=1)
  for k,v in [('modules',mods),('theorems',ths),('constructions',defs)]:c=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),c)
  c=re.sub(r'#lint in [^\n]+\n','',c).rstrip()+'\n\n'+''.join('#lint in '+m+'\n' for m in mods)
 else:
  for k,v in [('roots',roots),('localModules',mods),('required',edges)]:c=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),c)
  start=c.index(' occur in the ');end=c.index('; DUB17--20 OPEN.',start)
  c=c[:start]+' occur in the proof value closure of actual Siegel holomorphy and the literal finite product transformation and Gamma1 invariance. Integral expansions, leading unit and peaked auxiliary existence remain open'+c[end:]
 c=c.replace('INTEGRAL TRACE','SIEGEL FUNCTION PREFLIGHT').replace('Frobenius Normalization','Siegel function')
 write(b+'.lean',c)
 c=(s/'audit_peaked_exponent_preflight_1552.ps1').read_text(encoding='utf-8').replace('SourcePeakedExponentPreflight1552',b)
 write('audit_'+b+'_1577.ps1',c)
print(json.dumps(dict(modules=len(mods),theorems=len(ths),constructions=len(defs),edges=len(edges))))
