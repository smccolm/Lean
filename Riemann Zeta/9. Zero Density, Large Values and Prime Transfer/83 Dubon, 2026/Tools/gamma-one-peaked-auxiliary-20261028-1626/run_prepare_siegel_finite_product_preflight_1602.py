from pathlib import Path
import re,json
s=Path(__file__).parent
versions={
'SourceSiegelFiniteSeriesProducts':'1596b','SourceSiegelProductCoefficients':'1597b',
'SourceSiegelProductLeadingCoefficient':'1599b','SourceSiegelProductPhases':'1600a',
'SourceSiegelFiniteProductExpansion':'1601b'}
mods=[m+v for m,v in versions.items()];ths=[];defs=[]
for m in mods:
 f=s/(m+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 c=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',f.read_text(encoding='utf-8'),flags=re.S));ns=re.search(r'^namespace (\S+)',c,re.M)[1]+'.'
 ths += [ns+x for x in re.findall(r'^(?:theorem|lemma)\s+([\w.\x27]+)',c,re.M)]
 defs += [ns+x for x in re.findall(r'^(?:noncomputable )?def\s+([\w.\x27]+)',c,re.M)]
assert len(set(ths+defs))==len(ths+defs)
ns='Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.FiniteExpansion.'
roots=[ns+'exists_integral_hasSum_prod_siegelFun_pow']
edges=ths+defs+[
'Dubon2026.SourceFunctionField.Realized.hasSum_qParam_mul',
'Dubon2026.SourceFunctionField.Realized.tendsto_atImInfty',
'Dubon2026.SourceFunctionField.IntegralTrace.coeff_mul_mem',
'Dubon2026.SourceFunctionField.IntegralTrace.coeff_pow_mem',
'Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.EulerExpansion.hasSum_coef',
'Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.EulerExpansion.isIntegral_coef',
'Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.EulerExpansion.coef_zero',
'Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.EulerExpansion.isIntegral_N_mul_inv_coef_zero',
'Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.EulerExpansion.zeta_ne_one']
cfg=dict(modules=mods,theorems=ths,constructions=defs,roots=roots,proofEdges=edges)
arr=lambda xs:'#['+', '.join(chr(96)+x for x in xs)+']'
def write(n,t):
 f=s/n;assert not f.exists();f.write_text(t,encoding='utf-8')
write('siegel-finite-product-versions-1602.json',json.dumps(versions,indent=2)+'\n')
write('siegel-finite-product-preflight-config-1602.json',json.dumps(cfg,indent=2)+'\n')
for a,b in [('SourceIntegralTraceAudit1','SourceSiegelFiniteProductPreflight1602'),('SourceIntegralTraceDependencyAudit1','SourceSiegelFiniteProductValuePreflight1602')]:
 c=(s/(a+'.lean')).read_text(encoding='utf-8')
 c='\n'.join('import '+m for m in mods)+'\nimport Mathlib.Tactic\n'+c[c.index('\nopen Lean'):]
 if a=='SourceIntegralTraceAudit1':
  c=re.sub(r'(#print axioms [^\n]+\n)+',''.join('#print axioms '+x+'\n' for x in ths+defs),c,count=1)
  for k,v in [('modules',mods),('theorems',ths),('constructions',defs)]:c=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),c)
  c=re.sub(r'#lint in [^\n]+\n','',c).rstrip()+'\n\n'+''.join('#lint in '+m+'\n' for m in mods)
 else:
  for k,v in [('roots',roots),('localModules',mods),('required',edges)]:c=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),c)
  start=c.index(' occur in the ');end=c.index('; DUB17--20 OPEN.',start)
  c=c[:start]+' occur in the proof value closure of the literal finite Siegel product integral expansion, specified nonzero leading coefficient, level-cleared inverse, phase root of unity and cusp limit. Discriminant adjustment, cusp estimates and peaked auxiliary existence remain open'+c[end:]
 c=c.replace('INTEGRAL TRACE','SIEGEL FINITE PRODUCT PREFLIGHT').replace('Frobenius Normalization','Siegel expansion')
 write(b+'.lean',c)
 c=(s/'audit_peaked_exponent_preflight_1552.ps1').read_text(encoding='utf-8').replace('SourcePeakedExponentPreflight1552',b)
 write('audit_'+b+'_1602.ps1',c)
print(json.dumps(dict(modules=len(mods),theorems=len(ths),constructions=len(defs),edges=len(edges))))
