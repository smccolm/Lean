from pathlib import Path
import re,json
s=Path(__file__).parent
versions={
'SourceIntegralSeriesScalarDescent':'1642b','SourceIntegralSeriesCommonDenominator':'1644b',
'SourceGammaOneAlgebraicCuspDenominator':'1645b','SourceIntegralDiscriminantCancellation':'1646b',
'SourceGammaOneAlgebraicFormDenominator':'1647a','SourceEvenWeightBalance':'1648b',
'SourceEvenWeightFrickeCommonDenominator':'1649c','SourceEvenWeightUniformFrickeIntegrality':'1650b'}
mods=[m+v for m,v in versions.items()];ths=[];defs=[]
for m in mods:
 f=s/(m+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 c=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',f.read_text(encoding='utf-8'),flags=re.S));ns=re.search(r'^namespace (\S+)',c,re.M)[1]+'.'
 ths += [ns+x for x in re.findall(r'^(?:theorem|lemma)\s+([\w.\x27]+)',c,re.M)]
 defs += [ns+x for x in re.findall(r'^(?:noncomputable )?def\s+([\w.\x27]+)',c,re.M)]
assert len(set(ths+defs))==len(ths+defs)
ns='Dubon2026.SourceFunctionField.IntegralFricke.'
roots=[ns+'exists_level_power_integral_even_fricke_coefficients']
edges=ths+defs+[
ns+'even_weight_coeff_slash_fricke_mem_RN',
ns+'even_weight_level_power_fricke_of_common_denominator',
'Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.exists_gamma1_peaked_auxiliary_form_twelve_dvd',
'Dubon2026.SourceFunctionField.IntegralTrace.even_weight_slash_coeff_mem_of_peaked_auxiliary',
'Dubon2026.SourceFricke.span_gammaOne_integral_cuspForms_eq_top',
'Dubon2026.SourceFunctionField.qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit',
'Dubon2026.SourceFunctionField.dedekindEtaUnit_mul_inv',
'Dubon2026.SourceFunctionField.IntegralTrace.coeff_mul_mem',
'Dubon2026.SourceFricke.gammaOneQCoeffLinear',
'Dubon2026.cuspRestrictSubgroup',
'Algebra.IsAlgebraic.exists_integral_multiples',
'LinearMap.exists_leftInverse_of_injective']
cfg=dict(modules=mods,theorems=ths,constructions=defs,roots=roots,proofEdges=edges)
arr=lambda xs:'#['+', '.join(chr(96)+x for x in xs)+']'
def write(n,t):
 f=s/n;assert not f.exists();f.write_text(t,encoding='utf-8')
write('even-weight-fricke-uniform-versions-1651.json',json.dumps(versions,indent=2)+'\n')
write('even-weight-fricke-uniform-preflight-config-1651.json',json.dumps(cfg,indent=2)+'\n')
for a,b in [('SourceIntegralTraceAudit1','SourceEvenWeightFrickeUniformPreflight1651'),('SourceIntegralTraceDependencyAudit1','SourceEvenWeightFrickeUniformValuePreflight1651')]:
 c=(s/(a+'.lean')).read_text(encoding='utf-8')
 c='\n'.join('import '+m for m in mods)+'\nimport Mathlib.Tactic\n'+c[c.index('\nopen Lean'):]
 if a=='SourceIntegralTraceAudit1':
  c=re.sub(r'(#print axioms [^\n]+\n)+',''.join('#print axioms '+x+'\n' for x in ths+defs),c,count=1)
  for k,v in [('modules',mods),('theorems',ths),('constructions',defs)]:c=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),c)
  c=re.sub(r'#lint in [^\n]+\n','',c).rstrip()+'\n\n'+''.join('#lint in '+m+'\n' for m in mods)
 else:
  for k,v in [('roots',roots),('localModules',mods),('required',edges)]:c=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),c)
  start=c.index(' occur in the ');end=c.index('; DUB17--20 OPEN.',start)
  c=c[:start]+' occur in the proof value closure of the actual even-weight Fricke trace consumer. The constructed auxiliary discharges all trace auxiliary hypotheses; coefficientwise level-power integrality is proved and a uniform exponent follows from an explicit common integer denominator. Constructing that common denominator, full slash integrality, reduced field action and degree/genus remain open'+c[end:]
 c=c.replace('INTEGRAL TRACE','EVEN WEIGHT FRICKE UNIFORM PREFLIGHT').replace('Frobenius Normalization','Siegel expansion')
 write(b+'.lean',c)
 c=(s/'audit_peaked_exponent_preflight_1552.ps1').read_text(encoding='utf-8').replace('SourcePeakedExponentPreflight1552',b)
 write('audit_'+b+'_1651.ps1',c)
print(json.dumps(dict(modules=len(mods),theorems=len(ths),constructions=len(defs),edges=len(edges))))
