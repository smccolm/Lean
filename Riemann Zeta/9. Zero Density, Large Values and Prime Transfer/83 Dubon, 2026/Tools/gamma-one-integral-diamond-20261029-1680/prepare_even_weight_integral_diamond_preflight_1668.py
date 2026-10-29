from pathlib import Path
import re,json
s=Path(__file__).parent
versions={'SourceRationalCuspDiamondFourier':'1664c','SourceRationalDiscriminantCancellation':'1665a','SourceRationalModularDiamondFourier':'1666a','SourceEvenWeightIntegralDiamondForm':'1667a'}
mods=[m+v for m,v in versions.items()];ths=[];defs=[]
for m in mods:
 f=s/(m+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 c=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',f.read_text(encoding='utf-8'),flags=re.S));ns=re.search(r'^namespace (\S+)',c,re.M)[1]+'.'
 ths += [ns+x for x in re.findall(r'^(?:theorem|lemma)\s+([\w.\x27]+)',c,re.M)]
 defs += [ns+x for x in re.findall(r'^(?:noncomputable )?def\s+([\w.\x27]+)',c,re.M)]
assert len(set(ths+defs))==len(ths+defs)
ns='Dubon2026.SourceFunctionField.IntegralSlash.'
roots=[ns+'exists_level_power_integral_even_diamond_form']
edges=ths+defs+[
ns+'exists_level_power_integral_even_slash_coefficients',
'Dubon2026.SourceFunctionField.IntegralFricke.exists_level_power_integral_even_fricke_coefficients',
'Dubon2026.SourceFunctionField.IntegralFricke.exists_common_nat_denominator_even_fricke',
'Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.exists_gamma1_peaked_auxiliary_form_twelve_dvd',
'Dubon2026.SourceFunctionField.IntegralTrace.even_weight_slash_coeff_mem_of_peaked_auxiliary',
'Dubon2026.SourceFricke.exists_rational_cuspWeightImage_diamond_laurent',
'Dubon2026.SourceFricke.represents_rational_discriminantLaurent',
'Dubon2026.SourceFricke.represents_rational_eisensteinFactorLaurent',
'Dubon2026.SourceFricke.exists_integer_unit_eisensteinFactorLaurent',
'Dubon2026.SourceFunctionField.CuspWeightCriterion.slash_mul_eisensteinFactor',
'Dubon2026.SourceFunctionField.dedekindEtaUnit_mul_inv',
'Dubon2026.SourceFunctionField.GammaOne.modularDiamond',
'Dubon2026.SourceFricke.qExpansion_coeff_width']
up=list(json.loads((s/'even-weight-fricke-trace-versions-1643.json').read_text(encoding='utf-8')))+list(json.loads((s/'even-weight-fricke-uniform-versions-1653.json').read_text(encoding='utf-8')))
up+=list(json.loads((s/'even-weight-full-slash-versions-1661.json').read_text(encoding='utf-8')))
cfg=dict(modules=mods,theorems=ths,constructions=defs,roots=roots,proofEdges=edges,localModules=mods+up)
arr=lambda xs:'#['+', '.join(chr(96)+x for x in xs)+']'
def write(n,t):
 f=s/n;assert not f.exists(),f;f.write_text(t,encoding='utf-8')
write('even-weight-integral-diamond-versions-1668.json',json.dumps(versions,indent=2)+'\n')
write('even-weight-integral-diamond-preflight-config-1668.json',json.dumps(cfg,indent=2)+'\n')
for a,b in [('SourceEvenWeightFrickeUniformPreflight1652','SourceEvenWeightIntegralDiamondPreflight1668'),('SourceEvenWeightFrickeUniformValuePreflight1652','SourceEvenWeightIntegralDiamondValuePreflight1668')]:
 c=(s/(a+'.lean')).read_text(encoding='utf-8')
 c='\n'.join('import '+m for m in mods)+'\nimport Mathlib.Tactic\n'+c[c.index('\nopen Lean'):]
 if 'Value' not in a:
  c=re.sub(r'(#print axioms [^\n]+\n)+',''.join('#print axioms '+x+'\n' for x in ths+defs),c,count=1)
  for k,v in [('modules',mods),('theorems',ths),('constructions',defs)]:c=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),c)
  c=re.sub(r'#lint in [^\n]+\n','',c).rstrip()+'\n\n'+''.join('#lint in '+m+'\n' for m in mods)
 else:
  for k,v in [('roots',roots),('localModules',cfg['localModules']),('required',edges)]:c=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),c)
  start=c.index(' occur in the ');end=c.index('; DUB17--20 OPEN.',start)
  c=c[:start]+' occur in the proof value closure of the actual level-cleared integral diamond form consumer. Rational cusp and modular diamond coefficients are derived from the original rational expansion; full slash integrality supplies algebraic integrality; rational algebraic integers give the constructed integer Fourier series. Preservation of reduced relations, full reduced field action and degree/genus remain open'+c[end:]
 c=c.replace('EVEN WEIGHT FRICKE UNIFORM PREFLIGHT','EVEN WEIGHT INTEGRAL DIAMOND PREFLIGHT')
 write(b+'.lean',c)
 c=(s/('audit_'+a+'_1652.ps1')).read_text(encoding='utf-8').replace(a,b)
 write('audit_'+b+'_1668.ps1',c)
write('audit_even_weight_full_slash_preflight_1668.ps1',(s/'audit_even_weight_fricke_uniform_preflight_1652.ps1').read_text(encoding='utf-8').replace('1652','1668').replace('EvenWeightFrickeUniform','EvenWeightIntegralDiamond'))
print(json.dumps(dict(modules=len(mods),theorems=len(ths),constructions=len(defs),edges=len(edges))))
