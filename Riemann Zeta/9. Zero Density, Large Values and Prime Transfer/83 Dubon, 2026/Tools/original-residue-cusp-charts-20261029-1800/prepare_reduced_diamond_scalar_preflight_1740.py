from pathlib import Path
import json,re
s=Path(__file__).parent
versions={'SourceReducedFieldScalarGeneration':'1721f','SourceReducedFieldTensorEmbedding':'1725c','SourceReducedFieldTensorFraction':'1727c','SourceReducedFieldAutomorphismExtension':'1730d','SourceReducedFieldAutomorphismExtensionLaws':'1732b','SourceIntegralDiamondScalarAction':'1733b','SourceIntegralDiamondScalarBaseFixed':'1734c','SourceIntegralDiamondScalarFixedDegree':'1735b'}
mods=[m+v for m,v in versions.items()];ths=[];defs=[]
for m in mods:
 f=s/(m+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0
 text=f.read_text(encoding='utf-8');ns=re.search(r'^namespace (\S+)',text,re.M)[1]
 ths += [ns+'.'+n for n in re.findall(r'^theorem (\w+)',text,re.M)]
 defs += [ns+'.'+n for n in re.findall(r'^(?:def|abbrev) (\w+)',text,re.M)]
assert (len(mods),len(ths),len(defs))==(8,19,7)
prior=json.loads((s/'source-reduced-diamond-kernel-1-audit-config.json').read_text(encoding='utf-8'))
base='Dubon2026.SourceFunctionField.';di=base+'IntegralDiamond.'
roots=[di+n for n in ['reducedFieldActionOver_coeff','reducedFieldActionOver_kernel','reducedFieldActionOver_fixes_fullBase','reduced_over_fixedField_degree_eq_signed_relativeIndex']]
edges=ths+defs+[x for x in prior['proofEdges'] if x not in [di+'reducedFieldAction_range_finite',di+'reduced_fixedField_degree_eq_signed_relativeIndex']]+[base+'ReducedDegreeTransport.coeffMap_intSeries',base+'ReducedDegreeTransport.coeffMap_mem_originalField',base+'linearIndependent_coeffMap_algebraMap','IsFractionRing.algEquivOfAlgEquiv','IsFractionRing.of_field','Module.Basis.baseChange']
edges=list(dict.fromkeys(edges))
cfg=dict(modules=mods,theorems=ths,constructions=defs,roots=roots,proofEdges=edges,localModules=mods+['SourceReducedFieldCoefficientMap1710b']+prior['localModules'])
arr=lambda xs:'#['+', '.join(chr(96)+x for x in xs)+']'
def write(n,t):
 f=s/n;assert not f.exists(),f;f.write_text(t,encoding='utf-8')
write('reduced-diamond-scalar-versions-1740.json',json.dumps(versions,indent=2)+'\n')
write('reduced-diamond-scalar-preflight-config-1740.json',json.dumps(cfg,indent=2)+'\n')
for a,b in [('SourceGammaOneGenusUpperPreflight1720','SourceReducedDiamondScalarPreflight1740'),('SourceGammaOneGenusUpperValuePreflight1720','SourceReducedDiamondScalarValuePreflight1740')]:
 c=(s/(a+'.lean')).read_text(encoding='utf-8')
 c='\n'.join('import '+m for m in mods)+'\nimport Mathlib.Tactic\n'+c[c.index('\nopen Lean'):]
 if 'Value' not in a:
  c=re.sub(r'(#print axioms [^\n]+\n)+',''.join('#print axioms '+x+'\n' for x in ths+defs),c,count=1)
  for k,v in [('modules',mods),('theorems',ths),('constructions',defs)]:c=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),c)
  c=re.sub(r'#lint in [^\n]+\n','',c).rstrip()+'\n\n'+''.join('#lint in '+m+'\n' for m in mods)
 else:
  for k,v in [('roots',roots),('localModules',cfg['localModules']),('required',edges)]:c=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),c)
  start=c.index(' occur in the ');end=c.index('; DUB17--20 OPEN.',start)
  c=c[:start]+' occur in the declaration-value closures of the actual scalar-extended diamond action, exact signed kernel, full-base fixation and Artin degree. Coefficient independence and actual tensor fractions supply the extension; no action, kernel or fixed-field degree is assumed. Fixed-field identification, fiber bounds, reverse genus, all-weight association, automorphy and higher continuation remain open'+c[end:]
 c=c.replace('GAMMA ONE GENUS UPPER PREFLIGHT','REDUCED DIAMOND SCALAR PREFLIGHT');write(b+'.lean',c)
 c=(s/('audit_'+a+'_1720.ps1')).read_text(encoding='utf-8').replace(a,b)
 write('audit_'+b+'_1740.ps1',c)
c=(s/'audit_gamma_one_genus_upper_preflight_1720.ps1').read_text(encoding='utf-8').replace('1720','1740').replace('GammaOneGenusUpper','ReducedDiamondScalar')
write('audit_reduced_diamond_scalar_preflight_1740.ps1',c)
print(json.dumps(dict(modules=len(mods),theorems=len(ths),constructions=len(defs),edges=len(edges))))
