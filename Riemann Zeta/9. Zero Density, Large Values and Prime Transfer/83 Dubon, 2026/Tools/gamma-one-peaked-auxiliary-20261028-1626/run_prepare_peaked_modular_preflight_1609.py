from pathlib import Path
import re,json
s=Path(__file__).parent
versions={
'SourcePeakedAuxiliaryFunction':'1603a','SourceSiegelCuspPermutation':'1604a',
'SourcePeakedAuxiliaryCuspDecay':'1605a','SourcePeakedAuxiliaryHolomorphic':'1606a',
'SourcePeakedAuxiliaryModularForm':'1607a'}
mods=[m+v for m,v in versions.items()];ths=[];defs=[]
for m in mods:
 f=s/(m+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 c=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',f.read_text(encoding='utf-8'),flags=re.S));ns=re.search(r'^namespace (\S+)',c,re.M)[1]+'.'
 ths += [ns+x for x in re.findall(r'^(?:theorem|lemma)\s+([\w.\x27]+)',c,re.M)]
 defs += [ns+x for x in re.findall(r'^(?:noncomputable )?def\s+([\w.\x27]+)',c,re.M)]
assert len(set(ths+defs))==len(ths+defs)
ns='Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.Form.'
roots=[ns+'exists_modularForm_gamma1_coe_eq_prod_siegelFun_pow_mul_discriminant_pow']
edges=ths+defs+[
'Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.Siegel.prod_siegelFun_pow_specialLinearGroup_smul',
'Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.Siegel.differentiableOn_siegelFun',
'Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.FiniteExpansion.exists_integral_hasSum_prod_siegelFun_pow',
'CuspFormClass.exp_decay_atImInfty',
'SlashInvariantForm.slash_action_generators_SL2Z']
cfg=dict(modules=mods,theorems=ths,constructions=defs,roots=roots,proofEdges=edges)
arr=lambda xs:'#['+', '.join(chr(96)+x for x in xs)+']'
def write(n,t):
 f=s/n;assert not f.exists();f.write_text(t,encoding='utf-8')
write('peaked-modular-form-versions-1609.json',json.dumps(versions,indent=2)+'\n')
write('peaked-modular-form-preflight-config-1609.json',json.dumps(cfg,indent=2)+'\n')
for a,b in [('SourceIntegralTraceAudit1','SourcePeakedModularFormPreflight1609'),('SourceIntegralTraceDependencyAudit1','SourcePeakedModularFormValuePreflight1609')]:
 c=(s/(a+'.lean')).read_text(encoding='utf-8')
 c='\n'.join('import '+m for m in mods)+'\nimport Mathlib.Tactic\n'+c[c.index('\nopen Lean'):]
 if a=='SourceIntegralTraceAudit1':
  c=re.sub(r'(#print axioms [^\n]+\n)+',''.join('#print axioms '+x+'\n' for x in ths+defs),c,count=1)
  for k,v in [('modules',mods),('theorems',ths),('constructions',defs)]:c=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),c)
  c=re.sub(r'#lint in [^\n]+\n','',c).rstrip()+'\n\n'+''.join('#lint in '+m+'\n' for m in mods)
 else:
  for k,v in [('roots',roots),('localModules',mods),('required',edges)]:c=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),c)
  start=c.index(' occur in the ');end=c.index('; DUB17--20 OPEN.',start)
  c=c[:start]+' occur in the proof value closure of the actual discriminant-adjusted Gamma1 modular form and its exact exponential bound at every SL2 cusp, under explicit nonnegative shifted-order hypotheses. Selection of the discriminant power, exact auxiliary q-expansions and peaked auxiliary existence remain open'+c[end:]
 c=c.replace('INTEGRAL TRACE','PEAKED MODULAR FORM PREFLIGHT').replace('Frobenius Normalization','Siegel expansion')
 write(b+'.lean',c)
 c=(s/'audit_peaked_exponent_preflight_1552.ps1').read_text(encoding='utf-8').replace('SourcePeakedExponentPreflight1552',b)
 write('audit_'+b+'_1609.ps1',c)
print(json.dumps(dict(modules=len(mods),theorems=len(ths),constructions=len(defs),edges=len(edges))))
