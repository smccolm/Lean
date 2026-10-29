from pathlib import Path
import json,re
s=Path(__file__).parent
versions={
 'SourceIntegralDiamondFullBaseInclusion':'1692d',
 'SourceIntegralDiamondGammaZeroFixed':'1695a',
 'SourceIntegralDiamondEisensteinAction':'1696b',
 'SourceIntegralDiamondSignedMembership':'1697a',
 'SourceIntegralDiamondExactKernel':'1698a',
 'SourceIntegralDiamondFixedFieldDegree':'1699b'}
mods=[m+v for m,v in versions.items()];ths=[]
for m in mods:
 f=s/(m+'.lean');assert f.with_suffix('.exit').read_text().strip()=='0' and f.with_suffix('.log').stat().st_size==0,m
 c=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',f.read_text(encoding='utf-8'),flags=re.S))
 ns=re.search(r'^namespace (\S+)',c,re.M)[1]+'.'
 ths += [ns+x for x in re.findall(r'^(?:theorem|lemma)\s+([\w.\x27]+)',c,re.M)]
ns='Dubon2026.SourceFunctionField.IntegralDiamond.'
roots=[ns+n for n in ['reduced_fixedField_degree_eq_signed_relativeIndex','reducedFieldAction_kernel',
 'reducedFieldAction_fixes_fullBase','fullBase_le_originalReducedField']]
prior=json.loads((s/'reduced-diamond-action-preflight-config-1694.json').read_text(encoding='utf-8'))
edges=ths+[ns+n for n in ['reducedFieldAction','reducedFieldEquiv','reducedFieldPull','reducedFieldPull_eq',
 'reducedDiamond_eq','reducedDiamond_of_invariant','reducedFieldAction_eq_one_of_signed_gammaOne']]
edges += ['Dubon2026.SourceFunctionField.IntegralEisenstein.'+n for n in [
 'ratio_separates_signed_identity','ratio_mem_original_field','normalizedForm_integral']]
edges += ['Dubon2026.SourceFunctionField.GammaOne.exists_even_integral_ratio',
 'Dubon2026.SourceFunctionField.GammaOne.jqModC_mem_integralRatioField',
 'FixedPoints.finrank_eq_card','Subgroup.index_ker']
cfg=dict(modules=mods,theorems=ths,constructions=[],roots=roots,proofEdges=edges,localModules=mods+prior['localModules'])
arr=lambda xs:'#['+', '.join(chr(96)+x for x in xs)+']'
def write(n,t):
 f=s/n;assert not f.exists(),f;f.write_text(t,encoding='utf-8')
write('reduced-diamond-kernel-versions-1701.json',json.dumps(versions,indent=2)+'\n')
write('reduced-diamond-kernel-preflight-config-1701.json',json.dumps(cfg,indent=2)+'\n')
for a,b in [('SourceReducedDiamondActionPreflight1694','SourceReducedDiamondKernelPreflight1701'),('SourceReducedDiamondActionValuePreflight1694','SourceReducedDiamondKernelValuePreflight1701')]:
 c=(s/(a+'.lean')).read_text(encoding='utf-8')
 c='\n'.join('import '+m for m in mods)+'\nimport Mathlib.Tactic\n'+c[c.index('\nopen Lean'):]
 if 'Value' not in a:
  c=re.sub(r'(#print axioms [^\n]+\n)+',''.join('#print axioms '+x+'\n' for x in ths),c,count=1)
  for k,v in [('modules',mods),('theorems',ths),('constructions',[])]:c=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),c)
  c=re.sub(r'#lint in [^\n]+\n','',c).rstrip()+'\n\n'+''.join('#lint in '+m+'\n' for m in mods)
 else:
  for k,v in [('roots',roots),('localModules',cfg['localModules']),('required',edges)]:c=re.sub(r'let '+k+r' : Array Name := #\[[^\n]*\]','let '+k+' : Array Name := '+arr(v),c)
  start=c.index(' occur in the ');end=c.index('; DUB17--20 OPEN.',start)
  c=c[:start]+' occur in the proof value closure of actual full-base inclusion and fixation, exact signed kernel and Artin fixed-field degree. The full-base degree comparison, total signed-index bound, original degree/genus and higher continuation remain open'+c[end:]
 c=c.replace('REDUCED DIAMOND ACTION PREFLIGHT','REDUCED DIAMOND KERNEL PREFLIGHT')
 write(b+'.lean',c)
 c=(s/('audit_'+a+'_1694.ps1')).read_text(encoding='utf-8').replace(a,b)
 write('audit_'+b+'_1701.ps1',c)
c=(s/'audit_reduced_diamond_action_preflight_1694.ps1').read_text(encoding='utf-8').replace('1694','1701').replace('ReducedDiamondAction','ReducedDiamondKernel')
write('audit_reduced_diamond_kernel_preflight_1701.ps1',c)
print(json.dumps(dict(modules=len(mods),theorems=len(ths),edges=len(edges))))
