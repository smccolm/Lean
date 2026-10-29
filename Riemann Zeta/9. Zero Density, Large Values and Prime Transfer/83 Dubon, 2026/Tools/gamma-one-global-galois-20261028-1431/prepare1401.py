from pathlib import Path
import json,re
d=Path('E:/Lean/.tmp/dubon83');p=Path('E:/Lean/Riemann Zeta/9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026')
specs=[('DualMatrixStrictUnits', 'dualMatrixInfinitesimal_strictConjugate', 'A X', True), ('FirstOrderStrictConjugation', 'matrixFirstOrderConjugate_coboundary', 'ρ τ X', True), ('FirstOrderCohomologyClassification', 'matrixFirstOrderStrictlyConjugate_iff', 'ρ τ σ', True), ('ContinuousFirstOrderDeformation', 'matrixFirstOrderLift_continuous_iff', 'ρ hρ τ', True)]
out='\n'
for mod,name,args,vars in specs:
 source=(p/f'Extension/Dubon2026/{mod}.lean').read_text(encoding='utf8')
 a=re.search(r'^theorem '+re.escape(name)+r'(?=[\s:{(\[])',source,re.M).start()
 depth=0;b=a
 while b < len(source):
  if depth==0 and source.startswith(':=',b):break
  if source[b] in '([{':depth+=1
  elif source[b] in ')]}':depth-=1
  b+=1
 assert b<len(source),name
 sig=source[a:b].replace('theorem '+name,'theorem actual_strict_deformation_'+name+'_source',1)
 out+='section\n\nopen IsDedekindDomain Matrix Module\nopen scoped TensorProduct\n\n'
 out+=''.join(line+'\n' for line in re.findall(r'^universe .+$',source,re.M))+'\n'
 if vars:
  a=re.search(r'^variable ',source,re.M).start();b=source.index('/--',a);out+=re.sub(r"^omit .+ in\n", "", source[a:b], flags=re.M)
 out+=f'/-- Exact original-object consumer of `{name}`. -/\n'+sig+':=\n  '+name+' '+args+'\n\nend\n\n'
(d/'consumers1401.txt').write_text(out,encoding='utf8')
(d/'modules1401.json').write_text(json.dumps(list(dict.fromkeys(x[0] for x in specs)),indent=2)+'\n',encoding='utf8')
print('Prepared four exact consumers of original strict conjugacy, cohomology and continuity.')
