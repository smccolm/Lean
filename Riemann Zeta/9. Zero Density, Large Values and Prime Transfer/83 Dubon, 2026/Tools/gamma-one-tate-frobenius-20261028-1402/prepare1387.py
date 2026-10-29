from pathlib import Path
import json,re
d=Path('E:/Lean/.tmp/dubon83');p=Path('E:/Lean/Riemann Zeta/9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026')
specs=[('GroupAlgebraMatrix', 'groupAlgebraMatrix_map', 'ρ φ x', True), ('MatrixRepresentationDeterminant', 'matrixRepresentationDeterminant_map', 'ρ φ x', True), ('DeterminantCoefficientLaw', 'determinantCoefficientLaw_natural', 'ρ φ ψ x', True), ('GroupAlgebraScalarExtension', 'groupAlgebraScalarExtensionEquiv_tmul', 'a x', True), ('SymmetricDeterminantLaw', 'symmetricMatrixRepresentation_determinant_baseChange', 'n ρ φ x', True), ('MatrixTensorDeterminant', 'matrixTensorDeterminant_natural', 'ρ ψ x', True), ('DeterminantCharacteristicPolynomial', 'determinantCharacteristicPolynomial_annihilates', 'ρ g', True)]
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
 sig=source[a:b].replace('theorem '+name,'theorem actual_matrix_determinant_'+name+'_source',1)
 out+='section\n\nopen IsDedekindDomain Matrix Module\nopen scoped TensorProduct\n\n'
 if vars:
  a=source.index('variable ');b=source.index('/--',a);out+=re.sub(r"^omit .+ in\n", "", source[a:b], flags=re.M)
 out+=f'/-- Exact original-object consumer of `{name}`. -/\n'+sig+':=\n  '+name+' '+args+'\n\nend\n\n'
(d/'consumers1387.txt').write_text(out,encoding='utf8')
(d/'modules1387.json').write_text(json.dumps(list(dict.fromkeys(x[0] for x in specs)),indent=2)+'\n',encoding='utf8')
print('Prepared seven exact consumers of the original representation determinant family.')
