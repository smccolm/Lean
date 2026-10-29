from pathlib import Path
import json,re
d=Path('E:/Lean/.tmp/dubon83');p=Path('E:/Lean/Riemann Zeta/9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026')
specs=[('MatrixPolynomialAction','matrixPolynomialAction_mul','g h',True),('UniversalMatrixPolynomial','matrixCoefficientPolynomial_eval','p d a',True),('HomogeneousMonomialBasis','homogeneousMonomial_span','n',True),('HomogeneousCoefficientChange','homogeneousCoefficientMap_GL','n φ g p',True),('HomogeneousSymmetricMatrix','homogeneousSymmetricGL_val','n g',True),('HomogeneousSymmetricBaseChange','homogeneousSymmetricGL_map','n φ g',True),('HomogeneousSymmetricContinuity','homogeneousSymmetricGL_continuous','n',True),('SymmetricRepresentationReduction','symmetricMatrixRepresentation_map','n ρ φ',True)]
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
 sig=source[a:b].replace('theorem '+name,'theorem actual_arithmetic_symmetric_'+name+'_source',1)
 out+='section\n\nopen IsDedekindDomain Matrix MvPolynomial Module\n\n'
 if vars:
  a=source.index('variable ');b=source.index('/--',a);out+=re.sub(r"^omit .+ in\n", "", source[a:b], flags=re.M)
 out+=f'/-- Exact original-object consumer of `{name}`. -/\n'+sig+':=\n  '+name+' '+args+'\n\nend\n\n'
(d/'consumers1380.txt').write_text(out,encoding='utf8')
(d/'modules1380.json').write_text(json.dumps(list(dict.fromkeys(x[0] for x in specs if x[0] not in ['MatrixPolynomialAction','UniversalMatrixPolynomial','HomogeneousMonomialBasis'])),indent=2)+'\n',encoding='utf8')
print('Prepared eight exact consumers of the original symmetric action over arithmetic coefficient rings.')
