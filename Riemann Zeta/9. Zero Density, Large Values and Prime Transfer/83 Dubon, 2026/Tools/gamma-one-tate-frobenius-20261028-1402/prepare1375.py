from pathlib import Path
import json
d=Path('E:/Lean/.tmp/dubon83');p=Path('E:/Lean/Riemann Zeta/9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026')
specs=[('RepresentationOrbitRange','representation_orbit_linearCombination','ρ v g a',True),('SphericalCoefficientQuotient','sphericalCoefficientIntertwiner_surjective','ρ σ hρ v w ℓ hcoeff hspan',True),('IntertwiningQuotientEquiv','intertwiningQuotientEquiv_intertwines','ρ σ T hs g x',True),('PrimitiveInducedCyclicQuotient','primitiveLocalInduced_spherical_constituent','F hpN',False),('HomogeneousDiagonalAction','homogeneousMatrixAction_diagonal_monomial','a n d hd',False),('HomogeneousMonomialBasis','homogeneousMonomial_span','n',False),('HomogeneousSatakeEuler','homogeneousUnitDiagonal_euler','a b n',False),('PrimitiveSymmetricDualEuler','primitiveLocalInduced_actual_symmetric_factor','F hpN r s',False),('PrimitiveSymmetricDualEuler','primitiveSymmetricMatrix_hasProd_far','F hk r hs',False)]
out='\n'
for mod,name,args,vars in specs:
 source=(p/f'Extension/Dubon2026/{mod}.lean').read_text(encoding='utf8')
 a=source.index('theorem '+name);b=source.index(':=',a)
 sig=source[a:b].replace('theorem '+name,'theorem actual_induced_quotient_'+name+'_source',1)
 out+='section\n\nopen IsDedekindDomain Matrix\n\n'
 if vars:
  a=source.index('variable ');b=source.index('/--',a);out+=source[a:b]
 out+=f'/-- Exact original-object consumer of `{name}`. -/\n'+sig+':=\n  '+name+' '+args+'\n\nend\n\n'
(d/'consumers1375.txt').write_text(out,encoding='utf8')
(d/'modules1375.json').write_text(json.dumps(list(dict.fromkeys(x[0] for x in specs)),indent=2)+'\n',encoding='utf8')
print('Prepared nine exact consumers of the actual induced subquotient and symmetric dual Euler factors.')
