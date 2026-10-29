from pathlib import Path
import json
d=Path('E:/Lean/.tmp/dubon83')
p=Path('E:/Lean/Riemann Zeta/9. Zero Density, Large Values and Prime Transfer/83 Dubon, 2026')
specs=[
 ('SmoothInducedContinuity','smoothInducedCharacter_continuous','B χ f','first',''),
 ('SmoothInducedCompactAverage','smoothInducedCompactAverage_fixed','B K χ μ f hf','first',''),
 ('FinitePlaceInducedAverage','finitePlaceInducedAverage_spherical','v z₁ z₂','',''),
 ('RepresentationSphericalFunctional','sphericalFunctional_scalar_double_coset','ρ K ℓ hℓ y hy c a hc l r','include','hℓ hy'),
 ('FinitePlaceFunctionalRadial','finitePlaceFunctionalRadial_forward','p ρ ℓ y hℓ hy n i hi','radial','hℓ hy'),
 ('FinitePlaceFunctionalHecke','finitePlaceFunctionalHecke_eigen_recurrence','p ρ ℓ y hℓ hy hc μ heigen','include','hℓ hy hc'),
 ('FinitePlaceFunctionalSpherical','finitePlaceFunctional_unitary_unique','p ρ ℓ y hℓ hy hc hn z heigen σ hσ hσc w hw hwK hwT g','include','hℓ hy hc hn heigen'),
 ('SphericalCoefficientRelations','sphericalCoefficient_linearCombination_ker_le','ρ σ hρ v w ℓ hcoeff','include','hρ hcoeff'),
 ('PrimitiveInducedSphericalCoefficient','primitiveLocalInduced_smooth_coefficient','F hpN g','',''),
]
out='\n'
for mod,name,args,kind,inc in specs:
 source=(p/f'Extension/Dubon2026/{mod}.lean').read_text(encoding='utf8')
 start=source.index('theorem '+name)
 end=source.index(':=',start)
 signature=source[start:end].replace('theorem '+name,'theorem actual_induced_coefficient_'+name+'_source',1)
 out+='section\n\nopen IsDedekindDomain Matrix MeasureTheory\n\n'
 if kind:
  a=source.index('variable ')
  b=source.index('/--',a) if kind=='first' else source.index('include ',a)
  if kind=='radial':
   out+=source[a:source.index('/--',a)]
   a=source.index('\nvariable',a+1)+1
  out+=source[a:b]
 if inc:out+='include '+inc+'\n\n'
 out+=f'/-- Exact source consumer of `{name}`. -/\n'+signature+':=\n  '+name+' '+args+'\n\nend\n\n'
(d/'consumers1367.txt').write_text(out,encoding='utf8')
(d/'modules1367.json').write_text(json.dumps([x[0] for x in specs],indent=2)+'\n',encoding='utf8')
print('Prepared nine exact consumers for actual compact spherical coefficients and their relation map.')
