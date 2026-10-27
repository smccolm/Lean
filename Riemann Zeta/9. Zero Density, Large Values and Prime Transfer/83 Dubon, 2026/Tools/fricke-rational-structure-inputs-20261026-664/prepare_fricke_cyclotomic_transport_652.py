from pathlib import Path
import re,json
p=Path(r'E:\Lean\.tmp\dubon83')
s=(p/'fricke-torsion-expansion-reuse-648/P2M/Sol/S_ModularForm_weierstrassP_torsion_qExpansion_package.lean.txt').read_text(encoding='utf-8')
def take(a,b):return s[s.index(a):s.index(b,s.index(a))]
h='''/-! DUB-17/18 -> original all-weight association -> finite Gamma1
character realization -> Picard/H1 and diamond comparison -> differential
realization -> rational Fourier structure -> cyclotomic conjugation.
The actual finite Fourier coefficient model is transported by the given
cyclotomic embedding. No preservation of analytic modularity is assumed.
Adapted from anthropics/fermats-last-theorem at
6e837e75355538c7f80bab5b956861e86c4eacc2 (Apache License 2.0). -/
namespace Dubon2026.SourceFricke
noncomputable section
open Complex Real PeriodPair
open UpperHalfPlane hiding I
open scoped UpperHalfPlane Manifold MatrixGroups ModularForm

'''
tail='\nend\nend Dubon2026.SourceFricke\n'
coeff=take('lemma isPrimitiveRoot_zetaN','theorem wpQCoeff_eq_iff_neg')+take('def zetaK','lemma ringHom_wpMonCoeffK')
coeff=coeff.replace('@[scoped simp]','@[simp]')
for n,d in {'zetaK':'The actual generating root of unity viewed in its cyclotomic field.','wpMonCoeffK':'The explicit monomial coefficient as an element of its actual coefficient field.','wpQCoeffK':'The actual finite exponent-fiber Fourier coefficient in the cyclotomic field.'}.items():
 coeff=re.sub(r'(?m)^(def '+n+r'\b)',lambda m:'/-- '+d+' -/\n'+m[1],coeff)
trans=take('lemma ringHom_wpMonCoeffK','end B4_qexp')
for n,im,t in [('SourceFrickeCyclotomicCoefficients','import SourceWeierstrassTorsionFourierExpansion\n\n',coeff),('SourceFrickeCyclotomicTransport','import SourceFrickeCyclotomicCoefficients\n\n',trans)]:
 f=p/(n+'.lean');assert not f.exists();f.write_text(im+h+t+tail,encoding='utf-8')
f=p/'fricke-cyclotomic-transport-route-652.json';assert not f.exists()
f.write_text(json.dumps(dict(chain='DUB-17/18 -> higher continuation -> arithmetic automorphy -> original all-weight association -> original finite Gamma1 characters -> Picard/H1 and diamond comparison -> differential realization -> rational Fourier basis -> cyclotomic conjugation of Fricke generators.',selectedRoute='Use the already proved finite Fourier coefficient model. Native ring-hom preservation of powers, inverses and finite sums transports coefficients directly; avoid an assumed analytic coefficient-conjugation operation. The actual analytic q-expansion is then identified using scope651.',assumptionsToDischarge='A coefficient embedding taking the level root to its s-th power sends the actual normalized torsion Weierstrass q-expansion to that at the transformed second torsion coordinate, for s coprime to the level.',remaining='The corresponding Fricke product coefficients, separation and rational spanning remain before actual cusp differential realization and the arithmetic comparison; 16/20; DUB-17--20 OPEN.',source='fricke-torsion-expansion-reuse-648/snapshots.json',rootPinsChanged=False,proofLimitsChanged=False,externalImport=False),indent=2)+'\n',encoding='utf-8')
print('Prepared exact cyclotomic coefficient transport.')
