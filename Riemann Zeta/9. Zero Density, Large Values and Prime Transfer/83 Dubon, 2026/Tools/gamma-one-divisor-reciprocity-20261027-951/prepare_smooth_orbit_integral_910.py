from pathlib import Path
import json,hashlib
p=Path(r'E:\Lean\.tmp\dubon83')
src=p/'anthropic-flt-residual-closure-20261020/P2M/Sol/S_ModularCurve_tendsto_integral_mul_smoothedFundamental_mul_finsum_translate.lean.txt'
t=src.read_text(encoding='utf-8')
def block(a,b):return t[t.index(a):t.index(b)]
def output(n,s):
 with (p/n).open('x',encoding='utf-8',newline='\n') as f:f.write(s)
header='''/-! DUB-17/18 -> original all-weight arithmetic association -> Gamma1 Picard/H1
-> Abel-Jacobi converse -> analytic reciprocity -> smooth divisor integral.
Adapted from pinned Apache-2.0 anthropics/fermats-last-theorem source.
Reuse the proved action geometry and compact-support continuity. The finite
orbit sum is unfolded by native change of variables. Compact support permits
eventual exact equality instead of a separate dominated-convergence argument.
No integral identity, comparison function or period identity is assumed. -/
namespace Dubon2026.SourceSmoothOrbitIntegral
noncomputable section
open UpperHalfPlane hiding I
open MeasureTheory Filter Complex Set Metric SourceSmoothDivisor
open scoped MatrixGroups Topology Real ComplexConjugate
local notation "UHP" => UpperHalfPlane.upperHalfPlaneSet

'''
geom=block('theorem sm_image','theorem continuousAt_ofComplex')
geom+=block('theorem continuousAt_ofComplex','theorem hasFDerivAt_sm')
geom+=block('theorem hasFDerivAt_sm','theorem finite_moving')
geom=geom.replace('hasFDerivAt_sm','hasFDerivAt_sm_matrix')
geom+=block('theorem eq_zero_of_notMem','section CoV')
geom=geom.replace(chr(0x1d54c),'UHP')
geom=geom.replace('isOpen_U','UpperHalfPlane.isOpen_upperHalfPlaneSet')
output('SourceSmoothOrbitIntegralGeometry.lean','import SourceSmoothModularGeometry\nimport SourceComplexHolomorphicStokes\n\n'+header+geom+'\nend\nend Dubon2026.SourceSmoothOrbitIntegral\n')
cov=block('section CoV','theorem main')
cov=cov.replace(chr(0x1d54c),'UHP').replace('isOpen_U','UpperHalfPlane.isOpen_upperHalfPlaneSet')
cov=cov.replace('hasFDerivAt_sm','hasFDerivAt_sm_matrix')
cov=cov.replace('continuous_mul_of_tsupport_subset','SourceComplexReciprocity.continuous_mul_of_tsupport_subset UpperHalfPlane.isOpen_upperHalfPlaneSet')
cov=cov.replace('include hF hFU hg hgw hh hhU in','include hFU hgw hhU in')
output('SourceSmoothOrbitIntegralChangeVariables.lean','import SourceSmoothOrbitIntegralGeometry\n\n'+header+cov+'\nend\nend Dubon2026.SourceSmoothOrbitIntegral\n')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
route=dict(chain='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> all-weight arithmetic association -> original Gamma1 Picard/H1 -> Abel-Jacobi converse -> analytic reciprocity -> integral of the constructed smooth comparison V',source=dict(path=str(src),sha256=sha(src),fullMathematicalSourceRead=True),reuseChecked=[dict(path=str(p/n),sha256=sha(p/n)) for n in ['SourceSmoothModularGeometry.lean','SourceComplexHolomorphicStokes.lean','SourceModularSmoothedFundamental.lean','SourceModularInvariantIntegralUnfolding.lean','SourceModularSmoothPlaneIntegral.lean']],shorterRoute='The invariant-integrand unfolding theorem needs a fundamental-domain integrability premise that is not yet known for the translated compact coefficients. Use native planar change of variables and finite compact overlap directly. On tsupport F, compactness bounds max(im, inverse im), so the proved orbit partition equals one uniformly for all sufficiently large cutoffs. This gives eventual exact equality and the required limit without a dominated-convergence layer.',assumptionsToDischarge=['Integrability of the actual weighted translate sum','Exact finite unfolding','Uniform eventual partition equality on actual compact support','Required integral limit for each constructed dipole coefficient'],remaining='Assemble with original divisor V and period primitive; then filled quotient/winding reciprocity, principal-divisor converse and full arithmetic chain. 16/20; DUB-17--20 OPEN.')
output('smooth-orbit-integral-shorter-route-910.json',json.dumps(route,indent=2)+'\n')
print('Prepared two change-of-variable modules; full primary source read and shorter route recorded.')
