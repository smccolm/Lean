from pathlib import Path
import json,hashlib,re
p=Path(r'E:\Lean\.tmp\dubon83')
src=p/'anthropic-flt-residual-closure-20261020/P2M/Sol/S_ModularCurve_exists_exp_eq_of_invariant_ne_zero_isParabolicHom.lean.txt'
s=src.read_text(encoding='utf-8-sig')
def output(n,t):
 with (p/n).open('x',encoding='utf-8',newline='\n') as f:f.write(t)
head="""/-! Adapted from anthropics/fermats-last-theorem (Apache-2.0), pinned
S_ModularCurve_exists_exp_eq_of_invariant_ne_zero_isParabolicHom.
DUB-17/18 -> original all-weight arithmetic association -> actual Gamma1
Picard/H1 -> Abel-Jacobi converse -> analytic reciprocity -> winding-period
comparison -> logarithm of the nonvanishing invariant quotient.
Native exponential covering and lift uniqueness are reused. All smoothness,
derivatives, integer character and cusp conditions are proved from the actual
function; no logarithm or parabolic-character certificate is assumed. -/
namespace Dubon2026.SourceWindingLog
noncomputable section
open UpperHalfPlane hiding I
open Filter Complex Set Topology
open scoped MatrixGroups Topology Real

"""
b=s[s.index('theorem eq_zero_of_exp_eq_one_of_norm_lt'):s.index('section Global')]
b=b.replace('    have : |(k : ℝ)| = |((k : ℤ) : ℝ)| := rfl\n','')
a=b.index('  have hlc : IsLocallyConstant D')
e=b.index('\nsection Lift',a)
b=b[:a]+"""  exact Complex.isCoveringMap_exp.const_of_comp hD (fun a b => by
    apply Subtype.ext
    exact (h1 a).trans (h1 b).symm) x y

"""+b[e:]
b=b.replace('def toUnits','/-- The actual nonvanishing function as a continuous map to punctured C. -/\ndef toUnits')
output('SourceComplexWindingLogLift.lean','import Mathlib\n\n'+head+b+'end\nend Dubon2026.SourceWindingLog\n')
b=s[s.index('section Global'):s.index('theorem isEquivariantPrimitive')]
for n,d in [('Lext','Extend the continuous upper-half-plane lift through the standard retraction.'),('mInt','The uniquely determined integer exponential period of the actual lift.'),('mHom','The integral additive character defined by the actual logarithmic shifts.')]:
 b=b.replace('def '+n+' ', '/-- '+d+' -/\ndef '+n+' ')
b=b.replace("theorem two_pi_I_ne_zero'","theorem two_pi_I_ne_zero")
b=b.replace("two_pi_I_ne_zero'","two_pi_I_ne_zero")
output('SourceModularWindingCharacter.lean','import SourceComplexWindingLogLift\n\n'+head+b+'end Global\nend\nend Dubon2026.SourceWindingLog\n')
b=s[s.index('section Cusp'):s.index('theorem main')]
b=b.replace('def retract','/-- Continuous retraction to a closed horoball above a positive height. -/\ndef retract')
output('SourceModularWindingCuspLimit.lean','import SourceModularWindingCharacter\n\n'+head+b+'end\nend Dubon2026.SourceWindingLog\n')
route=dict(chain=['DUB-17/18','original all-weight arithmetic association','actual Gamma1 Picard/H1','Abel-Jacobi converse','analytic reciprocity','winding-period comparison','logarithm of actual nonvanishing invariant quotient'],primary=dict(path=str(src),sha256=hashlib.sha256(src.read_bytes()).hexdigest().upper(),read='Entire source including cusp and final theorem read.'),reuse='Native Complex.isCoveringMap_exp.existsUnique_continuousMap_lifts constructs the lift. Native IsCoveringMap.const_of_comp replaces the source locally-constant proof. Existing SourceParabolic.classification will replace the external Period wrapper in the exact squared-trace-four conclusion. Existing SourceSimplyConnectedCovering has simply connected BASE and is not applicable to the punctured complex base.',scope='Actual C1 nonzero invariant function and nonzero finite translated cusp limits are input. Construct logarithm, its derivative, integer character, finite cusp limits and literal trace-four vanishing. This does not assume or prove realization of the original divisor.',remaining='Smooth comparison V, quotient assembly and winding-period integral remain before reciprocity, principal-divisor converse and full all-weight arithmetic association. 16/20; DUB-17--20 OPEN.')
output('winding-log-reuse-route-887.json',json.dumps(route,indent=2)+'\n')
