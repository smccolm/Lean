from pathlib import Path
from datetime import datetime,timezone
import json,hashlib
s=Path(__file__).parent
p=Path(r'E:\Lean\Riemann Zeta\9. Zero Density, Large Values and Prime Transfer\83 Dubon, 2026\Extension\Dubon2026')
source=s/'anthropic-peaked-core-1533/S_ModularCurve_SiegelUnit_exists_modularForm_gamma1_coe_eq_prod_siegelFun_pow_mul_discriminant_pow.lean.txt'
inputs=[source,s/'SourceSiegelHolomorphic.lean',s/'SourceSiegelProductTransformation.lean',s/'SourceSiegelFiniteProductExpansion1601b.lean',p/'SourceHolomorphicDiscriminantLift.lean',p/'SourceDiscriminantIntegralExpansion.lean',p/'SourceQExpansionPeriodWidth.lean']
r=dict(recordedUTC=datetime.now(timezone.utc).isoformat(),chain='DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> literal higher continuation -> automorphy -> original all-weight characteristic-zero association -> original Gamma1 degree/genus preservation -> reduced field action -> level-power slash integrality -> actual peaked auxiliary -> discriminant-adjusted Siegel product as an actual modular form with exact cusp decay.',reuseChecked=[dict(path=str(f),sha256=hashlib.sha256(f.read_bytes()).hexdigest().upper()) for f in inputs],shorterRoute='Reuse the actual audited Siegel holomorphy and SL2/Gamma1 product transformations, the newly proved exact finite-product cusp limit, and native discriminant cusp-form decay. The existing holomorphic discriminant lift targets Gamma0 quotients and lacks these explicit Siegel Bernoulli orders; adapt only the finite row permutation, literal slash identity and cusp-bound assembly. Reuse existing integral discriminant expansion and width-change theorem in the subsequent q-expansion step instead of the external duplicate Eisenstein divisibility proof.',assumptionsToDischarge=['Actual discriminant-adjusted product is holomorphic and Gamma1 invariant.','Every transformed literal product has the exact Bernoulli cusp order from the original exponent family.','The source exponential bound holds at every SL2 cusp.','Nonnegative shifted cusp orders give an actual ModularForm rather than a boundedness certificate.'],remaining='Select the discriminant power, prove exact integral q-expansions and leading coefficient bounds, and assemble the actual even-weight peaked auxiliary. Degree/genus preservation and downstream original arithmetic association/continuation remain open. Acceptance remains 16/20; DUB-17--20 OPEN.',externalBuild=False,externalImport=False,proofLimitsChanged=False)
def write(n,t):
 f=s/n;assert not f.exists(),f;f.write_text(t,encoding='utf-8')
write('peaked-modular-form-route-review-1603.json',json.dumps(r,indent=2)+'\n')
c=source.read_text(encoding='utf-8')
start=c.index('noncomputable def uFun');end=c.index('\nend FORM',start)
body=c[start:end]
body=body.replace('ModularCurve.SiegelUnit.prod_siegelFun_pow_specialLinearGroup_smul','Siegel.prod_siegelFun_pow_specialLinearGroup_smul').replace('ModularCurve.SiegelUnit.exists_isIntegral_hasSum_prod_siegelFun_pow','FiniteExpansion.exists_integral_hasSum_prod_siegelFun_pow').replace('((ModularCurve.SiegelUnit.differentiableOn_siegelFun N (r.val : ℤ) (s.val : ℤ)).1)','(Siegel.differentiableOn_siegelFun N (r.val : ℤ) (s.val : ℤ))')
docs={
'noncomputable def uFun':'/-- The literal finite Siegel product of the exponent family. -/\nnoncomputable def uFun',
'def Ord':'/-- The exact integer Bernoulli order on a residue column. -/\ndef Ord',
'noncomputable def thetaFun':'/-- The actual Siegel product times the chosen discriminant power. -/\nnoncomputable def thetaFun',
'def e00':'/-- The reduced top-left matrix entry. -/\ndef e00',
'def e01':'/-- The reduced top-right matrix entry. -/\ndef e01',
'def e10':'/-- The reduced bottom-left matrix entry. -/\ndef e10',
'def e11':'/-- The reduced bottom-right matrix entry. -/\ndef e11',
'def rowMul':'/-- The actual permutation of residue rows induced by an SL2 matrix. -/\ndef rowMul',
'def mT':'/-- The exponent family transported by the inverse row permutation. -/\ndef mT',
'noncomputable def theta (':'/-- The discriminant-adjusted literal product as an actual modular form. -/\nnoncomputable def theta ('}
for a,b in docs.items():body=body.replace(a,b)
cuts=[0,body.index('/-- The reduced top-left'),body.index('theorem discr_isBigO'),body.index('theorem mdifferentiable_thetaFun'),body.index('/-- The discriminant-adjusted literal product'),len(body)]
names=['SourcePeakedAuxiliaryFunction1603a','SourceSiegelCuspPermutation1604a','SourcePeakedAuxiliaryCuspDecay1605a','SourcePeakedAuxiliaryHolomorphic1606a','SourcePeakedAuxiliaryModularForm1607a']
imports=['import SourceSiegelFiniteProductExpansion1601b\nimport SourceSiegelProductTransformation\nimport SourceSiegelHolomorphic\nimport Mathlib.NumberTheory.ModularForms.Discriminant',
'import '+names[0], 'import '+names[1], 'import '+names[0], 'import '+names[2]+'\nimport '+names[3]]
header='''

/-! DUB-17/18 -> original Gamma1 degree/genus preservation -> level-power
slash integrality -> actual peaked auxiliary -> discriminant-adjusted Siegel
modular form and its exact cusp bounds. Consume actual literal products,
the proved finite-product cusp limit and native discriminant decay. The
nonnegative shifted-order hypothesis is explicit and will be discharged
when selecting the discriminant power; no auxiliary existence is assumed.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_SiegelUnit_exists_modularForm_gamma1_coe_eq_prod_siegelFun_pow_mul_discriminant_pow. -/
namespace Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.Form
noncomputable section
open UpperHalfPlane
open scoped MatrixGroups ModularForm Manifold
variable (N : ℕ) [NeZero N] (m : ZMod N → ZMod N → ℕ)

'''
tail='\nend\nend Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.Form\n'
for i,n in enumerate(names):
 chunk=body[cuts[i]:cuts[i+1]]
 if i==4:
  final=c[c.index('theorem solution'):]
  final=final.replace('theorem solution','theorem exists_modularForm_gamma1_coe_eq_prod_siegelFun_pow_mul_discriminant_pow').replace('ModularCurve.siegelFun','siegelFun').replace('FORM.','')
  final=final.replace('fun τ => rfl, fun β => ?_','theta_apply N m hm0 hm t ht, fun β => ?_')
  chunk+='\n'+final
 write(n+'.lean',imports[i]+header+chunk+tail)
print('Prepared five literal modular-form/cusp modules; source and native reuse recorded.')
