from pathlib import Path
import json,hashlib
p=Path(r'E:\Lean\.tmp\dubon83')
src=p/'gamma-one-smooth-local-model-reuse-886/S_ModularCurve_exists_invariant_localModel_tendsto_integral_dbarLogDeriv_smoothedFundamental_periodAlongOf.lean.txt'
t=src.read_text(encoding='utf-8')
body=t[t.index('theorem main'):t.index('\nend ModularCurve.DivisorTerm')]
body=body.replace('theorem main','theorem exists_comparison_period_limit')
body=body.replace('    (h : ℝ → ℂ → ℂ) (hh : ∀ T z, h T z = (ModularCurve.smoothedFundamental Γ T z : ℂ)) :','    :')
sig,proof=body.split(' := by\n',1)
sig=sig.replace('h T z','(smoothedFundamental Γ T z : ℂ)')
proof=proof.replace('  classical\n','  classical\n  let h : ℝ → ℂ → ℂ := fun T z => (smoothedFundamental Γ T z : ℂ)\n  have hh : ∀ T z, h T z = (smoothedFundamental Γ T z : ℂ) := fun _ _ => rfl\n',1)
body=sig+' := by\n'+proof
body=body.replace('ModularCurve.exists_invariant_localModel_dbarLogDeriv_eq_sum_finsum_translate_of_finiteIndex','exists_invariant_comparison')
body=body.replace('ModularCurve.tendsto_integral_mul_smoothedFundamental_mul_finsum_translate','SourceSmoothOrbitIntegral.compact_translate_limit')
body=body.replace('ModularCurve.contDiff_and_finsum_smoothedFundamental_eq_one','SourceSmoothedFundamental.smooth_partition')
body=body.replace('ModularCurve.periodAlongOf','sourceWeightTwoAlong')
body=body.replace('CuspForm Γ 2','CuspForm (Γ.map (mapGL ℝ)) 2')
body=body.replace('Eg Γ g','Ek g')
body=body.replace('hasDerivAt_Eg Γ g hz','Ek_hasDerivAt g hz')
body=body.replace(' h hh\n','\n')
body=body.replace('  rw [hm\' s hs, Eg_coe]','  rw [hm\' s hs]\n  simp only [Ek, ofComplex_apply]')
header='''import SourceSmoothCompactTranslateIntegral
import SourceSmoothInvariantComparison
import SourceWeightTwoPeriodUntwist

/-! DUB-17/18 -> original all-weight arithmetic association -> Gamma1 Picard/H1
-> Abel-Jacobi converse -> analytic reciprocity -> smooth divisor period limit.
Consume the constructed invariant comparison, actual compact coefficient
functions and exact local orders. The compact translate integral and existing
normalized endpoint primitive discharge the source period-limit obligation.
No primitive-existence, smoothed integral or reciprocity identity is assumed.
Adapted from pinned Apache-2.0 source 886; duplicate primitive and finite-
stabilizer foundations are replaced by existing proved declarations. -/
namespace Dubon2026.SourceSmoothDivisor
noncomputable section
open UpperHalfPlane hiding I
open MeasureTheory Filter Complex Set Matrix.SpecialLinearGroup SourcePeriodUntwist
open SourceSmoothedFundamental (smoothedFundamental)
open scoped MatrixGroups Topology Real ComplexConjugate ModularForm

theorem g_smul (Γ : Subgroup SL(2, ℤ))
    (g : CuspForm (Γ.map (mapGL ℝ)) 2) {γ : SL(2, ℤ)} (hγ : γ ∈ Γ) (τ : ℍ) :
    g (γ • τ) = denom (γ : GL (Fin 2) ℝ) τ ^ 2 * g τ := by
  simpa using SlashInvariantForm.slash_action_eqn_SL'' (Γ := Γ) g hγ τ

'''
out=header+body+'\n\nend\nend Dubon2026.SourceSmoothDivisor\n'
with (p/'SourceSmoothDivisorPeriodIntegral.lean').open('x',encoding='utf-8',newline='\n') as f:f.write(out)
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest().upper()
r=dict(chain='DUB-17/18 -> full all-weight arithmetic association -> original Gamma1 Picard/H1 -> Abel-Jacobi converse -> analytic reciprocity -> smooth divisor period limit',source=dict(path=str(src),sha256=sha(src),fullSourceRead=True),reused=[dict(path=str(p/n),sha256=sha(p/n)) for n in ['SourceSmoothInvariantComparison.lean','SourceWeightTwoPeriodUntwist.lean','SourceSmoothDivisorOrbitData.lean','smooth-orbit-integral-shorter-route-910.json']],assumptionsToDischarge=['Construct V rather than assume its existence','Integrability of its actual logarithmic derivative against the canonical smooth cutoff','Exact stabilizer-normalized limit expressed in the existing endpoint periods','Degree-zero cancellation removes the auxiliary base point'],shorterRoute='Reuse Ek and Ek_hasDerivAt, actual finite stabilizers and constructed compact dipoles. The compact translate theorem uses eventual exact equality. No copied affine-path, primitive-existence or finite-stabilizer boilerplate.',remaining='Actual original-divisor specialization, filled quotient and winding/Petersson reciprocity, principal-divisor converse and original all-weight arithmetic chain; 16/20; DUB-17--20 OPEN.')
with (p/'smooth-divisor-period-route-912.json').open('x',encoding='utf-8') as f:json.dump(r,f,indent=2)
print('Prepared source period-limit assembly from the actual comparison and existing endpoint primitive.')
