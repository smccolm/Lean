from pathlib import Path
s=Path(__file__).parent
c=(s/'anthropic-peaked-leaves-1535/S_ModularCurve_SiegelUnit_exists_isIntegral_hasSum_prod_siegelFun_pow.lean.txt').read_text(encoding='utf-8')
sig=c[c.index('theorem solution (N'):c.index(' :=\n  SExpPi.main')]
sig=sig.replace('theorem solution','theorem exists_integral_hasSum_prod_siegelFun_pow')
header='''import SourceSiegelProductLeadingCoefficient1599b
import SourceSiegelProductPhases1600a

/-! DUB-17/18 -> original Gamma1 degree/genus preservation -> level-power
slash integrality -> actual peaked auxiliary -> exact integral finite Siegel
product expansion. Assemble actual coefficients, literal product phases,
nonzero leading coefficient, level-cleared inverse and cusp limit. Native
q-series multiplication and cusp limits remove the candidate's separate
choice/dummy-factor construction and repeated convergence proof.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_SiegelUnit_exists_isIntegral_hasSum_prod_siegelFun_pow. -/
namespace Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.FiniteExpansion
noncomputable section
open Complex Filter Finset Topology
open scoped Real

theorem qParam_pow_eq (N : ℕ) (τ : ℂ) (n : ℕ) :
    Function.Periodic.qParam (N : ℝ) τ ^ n = cexp (2 * π * I * (n : ℂ) * τ / (N : ℂ)) := by
  rw [Function.Periodic.qParam, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem hasSum_productSeries (N : ℕ) [NeZero N] (e : ZMod N → ZMod N → ℕ) (τ : UpperHalfPlane) :
    HasSum (fun n : ℕ => PowerSeries.coeff n (productSeries N e) *
      Function.Periodic.qParam (N : ℝ) (τ : ℂ) ^ n)
      ((∏ r : ZMod N, ∏ s : ZMod N,
        siegelFun N (r.val : ℤ) (s.val : ℤ) (τ : ℂ) ^ (12 * N * e r s)) /
        (phase N e * cexp (2 * π * I * (orderSum N e : ℂ) * (τ : ℂ) / (N : ℂ)))) := by
  rw [normalized_product_eq]
  exact expands_productSeries N e τ

theorem tendsto_productSeries (N : ℕ) [NeZero N] (e : ZMod N → ZMod N → ℕ) :
    Tendsto (fun τ : UpperHalfPlane =>
      (∏ r : ZMod N, ∏ s : ZMod N,
        siegelFun N (r.val : ℤ) (s.val : ℤ) (τ : ℂ) ^ (12 * N * e r s)) /
        (phase N e * cexp (2 * π * I * (orderSum N e : ℂ) * (τ : ℂ) / (N : ℂ))))
      UpperHalfPlane.atImInfty (𝓝 (PowerSeries.coeff 0 (productSeries N e))) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  exact Dubon2026.SourceFunctionField.Realized.tendsto_atImInfty hN (hasSum_productSeries N e)

'''
proof=''' := by
  refine ⟨phase N e, fun n => PowerSeries.coeff n (productSeries N e), phase_pow N e,
    integral_productSeries N e, ?_, productSeries_zero_ne_zero N e he,
    integral_level_inverse_productSeries_zero N e he, fun τ => ?_, ?_⟩
  · simpa only [EulerExpansion.zeta, Int.cast_natCast] using productSeries_zero_eq N e
  · simpa only [qParam_pow_eq, orderSum] using hasSum_productSeries N e τ
  · exact tendsto_productSeries N e

end
end Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.FiniteExpansion
'''
f=s/'SourceSiegelFiniteProductExpansion1601a.lean';assert not f.exists();f.write_text(header+sig+proof,encoding='utf-8')
print('Prepared exact source finite-product assembly.')
