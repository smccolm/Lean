import Dubon2026.SourceInverseJPolynomialBounds
import Dubon2026.SourceOriginalInverseJAnalyticRelation

/-! DUB-17/18 -> regular-differential cusp forms -> decay at every cusp.
Original regularity and the actual analytic monic relation give a bound
independent of the full modular translate. This is the specific algebraic
estimate needed by the weight-two derivative identity.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane Filter Polynomial KaehlerDifferential SourceCurve
open scoped Topology BigOperators MatrixGroups

theorem original_regular_inverse_j_analytic_bound (N : ℕ) [NeZero N]
    (x : modularFunctionFieldOver N ℂ) (hx : x ≠ 0)
    (hreg : x • D ℂ (modularFunctionFieldOver N ℂ) (jOver N ℂ) ∈
      regularDifferentials ℂ (modularFunctionFieldOver N ℂ))
    {k : ℤ} (g h : ModularForm (CongruenceSubgroup.Gamma0 N) k) (hh : h ≠ 0)
    (hr : (x : LaurentSeries ℂ) * ModularRatios.qL h = ModularRatios.qL g) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ τ : ℍ in atImInfty, ∀ γ : SL(2, ℤ), h (γ • τ) ≠ 0 →
      ‖inverseJExpression (SourceLevelProjective.dedekindPsi N)
        (g (γ • τ) / h (γ • τ)) (JMultiplicity.jf τ)‖ ≤ C := by
  obtain ⟨n, c, _, hc⟩ := original_regular_inverse_j_analytic_relation N x hx hreg g h hh hr
  obtain ⟨B, hB, hcoeff⟩ := exists_inverse_j_polynomial_bound n c
  refine ⟨n * B + 1, by positivity, ?_⟩
  filter_upwards [hcoeff, JMultiplicity.eventually_j_ne_zero_atImInfty] with τ hτ hj
  intro γ hγ
  have hjγ : JMultiplicity.jf (γ • τ) ≠ 0 := by rwa [JMultiplicity.jf_smul]
  have he := hc (γ • τ) hγ hjγ
  rw [JMultiplicity.jf_smul] at he
  exact norm_le_of_monic_relation hB hτ he

end
end Dubon2026.SourceFunctionField
