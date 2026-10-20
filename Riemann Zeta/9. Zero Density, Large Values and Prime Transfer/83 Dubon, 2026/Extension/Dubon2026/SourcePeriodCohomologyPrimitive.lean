import Dubon2026.SourcePeriodPolynomialAction

/-! The corrected scalar Eichler integral of a cohomologically trivial original form.
DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> higher symmetric-power continuation
-> modular Galois association -> original analytic H1 injectivity.
The native H1 kernel supplies a genuine coboundary. Its exact dual action,
together with the already proved Eichler transformation, removes the period
error. SourcePeriodCohomologyBounded supplies boundedness at all cusps, and
SourcePeriodCohomologyInjective proves injectivity.
-/

namespace Dubon2026
noncomputable section
open Complex Matrix.SpecialLinearGroup MvPolynomial OnePoint
open UpperHalfPlane hiding I
open scoped Real Nat MatrixGroups ModularForm

variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {k : ℤ} {n : ℕ}

/-- Vanishing of the actual native H1 class supplies a single dual period coboundary. -/
theorem sourcePeriodH1_eq_zero_coboundary (f : CuspForm (Γ.map (mapGL ℝ)) k)
    (hk : k = n + 2) (hf : sourcePeriodH1 f hk ∞ = 0) :
    ∃ L : Module.Dual ℂ (homogeneousSubmodule (Fin 2) ℂ n),
      ∀ γ : Γ, sourcePeriodCocycle f hk ∞ γ = (sourcePeriodDualRep Γ n).ρ γ L - L := by
  obtain ⟨L, hL⟩ := (groupCohomology.H1π_eq_zero_iff _).mp hf
  exact ⟨L, fun γ => (congrFun hL γ).symm⟩

/-- A native coboundary makes the original scalar Eichler integral invariant after
subtracting its explicit period polynomial. -/
theorem sourceEichlerIntegral_corrected_slash (f : CuspForm (Γ.map (mapGL ℝ)) k)
    (hk : k = n + 2) {h : ℝ} (hh : 0 < h)
    (hΓ : h ∈ (Γ.map (mapGL ℝ)).strictPeriods)
    (L : Module.Dual ℂ (homogeneousSubmodule (Fin 2) ℂ n))
    (hL : ∀ γ : Γ,
      sourcePeriodCocycle f hk ∞ γ = (sourcePeriodDualRep Γ n).ρ γ L - L)
    (γ : Γ) :
    (fun τ : UpperHalfPlane => sourceEichlerIntegral h (n + 1) f τ -
      (-2 * π * I) ^ (n + 1) / (n ! : ℂ) *
        (sourcePeriodCorrectionPolynomial n L).eval (τ : ℂ)) ∣[-(n : ℤ)] γ.val =
      fun τ : UpperHalfPlane => sourceEichlerIntegral h (n + 1) f τ -
        (-2 * π * I) ^ (n + 1) / (n ! : ℂ) *
          (sourcePeriodCorrectionPolynomial n L).eval (τ : ℂ) := by
  funext τ
  have hp := congrArg (fun D : Module.Dual ℂ (homogeneousSubmodule (Fin 2) ℂ n) =>
    D (sourceEichlerBinaryForm n (τ : ℂ))) (hL γ⁻¹)
  dsimp only at hp
  rw [sourcePeriodCocycle_apply, sourceEichlerBinaryForm_periodIntegrand] at hp
  change sourceCuspIntegral (fun z => f z * ((z : ℂ) - τ) ^ n)
      ∞ (mapGL ℚ γ.val⁻¹ • ∞) =
    ((sourcePeriodDualRep Γ n).ρ γ⁻¹ L) (sourceEichlerBinaryForm n (τ : ℂ)) -
      L (sourceEichlerBinaryForm n (τ : ℂ)) at hp
  have he := sourceCuspForm_eichlerIntegral_slash_apply_of_mem hk f hh hΓ
    (Subgroup.mem_map_of_mem (mapGL ℝ) γ.property) τ
  rw [sourceCuspIntegral_symm, hp] at he
  have hq := congrFun (sourcePeriodCorrectionPolynomial_slash n L γ) τ
  simp only [ModularForm.SL_slash_apply, neg_neg, zpow_natCast,
    sourcePeriodCorrectionPolynomial_eval] at he hq ⊢
  linear_combination he -
    (-2 * π * I) ^ (n + 1) / (n ! : ℂ) * hq

end
end Dubon2026
