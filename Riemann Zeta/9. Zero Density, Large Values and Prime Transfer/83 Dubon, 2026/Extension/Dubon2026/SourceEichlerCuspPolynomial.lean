import Dubon2026.SourcePeriodCohomologyPrimitive
import Dubon2026.SourceEichlerPolynomialPeriodicity

/-! The polynomial correction at every original rational cusp.
DUB-17/18 -> modular Galois association -> original analytic H1 injectivity
-> boundedness of the corrected scalar Eichler integral at all cusps.
The actual convergent period expansion and exact binary coefficient action
express each translate as its decaying Eichler series plus a polynomial.
-/

namespace Dubon2026
noncomputable section
open Complex Matrix.SpecialLinearGroup MvPolynomial OnePoint SourceModularSymbols
open UpperHalfPlane hiding I
open scoped Real Nat MatrixGroups ModularForm

/-- The genuine convergent cusp integral is a polynomial in the Eichler parameter. -/
theorem sourceCuspIntegral_exists_polynomial
    {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] {F : Type*}
    [FunLike F UpperHalfPlane ℂ] {k : ℤ} [CuspFormClass F Γ k]
    {n : ℕ} (f : F) (hk : k = n + 2) (α β : OnePoint ℚ) :
    ∃ p : Polynomial ℂ, ∀ z : ℂ,
      sourceCuspIntegral (fun τ => f τ * ((τ : ℂ) - z) ^ n) α β = p.eval z := by
  refine ⟨∑ j ∈ Finset.range (n + 1),
    Polynomial.C ((n.choose j : ℂ) *
      sourceCuspIntegral (fun τ => f τ * (τ : ℂ) ^ j) α β) *
      (-Polynomial.X) ^ (n - j), ?_⟩
  intro z
  rw [sourceCuspIntegral_mul_sub_pow f hk]
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_neg, Polynomial.eval_X]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Slashing the original corrected primitive gives the translated original
Eichler integral plus an actual polynomial correction. -/
theorem sourceEichlerIntegral_corrected_slash_exists_polynomial
    {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] [Γ'.IsArithmetic]
    {F F' : Type*} [FunLike F UpperHalfPlane ℂ] [FunLike F' UpperHalfPlane ℂ]
    {k : ℤ} [CuspFormClass F Γ k] [CuspFormClass F' Γ' k]
    {n : ℕ} (hk : k = n + 2) (f : F) (f' : F')
    {h h' : ℝ} (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods)
    (hh' : 0 < h') (hΓ' : h' ∈ Γ'.strictPeriods) (σ : SL(2, ℤ))
    (hf' : ⇑f' = ⇑f ∣[k] σ)
    (L : Module.Dual ℂ (homogeneousSubmodule (Fin 2) ℂ n)) :
    ∃ p : Polynomial ℂ, ∀ τ : UpperHalfPlane,
      ((fun z : UpperHalfPlane => sourceEichlerIntegral h (n + 1) f z -
        (-2 * π * I) ^ (n + 1) / (n ! : ℂ) *
          (sourcePeriodCorrectionPolynomial n L).eval (z : ℂ)) ∣[-(n : ℤ)] σ) τ =
      sourceEichlerIntegral h' (n + 1) f' τ + p.eval (τ : ℂ) := by
  obtain ⟨r, hr⟩ := sourceCuspIntegral_exists_polynomial f' hk (mapGL ℚ σ⁻¹ • ∞) ∞
  let γ : (⊤ : Subgroup SL(2, ℤ)) := ⟨σ, Subgroup.mem_top σ⟩
  let q := sourcePeriodCorrectionPolynomial n
    ((sourcePeriodDualRep ⊤ n).ρ γ⁻¹ L)
  let A : ℂ := (-2 * π * I) ^ (n + 1) / (n ! : ℂ)
  refine ⟨-Polynomial.C A * (r + q), ?_⟩
  intro τ
  have he := sourceCuspForm_eichlerIntegral_slash_apply hk f hh hΓ f' hh' hΓ' σ hf' τ
  rw [hr] at he
  have hq := congrFun (sourcePeriodCorrectionPolynomial_slash n L γ) τ
  change ((fun z : UpperHalfPlane =>
      (sourcePeriodCorrectionPolynomial n L).eval (z : ℂ)) ∣[-(n : ℤ)] σ) τ =
      q.eval (τ : ℂ) at hq
  simp only [ModularForm.SL_slash_apply, neg_neg, zpow_natCast] at he hq ⊢
  simp only [Polynomial.eval_mul, Polynomial.eval_neg, Polynomial.eval_C,
    Polynomial.eval_add]
  change _ = sourceEichlerIntegral h' (n + 1) f' τ + -A * (r.eval (τ : ℂ) + q.eval (τ : ℂ))
  change sourceEichlerIntegral h (n + 1) f (σ • τ) * denom σ τ ^ n =
    sourceEichlerIntegral h' (n + 1) f' τ - A * r.eval (τ : ℂ) at he
  linear_combination he - A * hq

end
end Dubon2026
