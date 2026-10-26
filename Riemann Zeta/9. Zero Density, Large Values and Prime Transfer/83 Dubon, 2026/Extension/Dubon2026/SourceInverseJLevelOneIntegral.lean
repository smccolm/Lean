import Dubon2026.SourceLevelOneJPolynomial
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-! DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> original all-weight
association -> actual Gamma1 Picard/H1 comparison -> regular differential
comparison. This is the inverse-j integral coefficient input to the cusp
valuation bound. Reuse the proved level-one j polynomial; no new modular
ring presentation is needed.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_isIntegral_adjoin_coeffEmb_jq_inv_of_mul_thetaL_eq_qExpansion_of_gamma_le. -/
namespace Dubon2026.SourceFunctionField.InverseJIntegral
noncomputable section
open UpperHalfPlane ModularForm
open scoped MatrixGroups
local notation "qL" => fun F : ℍ → ℂ => (qExpansion 1 F : LaurentSeries ℂ)
local notation "δ" => qL ModularForm.discriminant
local notation "e₄" => qL (E₄ : ℍ → ℂ)

theorem eisenstein_four_expansion_ne_zero : e₄ ≠ 0 := by
  intro h
  rw [← PowerSeries.coe_zero] at h
  have hz := HahnSeries.ofPowerSeries_injective h
  have hc : (qExpansion 1 (E₄ : ℍ → ℂ)).coeff 0 = 1 :=
    EisensteinSeries.E_qExpansion_coeff_zero (by norm_num) ⟨2, rfl⟩
  simp [hz] at hc

theorem levelOne_isIntegral (m : ℕ) {k : ℤ} (F : ModularForm 𝒮ℒ k)
    (hk : (3 : ℤ) * k = 12 * (m : ℤ)) :
    IsIntegral (Algebra.adjoin ℂ ({δ / e₄ ^ 3} : Set (LaurentSeries ℂ)))
      (qL (F : ℍ → ℂ) / e₄ ^ m) := by
  refine IsIntegral.of_pow (by norm_num : 0 < 3) ?_
  obtain ⟨P, hP, hq⟩ := exists_levelOne_j_polynomial m ((F.pow 3).mcast hk)
  rw [ModularForm.qExpansion_mcast, ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL,
    PowerSeries.coe_pow] at hq
  have hE := eisenstein_four_expansion_ne_zero
  have hΔ := discriminant_expansion_ne_zero
  have hx : (qL (F : ℍ → ℂ) / e₄ ^ m) ^ 3 =
      ∑ i ∈ Finset.range (m + 1), algebraMap ℂ (LaurentSeries ℂ) (P.coeff i) *
        (δ / e₄ ^ 3) ^ (m - i) := by
    rw [div_pow, ← pow_mul, pow_mul', hq,
      Polynomial.aeval_eq_sum_range' (Nat.lt_succ_of_le hP),
      Finset.sum_mul, Finset.sum_div]
    refine Finset.sum_congr rfl fun i hi => ?_
    have him : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le him
    rw [Nat.add_sub_cancel_left, Algebra.smul_def, mul_assoc, mul_div_assoc]
    congr 1
    have ha : e₄ ^ 3 ≠ 0 := pow_ne_zero _ hE
    generalize e₄ ^ 3 = a at ha ⊢
    rw [div_pow, div_pow, pow_add, pow_add, div_mul_eq_mul_div,
      mul_left_comm (a ^ i) (δ ^ i), mul_div_cancel_left₀ _ (pow_ne_zero _ hΔ),
      mul_div_mul_left _ _ (pow_ne_zero _ ha)]
  rw [hx]
  let A := Algebra.adjoin ℂ ({δ / e₄ ^ 3} : Set (LaurentSeries ℂ))
  have hm : (∑ i ∈ Finset.range (m + 1),
      algebraMap ℂ (LaurentSeries ℂ) (P.coeff i) * (δ / e₄ ^ 3) ^ (m - i)) ∈ A :=
    Subalgebra.sum_mem _ fun i _ => Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
      (Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton ℂ _) _)
  exact isIntegral_algebraMap (R := A) (A := LaurentSeries ℂ) (x := ⟨_, hm⟩)

end
end Dubon2026.SourceFunctionField.InverseJIntegral
