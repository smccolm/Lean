import Dubon2026.SourceLipschitzTwoRealBoundary

/-! DUB-17/18 -> higher symmetric-power continuation -> arithmetic
automorphy -> original all-weight association -> original finite Gamma1
character realization -> Picard/H1 and diamond comparison -> differential
realization -> rational Fourier structure -> actual Fricke expansions.
Adapted from anthropics/fermats-last-theorem at
6e837e75355538c7f80bab5b956861e86c4eacc2 (Apache License 2.0).
Native Lipschitz summation and Weierstrass absolute summability are reused.
No external proof module or toolchain is imported. -/
namespace Dubon2026.SourceFricke
noncomputable section
open Complex Real PeriodPair
open UpperHalfPlane hiding I
open scoped UpperHalfPlane Manifold MatrixGroups ModularForm

theorem summable_one_div_sub_int_sq (w : ℂ) :
    Summable fun n : ℤ ↦ 1 / (w - n) ^ 2 := by
  refine (Equiv.neg ℤ).summable_iff.mp ?_
  simpa [Function.comp_def, sub_eq_add_neg] using summable_one_div_add_int_sq w

theorem tsum_int_one_div_sq : ∑' n : ℤ, 1 / ((n : ℂ)) ^ 2 = (π : ℂ) ^ 2 / 3 := by
  have h := two_mul_riemannZeta_eq_tsum_int_inv_pow_of_even (k := 2) le_rfl even_two
  simp only [Nat.cast_ofNat, riemannZeta_two] at h
  simp only [one_div, ← h]
  ring

theorem two_pi_I_sq : (2 * π * I : ℂ) ^ 2 = -(4 * π ^ 2) := by
  rw [mul_pow, I_sq]; ring

theorem neg_pi_sq_div_three_div : -((π : ℂ) ^ 2 / 3) = (2 * π * I) ^ 2 * (1 / 12) := by
  rw [two_pi_I_sq]; ring

theorem tsum_row_split (z l₀ : ℂ) :
    ∑' d : ℤ, (1 / (z - (l₀ + d)) ^ 2 - 1 / (l₀ + d) ^ 2) =
      ∑' d : ℤ, 1 / ((z - l₀) + d) ^ 2 - ∑' d : ℤ, 1 / (l₀ + d) ^ 2 := by
  rw [Summable.tsum_sub _ (summable_one_div_add_int_sq l₀), ← tsum_one_div_sub_int_sq (z - l₀)]
  · exact congrArg₂ _ (tsum_congr fun d ↦ by ring_nf) rfl
  · simpa [sub_sub] using summable_one_div_sub_int_sq (z - l₀)

theorem tsum_row_zero (z : ℂ) :
    ∑' d : ℤ, (1 / (z - d) ^ 2 - 1 / ((d : ℂ)) ^ 2) =
      ∑' d : ℤ, 1 / (z + d) ^ 2 - (π : ℂ) ^ 2 / 3 := by
  rw [Summable.tsum_sub (summable_one_div_sub_int_sq z), tsum_one_div_sub_int_sq,
    tsum_int_one_div_sq]
  simpa [one_div] using EisensteinSeries.linear_right_summable (0 : ℂ) 1 (k := 2) le_rfl

theorem lipschitz_two_of_im_neg' {w : ℂ} (hw : w.im < 0) :
    ∑' n : ℤ, 1 / (w + n) ^ 2 =
      (2 * π * I) ^ 2 * ∑' m : ℕ, (m : ℂ) * cexp (2 * π * I * (-w)) ^ m := by
  rw [lipschitz_two_of_im_neg hw]
  simp [mul_neg]

theorem cexp_two_pi_I_mul_add (a b : ℂ) :
    cexp (2 * π * I * (a + b)) = cexp (2 * π * I * a) * cexp (2 * π * I * b) := by
  rw [mul_add, Complex.exp_add]

theorem cexp_two_pi_I_mul_nat_mul (c : ℕ) (τ : ℂ) :
    cexp (2 * π * I * (c * τ)) = cexp (2 * π * I * τ) ^ c := by
  rw [← Complex.exp_nat_mul]
  ring_nf

theorem cexp_two_pi_I_mul_neg (z : ℂ) :
    cexp (2 * π * I * (-z)) = (cexp (2 * π * I * z))⁻¹ := by
  rw [mul_neg, Complex.exp_neg]

theorem lipschitz_row_pair {z τ : ℂ} (hτ : 0 < τ.im) (hz₁ : -τ.im < z.im) (hz₂ : z.im < τ.im)
    {c : ℕ} (hc : 0 < c) :
    ((∑' d : ℤ, 1 / ((z - c * τ) + d) ^ 2) - ∑' d : ℤ, 1 / (c * τ + d) ^ 2) +
      ((∑' d : ℤ, 1 / ((z - (-(c : ℂ)) * τ) + d) ^ 2) - ∑' d : ℤ, 1 / ((-(c : ℂ)) * τ + d) ^ 2) =
      (2 * π * I) ^ 2 * ∑' m : ℕ, (m : ℂ) *
        (cexp (2 * π * I * z) ^ m + (cexp (2 * π * I * z))⁻¹ ^ m - 2) *
          cexp (2 * π * I * τ) ^ (c * m) := by
  have hc1 : (1 : ℝ) ≤ c := by exact_mod_cast hc
  have hcτ : τ.im ≤ c * τ.im := by nlinarith
  have hA : (z - c * τ).im < 0 := by
    simp only [Complex.sub_im, Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul,
      add_zero]
    linarith
  have hB : 0 < ((c : ℂ) * τ).im := by
    simp only [Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero]
    linarith
  have hC : 0 < (z - (-(c : ℂ)) * τ).im := by
    simp only [Complex.sub_im, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.natCast_re,
      Complex.natCast_im, neg_zero, zero_mul, add_zero]
    linarith
  have hD : ((-(c : ℂ)) * τ).im < 0 := by
    simp only [Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.natCast_re,
      Complex.natCast_im, neg_zero, zero_mul, add_zero]
    linarith
  have sA := summable_nat_mul_cexp_pow (w := -(z - c * τ)) (by simpa using hA)
  have sB := summable_nat_mul_cexp_pow hB
  have sC := summable_nat_mul_cexp_pow hC
  have sD := summable_nat_mul_cexp_pow (w := -((-(c : ℂ)) * τ)) (by simpa using hD)
  rw [lipschitz_two_of_im_neg' hA, lipschitz_two_of_im_pos hB, lipschitz_two_of_im_pos hC,
    lipschitz_two_of_im_neg' hD, ← mul_sub, ← mul_sub, ← mul_add, ← sA.tsum_sub sB,
    ← sC.tsum_sub sD, ← (sA.sub sB).tsum_add (sC.sub sD)]
  congr 1
  refine tsum_congr fun m ↦ ?_
  rw [show -(z - c * τ) = c * τ + -z by ring, show z - (-(c : ℂ)) * τ = c * τ + z by ring,
    show -((-(c : ℂ)) * τ) = c * τ by ring, cexp_two_pi_I_mul_add, cexp_two_pi_I_mul_add,
    cexp_two_pi_I_mul_neg, cexp_two_pi_I_mul_nat_mul]
  ring

theorem lipschitz_row_zero {z : ℂ} (hz : z ∈ Complex.integerComplement) :
    (∑' d : ℤ, 1 / (z + d) ^ 2) - ∑' d : ℤ, 1 / ((d : ℂ)) ^ 2 =
      (2 * π * I) ^ 2 * (cexp (2 * π * I * z) / (1 - cexp (2 * π * I * z)) ^ 2 + 1 / 12) := by
  rw [lipschitz_two_closed hz, tsum_int_one_div_sq, sub_eq_add_neg, neg_pi_sq_div_three_div]
  ring

theorem lipschitz_rows_qExpansion {z τ : ℂ} (hτ : 0 < τ.im) (hz₁ : -τ.im < z.im)
    (hz₂ : z.im < τ.im) (hz : z ∈ Complex.integerComplement)
    (hS : Summable fun c : ℤ ↦
      (∑' d : ℤ, 1 / ((z - c * τ) + d) ^ 2) - ∑' d : ℤ, 1 / (c * τ + d) ^ 2) :
    ∑' c : ℤ, ((∑' d : ℤ, 1 / ((z - c * τ) + d) ^ 2) - ∑' d : ℤ, 1 / (c * τ + d) ^ 2) =
      (2 * π * I) ^ 2 *
        (cexp (2 * π * I * z) / (1 - cexp (2 * π * I * z)) ^ 2 + 1 / 12 +
          ∑' c : ℕ+, ∑' m : ℕ, (m : ℂ) *
            (cexp (2 * π * I * z) ^ m + (cexp (2 * π * I * z))⁻¹ ^ m - 2) *
              cexp (2 * π * I * τ) ^ ((c : ℕ) * m)) := by
  have h3 : Summable fun c : ℕ+ ↦
      (∑' d : ℤ, 1 / ((z - ((c : ℤ) : ℂ) * τ) + d) ^ 2) -
        ∑' d : ℤ, 1 / (((c : ℤ) : ℂ) * τ + d) ^ 2 :=
    hS.comp_injective fun a b h ↦ by exact_mod_cast h
  have h4 : Summable fun c : ℕ+ ↦
      (∑' d : ℤ, 1 / ((z - ((-(c : ℤ) : ℤ) : ℂ) * τ) + d) ^ 2) -
        ∑' d : ℤ, 1 / (((-(c : ℤ) : ℤ) : ℂ) * τ + d) ^ 2 :=
    hS.comp_injective (f := fun c ↦ _) fun a b h ↦ by simpa using h
  rw [tsum_int_eq_zero_add_tsum_pnat hS, add_assoc, ← h3.tsum_add h4]
  simp only [Int.cast_zero, zero_mul, sub_zero, zero_add]
  rw [lipschitz_row_zero hz, mul_add _ _ (∑' c : ℕ+, _), ← tsum_mul_left]
  congr 1
  refine tsum_congr fun c ↦ ?_
  have := lipschitz_row_pair hτ hz₁ hz₂ c.pos
  push_cast at this ⊢
  exact this


end
end Dubon2026.SourceFricke
