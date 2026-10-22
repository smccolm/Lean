import Dubon2026.SourcePeriodPairScaling
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing

/-! DUB-17/18 -> the numerical modular genus -> elliptic ramification ->
the analytic j-invariant separates full modular-group orbits. Adapted
from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ModularCurve_exists_smul_eq_of_E4_cube_div_discriminant_eq.
This uses actual period lattices and the proved Weierstrass equation.
-/
namespace Dubon2026.SourceFunctionField.JOrbitSeparation
noncomputable section
open UpperHalfPlane ModularForm EisensteinSeries Complex
open scoped MatrixGroups Real Topology
private lemma pow_four_six_of_sq {t x : ℂ} (h : t ^ 2 = x) : t ^ 4 = x ^ 2 ∧ t ^ 6 = x ^ 3 := by
  constructor <;> [rw [show (4:ℕ) = 2 * 2 from rfl]; rw [show (6:ℕ) = 2 * 3 from rfl]] <;>
    rw [pow_mul, h]

theorem exists_scalar {a₁ b₁ a₂ b₂ : ℂ}
    (h₁ : a₁ ^ 3 - b₁ ^ 2 ≠ 0) (h₂ : a₂ ^ 3 - b₂ ^ 2 ≠ 0)
    (R1 : a₁ ^ 3 * b₂ ^ 2 = a₂ ^ 3 * b₁ ^ 2) :
    ∃ w : ℂ, w ≠ 0 ∧ a₂ = w ^ 4 * a₁ ∧ b₂ = w ^ 6 * b₁ := by
  by_cases ha₁ : a₁ = 0
  ·
    subst ha₁
    have hb₁ : b₁ ≠ 0 := by rintro rfl; exact h₁ (by ring)
    have ha₂ : a₂ = 0 := by
      have : a₂ ^ 3 * b₁ ^ 2 = 0 := by rw [← R1]; ring
      simpa [hb₁] using this
    subst ha₂
    have hb₂ : b₂ ≠ 0 := by rintro rfl; exact h₂ (by ring)
    obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq (b₂ / b₁) (by norm_num : 0 < 6)
    have ht0 : t ≠ 0 := by
      rintro rfl
      rw [zero_pow (by norm_num), eq_comm, div_eq_zero_iff] at ht
      exact ht.elim hb₂ hb₁
    exact ⟨t, ht0, by simp, by rw [ht]; field_simp⟩
  ·
    have ha₂ : a₂ ≠ 0 := by
      intro ha₂; subst ha₂
      have hb₂ : b₂ = 0 := by
        have : a₁ ^ 3 * b₂ ^ 2 = 0 := by rw [R1]; ring
        simpa [ha₁] using this
      exact h₂ (by rw [hb₂]; ring)
    by_cases hb₁ : b₁ = 0
    · subst hb₁
      have hb₂ : b₂ = 0 := by
        have : a₁ ^ 3 * b₂ ^ 2 = 0 := by rw [R1]; ring
        simpa [ha₁] using this
      subst hb₂
      obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq (a₂ / a₁) (by norm_num : 0 < 4)
      have ht0 : t ≠ 0 := by
        rintro rfl
        rw [zero_pow (by norm_num), eq_comm, div_eq_zero_iff] at ht
        exact ht.elim ha₂ ha₁
      exact ⟨t, ht0, by rw [ht]; field_simp, by simp⟩
    · have hb₂ : b₂ ≠ 0 := by
        intro hb₂
        have : a₂ ^ 3 * b₁ ^ 2 = 0 := by rw [← R1, hb₂]; ring
        simp [ha₂, hb₁] at this
      obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq (a₁ * b₂ / (a₂ * b₁)) (by norm_num : 0 < 2)
      have ht0 : t ≠ 0 := by
        rintro rfl
        rw [zero_pow (by norm_num), eq_comm, div_eq_zero_iff, mul_eq_zero, mul_eq_zero] at ht
        rcases ht with (h | h) | (h | h) <;> contradiction
      obtain ⟨ht4, ht6⟩ := pow_four_six_of_sq ht
      have ha : a₂ = t ^ 4 * a₁ := by
        rw [ht4, div_pow, div_mul_eq_mul_div,
          eq_div_iff (pow_ne_zero _ (mul_ne_zero ha₂ hb₁))]
        linear_combination -R1
      have hb : b₂ = t ^ 6 * b₁ := by
        rw [ht6, div_pow, div_mul_eq_mul_div,
          eq_div_iff (pow_ne_zero _ (mul_ne_zero ha₂ hb₁))]
        linear_combination -(b₁ * b₂) * R1
      exact ⟨t, ht0, ha, hb⟩

lemma int_indep (τ : ℍ) {m n m' n' : ℤ}
    (h : (m : ℂ) * τ + n = m' * τ + n') : m = m' ∧ n = n' := by
  have him := congrArg Complex.im h
  simp only [add_im, mul_im, intCast_re, intCast_im, zero_mul, add_zero, coe_im,
    coe_re] at him
  have hm : m = m' := by
    have : ((m : ℝ) - m') * τ.im = 0 := by linarith
    rcases mul_eq_zero.1 this with h0 | h0
    · exact_mod_cast sub_eq_zero.1 h0
    · exact absurd h0 τ.im_pos.ne'
  subst hm
  refine ⟨rfl, ?_⟩
  have := add_left_cancel h
  exact_mod_cast this

theorem exists_sl2z_of_lattice_rel (τ₁ τ₂ : ℍ) {u : ℂ} (hu : u ≠ 0)
    {a b c d p q r s : ℤ}
    (h1 : u * (a * τ₁ + b) = τ₂) (h2 : u * (c * τ₁ + d) = 1)
    (h3 : p * (τ₂ : ℂ) + q = u * τ₁) (h4 : r * (τ₂ : ℂ) + s = u) :
    ∃ γ : SL(2, ℤ), γ • τ₁ = τ₂ := by

  have hrow₁ : p * a + q * c = 1 ∧ p * b + q * d = 0 := by
    refine int_indep τ₁ (mul_left_cancel₀ hu ?_)
    push_cast
    linear_combination p * h1 + q * h2 + h3
  have hrow₂ : r * a + s * c = 0 ∧ r * b + s * d = 1 := by
    refine int_indep τ₁ (mul_left_cancel₀ hu ?_)
    push_cast
    linear_combination r * h1 + s * h2 + h4
  have hdet : (a * d - b * c) * (p * s - q * r) = 1 := by
    linear_combination (r * b + s * d) * hrow₁.1 - (r * a + s * c) * hrow₁.2 + hrow₂.2

  have hz : (c : ℂ) * τ₁ + d ≠ 0 := by
    intro h0; rw [h0, mul_zero] at h2; exact zero_ne_one h2
  have hτ₂ : (τ₂ : ℂ) * (c * τ₁ + d) = a * τ₁ + b := by
    linear_combination -((c : ℂ) * τ₁ + d) * h1 + ((a : ℂ) * τ₁ + b) * h2
  have him : τ₂.im * Complex.normSq (c * τ₁ + d) = (a * d - b * c) * τ₁.im := by
    have h := congrArg Complex.im
      (show (τ₂ : ℂ) * (Complex.normSq ((c : ℂ) * τ₁ + d) : ℂ) =
          (a * τ₁ + b) * (starRingEnd ℂ) (c * τ₁ + d) by
        rw [← Complex.mul_conj, ← mul_assoc, hτ₂])
    simp only [mul_im, ofReal_re, ofReal_im, mul_zero, add_zero, add_im, add_re, mul_re,
      intCast_re, intCast_im, zero_mul, sub_zero, Complex.conj_re, Complex.conj_im, coe_re,
      coe_im] at h
    rw [zero_add] at h
    rw [h]
    ring
  have hdet1 : a * d - b * c = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hdet with h | h
    · exact h
    · exfalso
      have hpos : 0 < τ₂.im * Complex.normSq (c * τ₁ + d) :=
        mul_pos τ₂.im_pos (Complex.normSq_pos.2 hz)
      rw [him] at hpos
      have : ((a * d - b * c : ℤ) : ℝ) = -1 := by exact_mod_cast h
      push_cast at this
      rw [this] at hpos
      linarith [τ₁.im_pos]

  let γ : SL(2, ℤ) := ⟨!![a, b; c, d], by rw [Matrix.det_fin_two_of]; linarith⟩
  refine ⟨γ, ?_⟩
  apply UpperHalfPlane.ext
  rw [coe_specialLinearGroup_apply]
  simp only [γ, algebraMap_int_eq, eq_intCast, ofReal_intCast, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Matrix.empty_val']
  rw [div_eq_iff hz, hτ₂]


end
end Dubon2026.SourceFunctionField.JOrbitSeparation
