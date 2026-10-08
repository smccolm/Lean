import Dubon2026.HigherAugmentedEuler

/-! # Actual divided differences cancel the higher augmented tensor pole under a zero at one -/

namespace Dubon2026

noncomputable section

/-- The true principal pole numerator vanishes at the actual trivial zero -2. -/
theorem principalPoleNumerator_neg_two (Q : ℕ) [NeZero Q] :
    DirichletCharacter.LFunctionTrivChar₁ Q (-2) = 0 := by
  have hz := riemannZeta_neg_two_mul_nat_add_one 0
  norm_num at hz
  rw [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne (by norm_num),
    DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta (by norm_num), hz]
  ring

/-- The literal principal numerator, symmetric divided difference and positive even continuations. -/
def higherSymmetricPoleCancellation (Q : ℕ) [NeZero Q] (H : ℕ → ℂ → ℂ)
    (r : ℕ) (s : ℂ) : ℂ :=
  DirichletCharacter.LFunctionTrivChar₁ Q s ^ 2 * (dslope (H r) 1 s) ^ 2 *
    ∏ t ∈ Finset.range r, H (2 * (t + 1)) s

/-- Entire positive symmetric continuations make the displayed divided-difference construction entire. -/
theorem higherSymmetricPoleCancellation_differentiable (Q : ℕ) [NeZero Q]
    (H : ℕ → ℂ → ℂ) (hH : ∀ n, 0 < n → Differentiable ℂ (H n))
    {r : ℕ} (hr : 0 < r) : Differentiable ℂ (higherSymmetricPoleCancellation Q H r) := by
  have hd : Differentiable ℂ (dslope (H r) 1) := by
    rw [← differentiableOn_univ]
    exact (Complex.differentiableOn_dslope Filter.univ_mem).mpr (hH r hr).differentiableOn
  exact ((DirichletCharacter.differentiable_LFunctionTrivChar₁ Q).pow 2 |>.mul (hd.pow 2)).mul
    (Differentiable.fun_finsetProd (fun t _ => hH (2 * (t + 1)) (by omega)))

/-- The true principal trivial zero survives in the explicit higher pole-cancelled product. -/
theorem higherSymmetricPoleCancellation_neg_two (Q : ℕ) [NeZero Q]
    (H : ℕ → ℂ → ℂ) (r : ℕ) : higherSymmetricPoleCancellation Q H r (-2) = 0 := by
  simp [higherSymmetricPoleCancellation, principalPoleNumerator_neg_two]

/-- Under a zero at one the explicit divided difference equals precisely the genuine double-principal product. -/
theorem higherSymmetricPoleCancellation_eq (Q : ℕ) [NeZero Q]
    (H : ℕ → ℂ → ℂ) (r : ℕ) (hz : H r 1 = 0) {s : ℂ} (hs : s ≠ 1) :
    higherSymmetricPoleCancellation Q H r s =
      DirichletCharacter.LFunctionTrivChar Q s ^ 2 * H r s ^ 2 *
        ∏ t ∈ Finset.range r, H (2 * (t + 1)) s := by
  rw [higherSymmetricPoleCancellation, DirichletCharacter.LFunctionTrivChar₁,
    Function.update_of_ne hs, dslope_of_ne _ hs, slope, vsub_eq_sub, hz, sub_zero, smul_eq_mul]
  field_simp [sub_ne_zero.mpr hs]

end
end Dubon2026
