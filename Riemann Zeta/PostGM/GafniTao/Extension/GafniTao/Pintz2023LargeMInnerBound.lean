import GafniTao.Pintz2023LargeMInterval
import GafniTao.Pintz2023RoundedCorollaryThree

/-!
# The inner estimate in Pintz equation (4.14)

This specializes the rounded Corollary-3 theorem to the exact quotient
interval `(A/d,B/d]` left by the Möbius factorization.
-/

open Complex Finset

namespace GafniTao

noncomputable section

theorem nat_div_two_mul_le_two_mul_div_add_one
    {A d : ℕ} (hd : 0 < d) :
    (2 * A) / d ≤ 2 * (A / d) + 1 := by
  have hA : A < (A / d + 1) * d := by
    exact (Nat.div_lt_iff_lt_mul hd).1 (Nat.lt_succ_self (A / d))
  have hTwo :=
    (Nat.mul_lt_mul_left (by omega : 0 < (2 : ℕ))).2 hA
  have hDiv : (2 * A) / d < 2 * (A / d) + 2 := by
    rw [Nat.div_lt_iff_lt_mul hd]
    simpa [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm,
      Nat.mul_left_comm] using hTwo
  omega

theorem pintz2023LargeMInnerBlock_corollary_three
    (r : ℕ) (epsilon B₀ : ℝ) (hr : 3 ≤ r)
    (hepsilon : 0 < epsilon) (hB₀ : 0 < B₀) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (xi Q t T : ℝ) (A B d : ℕ),
        xi ≤ pintz2023HBAlpha r - 6 * epsilon →
        0 < 1 - ((r : ℝ) - 1) * xi -
          6 * (r : ℝ) * epsilon →
        xi + 3 * epsilon ≤ 1 →
        1 ≤ Q →
        pintz2023CriticalScale r xi epsilon T ≤ Q →
        0 < |t| → |t| ≤ T → 1 ≤ T →
        0 < d → d ≤ A → B ≤ 2 * A →
        ((max (A / d) (Nat.ceil Q) : ℕ) : ℝ) ≤
          B₀ * |t| ^ (2 / (r : ℝ)) →
        ‖pintz2023LargeMInnerBlock B d (Finset.Ioc A B) Q
            (((1 - xi : ℝ) : ℂ) + I * (t : ℂ))‖ ≤
          C * Q ^ (-3 * epsilon) := by
  obtain ⟨C, hC, hrounded⟩ :=
    pintz2023_corollary_three_rounded r epsilon B₀ hr hepsilon hB₀
  refine ⟨C, hC, ?_⟩
  intro xi Q t T A B d hxi hden hxiOne hQ hcritical ht htT hT
    hd hdA hBA hphysical
  have hAdiv : 0 < A / d := Nat.div_pos hdA hd
  have hBdiv : B / d ≤ 2 * (A / d) + 1 := by
    exact (Nat.div_le_div_right hBA).trans
      (nat_div_two_mul_le_two_mul_div_add_one hd)
  rw [pintz2023LargeMInnerBlock_source_interval_eq_weighted
    (R := Q) hd (by linarith)]
  exact hrounded xi Q t T (A / d) (B / d) hxi hden hxiOne hQ
    hcritical ht htT hT hAdiv hBdiv hphysical

#print axioms nat_div_two_mul_le_two_mul_div_add_one
#print axioms pintz2023LargeMInnerBlock_corollary_three

end

end GafniTao
