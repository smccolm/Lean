import GafniTao.FordLemma63Equation69

/-!
# Ford Lemma 6.3

Assembly of equations (6.7)--(6.9), including the exact `2s`-th root which
produces Ford's leading constant `4`.
-/

open Finset Set
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- Ford's Lemma 6.3 in its literal shifted, finite-interval form. -/
theorem fordLemma63_native
    {s k M N R : ℕ} {u t : ℝ}
    (hs : 1 ≤ s) (hk : 2 ≤ k) (hM : 1 ≤ M) (hMN : M ≤ N)
    (hN : 1 ≤ N) (hR : R ≤ 2 * N)
    (hu0 : 0 < u) (hu1 : u ≤ 1) (ht : 0 < t)
    (htN : t ≤ (N : ℝ) ^ k)
    (hscale : t * (M : ℝ) ^ (k + 1) ≤ (N : ℝ) ^ (k + 1)) :
    ‖fordShiftedExponentialSum N R u t‖ ≤
      4 * ((N : ℝ) ^ (1 - 1 / (2 * s : ℝ)) / M) *
        ((Real.pi ^ k * (k.factorial : ℝ) * (k : ℝ) ^ k *
            (M : ℝ) ^ fordVinogradovKappa k) *
          fordLemma63W N k M t *
          (fordVinogradovMomentNat s k M : ℝ)) ^
            (1 / (2 * s : ℝ)) +
        (N : ℝ) / M + M := by
  let D : ℝ := Real.pi ^ k * (k.factorial : ℝ) * (k : ℝ) ^ k *
    (M : ℝ) ^ fordVinogradovKappa k
  let W : ℝ := fordLemma63W N k M t
  let J : ℝ := fordVinogradovMomentNat s k M
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hW : 0 ≤ W := by dsimp [W]; unfold fordLemma63W; positivity
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have hrs : (0 : ℝ) < 2 * s := by
    have : (0 : ℝ) < s := by exact_mod_cast (Nat.zero_lt_of_lt hs)
    positivity
  have hq : 0 ≤ (1 / (2 * s : ℝ)) := by positivity
  have h67 := ford_equation_6_7
    (M := M) (N := N) (R := R) (s := s) (u := u) (t := t)
    hM hMN hN hs hR hu0
  have h69 := ford_equation_6_9
    (s := s) (k := k) (M := M) (N := N) (u := u) (t := t)
    hs hk hM hN hu0 hu1 ht htN hscale
  have hmoment : fordLemma63Moment M N u t s ≤
      D * W * ((2 : ℝ) ^ (4 * s) * J) := by
    simpa only [fordLemma63Moment, D, W, J] using h69
  have hroot :
      (fordLemma63Moment M N u t s) ^ (1 / (2 * s : ℝ)) ≤
        (D * W * ((2 : ℝ) ^ (4 * s) * J)) ^
          (1 / (2 * s : ℝ)) := by
    apply Real.rpow_le_rpow
    · unfold fordLemma63Moment
      positivity
    · exact hmoment
    · exact hq
  have hfour :
      (D * W * ((2 : ℝ) ^ (4 * s) * J)) ^
          (1 / (2 * s : ℝ)) =
        4 * (D * W * J) ^ (1 / (2 * s : ℝ)) := by
    have hX : 0 ≤ D * W * J := by positivity
    have htwo : 0 ≤ (2 : ℝ) ^ (4 * s) := by positivity
    rw [show D * W * ((2 : ℝ) ^ (4 * s) * J) =
      (2 : ℝ) ^ (4 * s) * (D * W * J) by ring]
    rw [Real.mul_rpow htwo hX]
    have hp :
        ((2 : ℝ) ^ (4 * s)) ^ (1 / (2 * s : ℝ)) = 4 := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      have hexp : ((4 * s : ℕ) : ℝ) * (1 / (2 * s : ℝ)) = 2 := by
        push_cast
        field_simp [ne_of_gt hrs]
        ring
      rw [hexp, Real.rpow_two]
      norm_num
    rw [hp]
  calc
    ‖fordShiftedExponentialSum N R u t‖ ≤
        (N : ℝ) ^ (1 - 1 / (2 * s : ℝ)) / M *
            (fordLemma63Moment M N u t s) ^ (1 / (2 * s : ℝ)) +
          (N : ℝ) / M + M := h67
    _ ≤ (N : ℝ) ^ (1 - 1 / (2 * s : ℝ)) / M *
            (D * W * ((2 : ℝ) ^ (4 * s) * J)) ^
              (1 / (2 * s : ℝ)) +
          (N : ℝ) / M + M := by
      gcongr
    _ = 4 * ((N : ℝ) ^ (1 - 1 / (2 * s : ℝ)) / M) *
          (D * W * J) ^ (1 / (2 * s : ℝ)) +
          (N : ℝ) / M + M := by
      rw [hfour]
      ring
    _ = _ := by
      dsimp [D, W, J]

#print axioms fordLemma63_native

end

end GafniTao
