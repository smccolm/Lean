import GafniTao.FordLemma63RealMoment

/-!
# Ford Lemma 6.3 with its literal real cutoff

This assembles the real-cutoff equations (6.7) and (6.9).  The resulting
public theorem now matches the source convention: `P` is real, the finite
polynomial sum and Vinogradov moment end at `floor P`, and every displayed
scale factor is the real `P`.
-/

open Finset Set
open scoped BigOperators

namespace GafniTao

noncomputable section

theorem fordLemma63_real_cutoff
    {s k N R : ℕ} {P u t : ℝ}
    (hs : 1 ≤ s) (hk : 2 ≤ k) (hP : 1 ≤ P) (hPN : P ≤ N)
    (hN : 1 ≤ N) (hRlower : N < R) (hR : R ≤ 2 * N)
    (hu0 : 0 < u) (hu1 : u ≤ 1) (ht : 0 < t)
    (htN : t ≤ (N : ℝ) ^ k)
    (hscale : t * P ^ (k + 1) ≤ (N : ℝ) ^ (k + 1)) :
    ‖fordShiftedExponentialSum N R u t‖ ≤
      4 * ((N : ℝ) ^ (1 - 1 / (2 * s : ℝ)) / P) *
        ((Real.pi ^ k * (k.factorial : ℝ) * (k : ℝ) ^ k *
              P ^ fordVinogradovKappa k) *
            fordLemma63WReal N k P t *
            (fordVinogradovMoment s k P : ℝ)) ^
              (1 / (2 * s : ℝ)) +
        (N : ℝ) / P + P := by
  let D : ℝ := Real.pi ^ k * (k.factorial : ℝ) * (k : ℝ) ^ k *
    P ^ fordVinogradovKappa k
  let W : ℝ := fordLemma63WReal N k P t
  let J : ℝ := fordVinogradovMoment s k P
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hW : 0 ≤ W := by dsimp [W]; unfold fordLemma63WReal; positivity
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have hrs : (0 : ℝ) < 2 * s := by
    have : (0 : ℝ) < s := by exact_mod_cast (Nat.zero_lt_of_lt hs)
    positivity
  have hq : 0 ≤ (1 / (2 * s : ℝ)) := by positivity
  have h67 := ford_equation_6_7_real_cutoff
    (P := P) (N := N) (R := R) (s := s) (u := u) (t := t)
    hP hN hs hRlower hR hu0
  have h69 := ford_equation_6_9_real_cutoff
    (s := s) (k := k) (N := N) (P := P) (u := u) (t := t)
    hs hk hP hPN hN hu0 hu1 ht htN hscale
  have hmoment : fordLemma63Moment ⌊P⌋₊ N u t s ≤
      D * W * ((2 : ℝ) ^ (4 * s) * J) := by
    simpa only [D, W, J, mul_assoc] using h69
  have hroot :
      (fordLemma63Moment ⌊P⌋₊ N u t s) ^ (1 / (2 * s : ℝ)) ≤
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
        (N : ℝ) ^ (1 - 1 / (2 * s : ℝ)) / P *
            (fordLemma63Moment ⌊P⌋₊ N u t s) ^ (1 / (2 * s : ℝ)) +
          (N : ℝ) / P + P := h67
    _ ≤ (N : ℝ) ^ (1 - 1 / (2 * s : ℝ)) / P *
            (D * W * ((2 : ℝ) ^ (4 * s) * J)) ^
              (1 / (2 * s : ℝ)) +
          (N : ℝ) / P + P := by gcongr
    _ = 4 * ((N : ℝ) ^ (1 - 1 / (2 * s : ℝ)) / P) *
          (D * W * J) ^ (1 / (2 * s : ℝ)) +
          (N : ℝ) / P + P := by
      rw [hfour]
      ring
    _ = _ := by dsimp [D, W, J]

#print axioms fordLemma63_real_cutoff

end

end GafniTao
