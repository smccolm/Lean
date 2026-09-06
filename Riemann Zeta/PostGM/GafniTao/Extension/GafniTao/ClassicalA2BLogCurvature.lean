import GafniTao.ClassicalA2BReciprocal
import RiemannZeta.GuthMaynard.Weyl

/-!
# Curvature after two logarithmic `A`-process shifts

This is the analytic input to the inner `B` process in the classical
`A²B(0,1)` construction.  Both shift distances remain explicit.  The
fourth power of the physical block scale is not replaced by an asymptotic
surrogate.
-/

open Set

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

noncomputable def logarithmicSecondDifferencePhase
    (t A : ℝ) (r s : ℕ) (x : ℝ) : ℝ :=
  logarithmicDifferencePhase t A 0 r x -
    logarithmicDifferencePhase t A 0 r (x + s)

theorem hasDerivAt_logarithmicSecondDifferencePhase
    (t A : ℝ) (r s : ℕ) {x : ℝ}
    (hx : A + x ≠ 0) (hxr : A + x + r ≠ 0)
    (hxs : A + (x + s) ≠ 0) (hxsr : A + (x + s) + r ≠ 0) :
    HasDerivAt (logarithmicSecondDifferencePhase t A r s)
      ((-t / (A + x) + t / (A + x + r)) -
        (-t / (A + x + s) + t / (A + x + s + r))) x := by
  unfold logarithmicSecondDifferencePhase
  have hleft := hasDerivAt_logarithmicDifferencePhase t A 0 r
    (by simpa using hx) hxr
  have hrightAt :=
    hasDerivAt_logarithmicDifferencePhase t A 0 r
      (by simpa [add_assoc] using hxs) (by simpa [add_assoc] using hxsr)
  have hright := hrightAt.comp x ((hasDerivAt_id x).add_const (s : ℝ))
  convert hleft.sub hright using 1
  all_goals push_cast
  all_goals ring_nf

theorem hasDerivAt_logarithmicSecondDifferencePhase_deriv
    (t A : ℝ) (r s : ℕ) {x : ℝ}
    (hx : A + x ≠ 0) (hxr : A + x + r ≠ 0)
    (hxs : A + x + s ≠ 0) (hxsr : A + x + s + r ≠ 0) :
    HasDerivAt
      (fun y : ℝ =>
        (-t / (A + y) + t / (A + y + r)) -
          (-t / (A + y + s) + t / (A + y + s + r)))
      (t * (reciprocalSquareGap (r : ℝ) (A + x) -
        reciprocalSquareGap (r : ℝ) (A + x + s))) x := by
  have hleft :=
    hasDerivAt_logarithmicDifferencePhase_deriv t A 0 r
      (by simpa using hx) hxr
  have hrightAt := hasDerivAt_logarithmicDifferencePhase_deriv
    t A 0 r (by simpa [add_assoc] using hxs)
      (by simpa [add_assoc] using hxsr)
  have hright := hrightAt.comp x ((hasDerivAt_id x).add_const (s : ℝ))
  convert hleft.sub hright using 1
  · ext y
    simp only [Pi.sub_apply, Function.comp_apply, Nat.cast_zero, add_zero, id_eq]
    ring
  · simp only [reciprocalSquareGap, Nat.cast_zero, add_zero]
    ring

theorem reciprocalSquareGap_difference_bounds
    {A u r s : ℝ} (hA : 0 < A) (hr : 0 < r) (hs : 0 < s)
    (huLow : A ≤ u) (hursHigh : u + r + s ≤ 2 * A) :
    r * s / (16 * A ^ 4) ≤
        reciprocalSquareGap r u - reciprocalSquareGap r (u + s) ∧
      reciprocalSquareGap r u - reciprocalSquareGap r (u + s) ≤
        32 * r * s / A ^ 4 := by
  have hu : 0 < u := hA.trans_le huLow
  have hus : 0 < u + s := by linarith
  have hur : 0 < u + r := by linarith
  have hurs : 0 < u + s + r := by linarith
  have hcont : ContinuousOn (reciprocalSquareGap r) (Icc u (u + s)) := by
    intro x hx
    exact (hasDerivAt_reciprocalSquareGap
      (ne_of_gt (hu.trans_le hx.1))
      (ne_of_gt (by linarith [hx.1]))).continuousAt.continuousWithinAt
  have hderiv : ∀ x ∈ Ioo u (u + s),
      HasDerivAt (reciprocalSquareGap r)
        (-2 / x ^ 3 + 2 / (x + r) ^ 3) x := by
    intro x hx
    exact hasDerivAt_reciprocalSquareGap
      (ne_of_gt (hu.trans hx.1)) (ne_of_gt (by linarith [hx.1]))
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope
    (reciprocalSquareGap r)
    (fun x : ℝ => -2 / x ^ 3 + 2 / (x + r) ^ 3)
    (by linarith) hcont hderiv
  have hcLow : A ≤ c := huLow.trans hc.1.le
  have hcrHigh : c + r ≤ 2 * A := by linarith [hc.2, hursHigh]
  have hderivBounds :=
    reciprocalSquareGap_neg_deriv_bounds hA hr hcLow hcrHigh
  have hlength : u + s - u = s := by ring
  rw [hlength] at hslope
  have heq : reciprocalSquareGap r u - reciprocalSquareGap r (u + s) =
      -(-2 / c ^ 3 + 2 / (c + r) ^ 3) * s := by
    rw [hslope]
    field_simp [hs.ne']
    ring
  rw [heq]
  constructor
  · have hmul := mul_le_mul_of_nonneg_right hderivBounds.1 hs.le
    convert hmul using 1
    all_goals ring_nf
  · have hmul := mul_le_mul_of_nonneg_right hderivBounds.2 hs.le
    convert hmul using 1
    all_goals ring_nf

theorem logarithmicSecondDifferencePhase_secondDifference
    (t A : ℝ) (r s n : ℕ) (hA : 0 < A) :
    ∃ xi, xi ∈ Ioo (n : ℝ) (n + 2) ∧
      t * (reciprocalSquareGap (r : ℝ) (A + xi) -
        reciprocalSquareGap (r : ℝ) (A + xi + s)) =
        (logarithmicSecondDifferencePhase t A r s (n + 2) -
          logarithmicSecondDifferencePhase t A r s (n + 1)) -
        (logarithmicSecondDifferencePhase t A r s (n + 1) -
          logarithmicSecondDifferencePhase t A r s n) := by
  let F : ℝ → ℝ := logarithmicSecondDifferencePhase t A r s
  let F' : ℝ → ℝ := fun x =>
    ((-t / (A + x) + t / (A + x + r)) -
      (-t / (A + x + s) + t / (A + x + s + r)))
  let F'' : ℝ → ℝ := fun x =>
    t * (reciprocalSquareGap (r : ℝ) (A + x) -
      reciprocalSquareGap (r : ℝ) (A + x + s))
  have hmv := second_order_mean_value F F' F'' n
    (fun x hx => by
      dsimp only [F, F']
      have hx0 : 0 ≤ x := (Nat.cast_nonneg n).trans hx.1
      exact hasDerivAt_logarithmicSecondDifferencePhase t A r s
        (ne_of_gt (by positivity)) (ne_of_gt (by positivity))
        (ne_of_gt (by positivity)) (ne_of_gt (by positivity)))
    (fun x hx => by
      dsimp only [F', F'']
      have hx0 : 0 ≤ x := (Nat.cast_nonneg n).trans hx.1
      exact hasDerivAt_logarithmicSecondDifferencePhase_deriv t A r s
        (ne_of_gt (by positivity)) (ne_of_gt (by positivity))
        (ne_of_gt (by positivity)) (ne_of_gt (by positivity)))
  obtain ⟨xi, hxi, heq⟩ := hmv
  refine ⟨xi, hxi, ?_⟩
  dsimp only [F, F''] at heq
  push_cast at heq ⊢
  convert heq using 1
  ring

theorem logarithmicSecondDifference_secondDifference_bounds
    (t A : ℝ) (r s N : ℕ) (ht : 0 < t) (hA : 0 < A)
    (hr : 0 < r) (hs : 0 < s)
    (hsize : ((N + 1 + r + s : ℕ) : ℝ) ≤ A) :
    ∀ n, n < N →
      t * r * s / (16 * A ^ 4) ≤
        (logarithmicSecondDifferencePhase t A r s (n + 2) -
          logarithmicSecondDifferencePhase t A r s (n + 1)) -
          (logarithmicSecondDifferencePhase t A r s (n + 1) -
            logarithmicSecondDifferencePhase t A r s n) ∧
      (logarithmicSecondDifferencePhase t A r s (n + 2) -
          logarithmicSecondDifferencePhase t A r s (n + 1)) -
          (logarithmicSecondDifferencePhase t A r s (n + 1) -
            logarithmicSecondDifferencePhase t A r s n) ≤
        32 * t * r * s / A ^ 4 := by
  intro n hn
  obtain ⟨xi, hxi, heq⟩ :=
    logarithmicSecondDifferencePhase_secondDifference t A r s n hA
  have hxi0 : 0 ≤ xi := (Nat.cast_nonneg n).trans hxi.1.le
  have huLow : A ≤ A + xi := by linarith
  have hnat : n + 2 + r + s ≤ N + 1 + r + s := by omega
  have hcast : (n : ℝ) + 2 + r + s ≤ A := by
    have := (Nat.cast_le.mpr hnat).trans hsize
    norm_num at this ⊢
    exact this
  have hurs : A + xi + r + s ≤ 2 * A := by linarith [hxi.2]
  have hgap := reciprocalSquareGap_difference_bounds hA
    (by exact_mod_cast hr) (by exact_mod_cast hs) huLow hurs
  have hmul := And.intro
    (mul_le_mul_of_nonneg_left hgap.1 ht.le)
    (mul_le_mul_of_nonneg_left hgap.2 ht.le)
  rw [heq] at hmul
  norm_num at hmul ⊢
  convert hmul using 1
  all_goals ring_nf

#print axioms reciprocalSquareGap_difference_bounds
#print axioms logarithmicSecondDifference_secondDifference_bounds

end

end GafniTao
