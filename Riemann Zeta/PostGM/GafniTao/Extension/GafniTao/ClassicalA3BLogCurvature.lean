import GafniTao.ClassicalA3BReciprocal

/-!
# Curvature after three logarithmic `A`-process shifts

The phase below is the third forward difference of `-t log (A+x)`.
Its second finite difference has positive size comparable with
`t*r*s*q/A^5`; these are the hypotheses needed by the final `B` process.
-/

open Set

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

noncomputable def logarithmicThirdDifferencePhase
    (t A : ℝ) (r s q : ℕ) (x : ℝ) : ℝ :=
  logarithmicSecondDifferencePhase t A r s x -
    logarithmicSecondDifferencePhase t A r s (x + q)

def reciprocalSquareSecondGap (r s u : ℝ) : ℝ :=
  reciprocalSquareGap r u - reciprocalSquareGap r (u + s)

theorem hasDerivAt_reciprocalSquareSecondGap
    {r s u : ℝ} (hu : u ≠ 0) (hur : u + r ≠ 0)
    (hus : u + s ≠ 0) (husr : u + s + r ≠ 0) :
    HasDerivAt (reciprocalSquareSecondGap r s)
      (-2 * (reciprocalCubeGap r u - reciprocalCubeGap r (u + s))) u := by
  have hleft := hasDerivAt_reciprocalSquareGap hu hur
  have hrightAt := hasDerivAt_reciprocalSquareGap hus husr
  have hright := hrightAt.comp u ((hasDerivAt_id u).add_const s)
  convert hleft.sub hright using 1
  unfold reciprocalCubeGap
  ring

theorem reciprocalSquareSecondGap_difference_bounds
    {A u r s q : ℝ} (hA : 0 < A) (hr : 0 < r) (hs : 0 < s)
    (hq : 0 < q) (huLow : A ≤ u)
    (hursqHigh : u + r + s + q ≤ 2 * A) :
    r * s * q / (16 * A ^ 5) ≤
        reciprocalSquareSecondGap r s u -
          reciprocalSquareSecondGap r s (u + q) ∧
      reciprocalSquareSecondGap r s u -
          reciprocalSquareSecondGap r s (u + q) ≤
        192 * r * s * q / A ^ 5 := by
  have hu : 0 < u := hA.trans_le huLow
  have huq : 0 < u + q := by linarith
  have hcont : ContinuousOn (reciprocalSquareSecondGap r s)
      (Icc u (u + q)) := by
    intro x hx
    exact (hasDerivAt_reciprocalSquareSecondGap
      (ne_of_gt (hu.trans_le hx.1))
      (ne_of_gt (by linarith [hx.1]))
      (ne_of_gt (by linarith [hx.1]))
      (ne_of_gt (by linarith [hx.1]))).continuousAt.continuousWithinAt
  have hderiv : ∀ x ∈ Ioo u (u + q),
      HasDerivAt (reciprocalSquareSecondGap r s)
        (-2 * (reciprocalCubeGap r x - reciprocalCubeGap r (x + s))) x := by
    intro x hx
    exact hasDerivAt_reciprocalSquareSecondGap
      (ne_of_gt (hu.trans hx.1))
      (ne_of_gt (by linarith [hx.1]))
      (ne_of_gt (by linarith [hx.1]))
      (ne_of_gt (by linarith [hx.1]))
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope
    (reciprocalSquareSecondGap r s)
    (fun x : ℝ =>
      -2 * (reciprocalCubeGap r x - reciprocalCubeGap r (x + s)))
    (by linarith) hcont hderiv
  have hcLow : A ≤ c := huLow.trans hc.1.le
  have hcrsHigh : c + r + s ≤ 2 * A := by
    linarith [hc.2, hursqHigh]
  have hcube := reciprocalCubeGap_difference_bounds hA hr hs hcLow hcrsHigh
  have hlength : u + q - u = q := by ring
  rw [hlength] at hslope
  have hslopeMul := (eq_div_iff hq.ne').mp hslope
  have heq : reciprocalSquareSecondGap r s u -
      reciprocalSquareSecondGap r s (u + q) =
        2 * (reciprocalCubeGap r c - reciprocalCubeGap r (c + s)) * q := by
    calc
      reciprocalSquareSecondGap r s u -
          reciprocalSquareSecondGap r s (u + q) =
        -(reciprocalSquareSecondGap r s (u + q) -
          reciprocalSquareSecondGap r s u) := by ring
      _ = -(-2 * (reciprocalCubeGap r c - reciprocalCubeGap r (c + s)) * q) := by
        rw [hslopeMul]
      _ = 2 * (reciprocalCubeGap r c - reciprocalCubeGap r (c + s)) * q := by ring
  rw [heq]
  constructor
  · have hmul := mul_le_mul_of_nonneg_right hcube.1 hq.le
    have hdouble := mul_le_mul_of_nonneg_left hmul (by norm_num : (0 : ℝ) ≤ 2)
    calc
      r * s * q / (16 * A ^ 5) =
          2 * (r * s / (32 * A ^ 5) * q) := by
        field_simp [hA.ne']
        ring
      _ ≤ 2 *
          ((reciprocalCubeGap r c - reciprocalCubeGap r (c + s)) * q) :=
        hdouble
      _ = 2 *
          (reciprocalCubeGap r c - reciprocalCubeGap r (c + s)) * q := by ring
  · have hmul := mul_le_mul_of_nonneg_right hcube.2 hq.le
    have hdouble := mul_le_mul_of_nonneg_left hmul (by norm_num : (0 : ℝ) ≤ 2)
    calc
      2 * (reciprocalCubeGap r c - reciprocalCubeGap r (c + s)) * q =
          2 * ((reciprocalCubeGap r c - reciprocalCubeGap r (c + s)) * q) := by ring
      _ ≤ 2 * (96 * r * s / A ^ 5 * q) := hdouble
      _ = 192 * r * s * q / A ^ 5 := by
        field_simp [hA.ne']
        ring

theorem hasDerivAt_logarithmicThirdDifferencePhase
    (t A : ℝ) (r s q : ℕ) {x : ℝ}
    (hx : A + x ≠ 0) (hxr : A + x + r ≠ 0)
    (hxs : A + x + s ≠ 0) (hxsr : A + x + s + r ≠ 0)
    (hxq : A + x + q ≠ 0) (hxqr : A + x + q + r ≠ 0)
    (hxqs : A + x + q + s ≠ 0)
    (hxqsr : A + x + q + s + r ≠ 0) :
    HasDerivAt (logarithmicThirdDifferencePhase t A r s q)
      (((-t / (A + x) + t / (A + x + r)) -
          (-t / (A + x + s) + t / (A + x + s + r))) -
        ((-t / (A + x + q) + t / (A + x + q + r)) -
          (-t / (A + x + q + s) + t / (A + x + q + s + r)))) x := by
  unfold logarithmicThirdDifferencePhase
  have hleft := hasDerivAt_logarithmicSecondDifferencePhase t A r s
    hx hxr (by simpa [add_assoc] using hxs) (by simpa [add_assoc] using hxsr)
  have hrightAt := hasDerivAt_logarithmicSecondDifferencePhase t A r s
    (x := x + q)
    (by simpa [add_assoc] using hxq)
    (by simpa [add_assoc] using hxqr)
    (by simpa [add_assoc] using hxqs)
    (by simpa [add_assoc] using hxqsr)
  have hright := hrightAt.comp x ((hasDerivAt_id x).add_const (q : ℝ))
  convert hleft.sub hright using 1
  all_goals ring_nf

theorem hasDerivAt_logarithmicThirdDifferencePhase_deriv
    (t A : ℝ) (r s q : ℕ) {x : ℝ}
    (hx : A + x ≠ 0) (hxr : A + x + r ≠ 0)
    (hxs : A + x + s ≠ 0) (hxsr : A + x + s + r ≠ 0)
    (hxq : A + x + q ≠ 0) (hxqr : A + x + q + r ≠ 0)
    (hxqs : A + x + q + s ≠ 0)
    (hxqsr : A + x + q + s + r ≠ 0) :
    HasDerivAt
      (fun y : ℝ =>
        ((-t / (A + y) + t / (A + y + r)) -
          (-t / (A + y + s) + t / (A + y + s + r))) -
        ((-t / (A + y + q) + t / (A + y + q + r)) -
          (-t / (A + y + q + s) + t / (A + y + q + s + r))))
      (t * (reciprocalSquareSecondGap (r : ℝ) (s : ℝ) (A + x) -
        reciprocalSquareSecondGap (r : ℝ) (s : ℝ) (A + x + q))) x := by
  have hleft := hasDerivAt_logarithmicSecondDifferencePhase_deriv t A r s
    hx hxr (by simpa [add_assoc] using hxs) (by simpa [add_assoc] using hxsr)
  have hrightAt := hasDerivAt_logarithmicSecondDifferencePhase_deriv t A r s
    (x := x + q)
    (by simpa [add_assoc] using hxq)
    (by simpa [add_assoc] using hxqr)
    (by simpa [add_assoc] using hxqs)
    (by simpa [add_assoc] using hxqsr)
  have hright := hrightAt.comp x ((hasDerivAt_id x).add_const (q : ℝ))
  convert hleft.sub hright using 1
  · ext y
    simp only [Pi.sub_apply, Function.comp_apply, id_eq]
    ring
  · unfold reciprocalSquareSecondGap
    ring

theorem logarithmicThirdDifferencePhase_secondDifference
    (t A : ℝ) (r s q n : ℕ) (hA : 0 < A) :
    ∃ xi, xi ∈ Ioo (n : ℝ) (n + 2) ∧
      t * (reciprocalSquareSecondGap (r : ℝ) (s : ℝ) (A + xi) -
        reciprocalSquareSecondGap (r : ℝ) (s : ℝ) (A + xi + q)) =
        (logarithmicThirdDifferencePhase t A r s q (n + 2) -
          logarithmicThirdDifferencePhase t A r s q (n + 1)) -
        (logarithmicThirdDifferencePhase t A r s q (n + 1) -
          logarithmicThirdDifferencePhase t A r s q n) := by
  let F : ℝ → ℝ := logarithmicThirdDifferencePhase t A r s q
  let F' : ℝ → ℝ := fun x =>
    ((-t / (A + x) + t / (A + x + r)) -
      (-t / (A + x + s) + t / (A + x + s + r))) -
    ((-t / (A + x + q) + t / (A + x + q + r)) -
      (-t / (A + x + q + s) + t / (A + x + q + s + r)))
  let F'' : ℝ → ℝ := fun x =>
    t * (reciprocalSquareSecondGap (r : ℝ) (s : ℝ) (A + x) -
      reciprocalSquareSecondGap (r : ℝ) (s : ℝ) (A + x + q))
  have hmv := second_order_mean_value F F' F'' n
    (fun x hx => by
      dsimp only [F, F']
      have hx0 : 0 ≤ x := (Nat.cast_nonneg n).trans hx.1
      exact hasDerivAt_logarithmicThirdDifferencePhase t A r s q
        (ne_of_gt (by positivity)) (ne_of_gt (by positivity))
        (ne_of_gt (by positivity)) (ne_of_gt (by positivity))
        (ne_of_gt (by positivity)) (ne_of_gt (by positivity))
        (ne_of_gt (by positivity)) (ne_of_gt (by positivity)))
    (fun x hx => by
      dsimp only [F', F'']
      have hx0 : 0 ≤ x := (Nat.cast_nonneg n).trans hx.1
      exact hasDerivAt_logarithmicThirdDifferencePhase_deriv t A r s q
        (ne_of_gt (by positivity)) (ne_of_gt (by positivity))
        (ne_of_gt (by positivity)) (ne_of_gt (by positivity))
        (ne_of_gt (by positivity)) (ne_of_gt (by positivity))
        (ne_of_gt (by positivity)) (ne_of_gt (by positivity)))
  obtain ⟨xi, hxi, heq⟩ := hmv
  refine ⟨xi, hxi, ?_⟩
  dsimp only [F, F''] at heq
  push_cast at heq ⊢
  convert heq using 1
  · ring

theorem logarithmicThirdDifference_secondDifference_bounds
    (t A : ℝ) (r s q N : ℕ) (ht : 0 < t) (hA : 0 < A)
    (hr : 0 < r) (hs : 0 < s) (hq : 0 < q)
    (hsize : ((N + 1 + r + s + q : ℕ) : ℝ) ≤ A) :
    ∀ n, n < N →
      t * r * s * q / (16 * A ^ 5) ≤
        (logarithmicThirdDifferencePhase t A r s q (n + 2) -
          logarithmicThirdDifferencePhase t A r s q (n + 1)) -
          (logarithmicThirdDifferencePhase t A r s q (n + 1) -
            logarithmicThirdDifferencePhase t A r s q n) ∧
      (logarithmicThirdDifferencePhase t A r s q (n + 2) -
          logarithmicThirdDifferencePhase t A r s q (n + 1)) -
          (logarithmicThirdDifferencePhase t A r s q (n + 1) -
            logarithmicThirdDifferencePhase t A r s q n) ≤
        192 * t * r * s * q / A ^ 5 := by
  intro n hn
  obtain ⟨xi, hxi, heq⟩ :=
    logarithmicThirdDifferencePhase_secondDifference t A r s q n hA
  have hxi0 : 0 ≤ xi := (Nat.cast_nonneg n).trans hxi.1.le
  have huLow : A ≤ A + xi := by linarith
  have hnat : n + 2 + r + s + q ≤ N + 1 + r + s + q := by omega
  have hcast : (n : ℝ) + 2 + r + s + q ≤ A := by
    have := (Nat.cast_le.mpr hnat).trans hsize
    norm_num at this ⊢
    exact this
  have hursq : A + xi + r + s + q ≤ 2 * A := by linarith [hxi.2]
  have hgap := reciprocalSquareSecondGap_difference_bounds hA
    (by exact_mod_cast hr) (by exact_mod_cast hs) (by exact_mod_cast hq)
    huLow hursq
  constructor
  · calc
      t * (r : ℝ) * s * q / (16 * A ^ 5) =
          t * ((r : ℝ) * s * q / (16 * A ^ 5)) := by ring
      _ ≤ t * (reciprocalSquareSecondGap (r : ℝ) (s : ℝ) (A + xi) -
          reciprocalSquareSecondGap (r : ℝ) (s : ℝ) (A + xi + q)) :=
        mul_le_mul_of_nonneg_left hgap.1 ht.le
      _ = (logarithmicThirdDifferencePhase t A r s q (n + 2) -
          logarithmicThirdDifferencePhase t A r s q (n + 1)) -
          (logarithmicThirdDifferencePhase t A r s q (n + 1) -
            logarithmicThirdDifferencePhase t A r s q n) := heq
  · calc
      (logarithmicThirdDifferencePhase t A r s q (n + 2) -
          logarithmicThirdDifferencePhase t A r s q (n + 1)) -
          (logarithmicThirdDifferencePhase t A r s q (n + 1) -
            logarithmicThirdDifferencePhase t A r s q n) =
        t * (reciprocalSquareSecondGap (r : ℝ) (s : ℝ) (A + xi) -
          reciprocalSquareSecondGap (r : ℝ) (s : ℝ) (A + xi + q)) := heq.symm
      _ ≤ t * (192 * (r : ℝ) * s * q / A ^ 5) :=
        mul_le_mul_of_nonneg_left hgap.2 ht.le
      _ = 192 * t * (r : ℝ) * s * q / A ^ 5 := by ring

#print axioms reciprocalSquareSecondGap_difference_bounds
#print axioms logarithmicThirdDifference_secondDifference_bounds

end

end GafniTao
