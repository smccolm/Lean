import GafniTao.HeathBrownAtkinsonBProcess
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# First-derivative bounds for differences of Atkinson phases

This file supplies the first-derivative alternative used together with the
`(1/2,1/2)` B-process in Ivić (7.19).  The bounds retain literal radical
scales on a dyadic index box; no exponent-pair estimate is postulated.
-/

open Set

namespace GafniTao

noncomputable section

/-- Lower first-derivative scale for two heights separated by `t-u` and
indices in `[A,B]`. -/
def heathBrownAtkinsonFirstDerivativeLower
    (u t A B : ℝ) : ℝ :=
  Real.pi * (t - u) /
    (B * heathBrownAtkinsonSlopeUpper u A)

/-- Upper first-derivative scale on the same box. -/
def heathBrownAtkinsonFirstDerivativeUpper
    (u t A B : ℝ) : ℝ :=
  Real.pi * (t - u) /
    (A * heathBrownAtkinsonSlopeLower u B)

/-- Rationalization of the exact square-root slope difference. -/
theorem heathBrownAtkinsonRealSlope_sub_eq
    {t u x : ℝ} (ht : 0 < t) (hu : 0 < u) (hx : 0 < x) :
    heathBrownAtkinsonRealSlope t x -
        heathBrownAtkinsonRealSlope u x =
      (2 * Real.pi * (t - u) / x) /
        (heathBrownAtkinsonRealSlope t x +
          heathBrownAtkinsonRealSlope u x) := by
  have hst := heathBrownAtkinsonRealSlope_pos ht hx
  have hsu := heathBrownAtkinsonRealSlope_pos hu hx
  have hden : heathBrownAtkinsonRealSlope t x +
      heathBrownAtkinsonRealSlope u x ≠ 0 := by positivity
  have htsq : (heathBrownAtkinsonRealSlope t x) ^ (2 : ℕ) =
      2 * Real.pi * t / x + Real.pi ^ (2 : ℕ) := by
    unfold heathBrownAtkinsonRealSlope
    rw [Real.sq_sqrt]
    positivity
  have husq : (heathBrownAtkinsonRealSlope u x) ^ (2 : ℕ) =
      2 * Real.pi * u / x + Real.pi ^ (2 : ℕ) := by
    unfold heathBrownAtkinsonRealSlope
    rw [Real.sq_sqrt]
    positivity
  apply (eq_div_iff hden).2
  calc
    (heathBrownAtkinsonRealSlope t x -
          heathBrownAtkinsonRealSlope u x) *
        (heathBrownAtkinsonRealSlope t x +
          heathBrownAtkinsonRealSlope u x) =
        (heathBrownAtkinsonRealSlope t x) ^ (2 : ℕ) -
          (heathBrownAtkinsonRealSlope u x) ^ (2 : ℕ) := by ring
    _ = 2 * Real.pi * (t - u) / x := by rw [htsq, husq]; ring

/-- Pointwise first-derivative bounds on a dyadic height/index box. -/
theorem heathBrownAtkinsonRealSlopeDifference_box_bounds
    {t u A x B : ℝ}
    (hu : 0 < u) (htu : u < t) (hA : 0 < A)
    (hAx : A ≤ x) (hxB : x ≤ B) (hBu : B ≤ u)
    (htUpper : t ≤ 2 * u) :
    heathBrownAtkinsonFirstDerivativeLower u t A B ≤
        heathBrownAtkinsonRealSlope t x -
          heathBrownAtkinsonRealSlope u x ∧
      heathBrownAtkinsonRealSlope t x -
          heathBrownAtkinsonRealSlope u x ≤
        heathBrownAtkinsonFirstDerivativeUpper u t A B := by
  have hx : 0 < x := hA.trans_le hAx
  have hB : 0 < B := hx.trans_le hxB
  have ht : 0 < t := hu.trans htu
  have hgap : 0 < t - u := sub_pos.mpr htu
  have hstPos := heathBrownAtkinsonRealSlope_pos ht hx
  have hsuPos := heathBrownAtkinsonRealSlope_pos hu hx
  have hupperApos := heathBrownAtkinsonSlopeUpper_pos hu hA
  have hlowerBpos := heathBrownAtkinsonSlopeLower_pos hu hB
  have hupperX := heathBrownAtkinsonSlopeUpper_anti hu hA hAx
  have hstUpper := heathBrownAtkinsonSlope_le_upper
    (u := u) (c := t) hu hx (hxB.trans hBu) htUpper
  have huu : u ≤ 2 * u := by linarith
  have hsuUpper := heathBrownAtkinsonSlope_le_upper
    (u := u) (c := u) hu hx (hxB.trans hBu) huu
  have hlowerX := heathBrownAtkinsonSlopeLower_anti hu hx hxB
  have hstLower := heathBrownAtkinsonSlopeLower_le
    (u := u) (c := t) hx htu.le
  have hsuLower := heathBrownAtkinsonSlopeLower_le
    (u := u) (c := u) hx le_rfl
  have hdenUpper :
      x * (heathBrownAtkinsonRealSlope t x +
        heathBrownAtkinsonRealSlope u x) ≤
      B * (2 * heathBrownAtkinsonSlopeUpper u A) := by
    have hsum : heathBrownAtkinsonRealSlope t x +
        heathBrownAtkinsonRealSlope u x ≤
        2 * heathBrownAtkinsonSlopeUpper u A := by
      linarith [hstUpper.trans hupperX, hsuUpper.trans hupperX]
    exact mul_le_mul hxB hsum (add_nonneg hstPos.le hsuPos.le) hB.le
  have hdenLower :
      A * (2 * heathBrownAtkinsonSlopeLower u B) ≤
      x * (heathBrownAtkinsonRealSlope t x +
        heathBrownAtkinsonRealSlope u x) := by
    have hsum : 2 * heathBrownAtkinsonSlopeLower u B ≤
        heathBrownAtkinsonRealSlope t x +
          heathBrownAtkinsonRealSlope u x := by
      linarith [hlowerX.trans hstLower, hlowerX.trans hsuLower]
    exact mul_le_mul hAx hsum (mul_nonneg (by norm_num) hlowerBpos.le) hx.le
  have hnum : 0 ≤ 2 * Real.pi * (t - u) := by positivity
  have hdenUpperPos : 0 < B *
      (2 * heathBrownAtkinsonSlopeUpper u A) :=
    mul_pos hB (mul_pos (by norm_num) hupperApos)
  have hdenLowerPos : 0 < A *
      (2 * heathBrownAtkinsonSlopeLower u B) :=
    mul_pos hA (mul_pos (by norm_num) hlowerBpos)
  have hdenActualPos : 0 < x *
      (heathBrownAtkinsonRealSlope t x +
        heathBrownAtkinsonRealSlope u x) :=
    mul_pos hx (add_pos hstPos hsuPos)
  have hsumPos : 0 < heathBrownAtkinsonRealSlope t x +
      heathBrownAtkinsonRealSlope u x := add_pos hstPos hsuPos
  rw [heathBrownAtkinsonRealSlope_sub_eq ht hu hx]
  constructor
  · unfold heathBrownAtkinsonFirstDerivativeLower
    have hdiv := div_le_div_of_nonneg_left hnum hdenActualPos hdenUpper
    calc
      Real.pi * (t - u) /
          (B * heathBrownAtkinsonSlopeUpper u A) =
          (2 * Real.pi * (t - u)) /
            (B * (2 * heathBrownAtkinsonSlopeUpper u A)) := by ring
      _ ≤ (2 * Real.pi * (t - u)) /
          (x * (heathBrownAtkinsonRealSlope t x +
            heathBrownAtkinsonRealSlope u x)) := hdiv
      _ = (2 * Real.pi * (t - u) / x) /
          (heathBrownAtkinsonRealSlope t x +
            heathBrownAtkinsonRealSlope u x) := by
        field_simp [hx.ne', hsumPos.ne']
  · unfold heathBrownAtkinsonFirstDerivativeUpper
    have hdiv := div_le_div_of_nonneg_left hnum hdenLowerPos hdenLower
    calc
      (2 * Real.pi * (t - u) / x) /
          (heathBrownAtkinsonRealSlope t x +
            heathBrownAtkinsonRealSlope u x) =
          (2 * Real.pi * (t - u)) /
            (x * (heathBrownAtkinsonRealSlope t x +
              heathBrownAtkinsonRealSlope u x)) := by
        field_simp [hx.ne', hsumPos.ne']
      _ ≤ (2 * Real.pi * (t - u)) /
          (A * (2 * heathBrownAtkinsonSlopeLower u B)) := hdiv
      _ = Real.pi * (t - u) /
          (A * heathBrownAtkinsonSlopeLower u B) := by ring

/-- The positively sloped orientation of the natural-index phase
difference. -/
def heathBrownAtkinsonIncreasingDifferenceNat
    (t u : ℝ) (K n : ℕ) : ℝ :=
  heathBrownAtkinsonPhase t (K + n) -
    heathBrownAtkinsonPhase u (K + n)

/-- A unit increment of the exact phase difference equals its derivative at
an intermediate real index. -/
theorem exists_heathBrownAtkinsonIncreasingDifferenceNat_increment
    {t u : ℝ} {K n : ℕ}
    (hu : 0 < u) (htu : u < t) (hK : 0 < K) :
    ∃ xi ∈ Set.Ioo ((K + n : ℕ) : ℝ) ((K + n + 1 : ℕ) : ℝ),
      heathBrownAtkinsonRealSlope t xi -
          heathBrownAtkinsonRealSlope u xi =
        heathBrownAtkinsonIncreasingDifferenceNat t u K (n + 1) -
          heathBrownAtkinsonIncreasingDifferenceNat t u K n := by
  let F : ℝ → ℝ := heathBrownAtkinsonPhaseDifference t u
  let F' : ℝ → ℝ := fun x =>
    heathBrownAtkinsonRealSlope t x - heathBrownAtkinsonRealSlope u x
  have hleft : 0 < ((K + n : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < K + n by omega)
  have hlt : ((K + n : ℕ) : ℝ) < ((K + n + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show K + n < K + n + 1 by omega)
  have hcont : ContinuousOn F
      (Set.Icc ((K + n : ℕ) : ℝ) ((K + n + 1 : ℕ) : ℝ)) := by
    intro x hx
    exact (hasDerivAt_heathBrownAtkinsonPhaseDifference
      (hu.trans htu) hu (hleft.trans_le hx.1)).continuousAt.continuousWithinAt
  have hderiv : ∀ x ∈ Set.Ioo ((K + n : ℕ) : ℝ)
      ((K + n + 1 : ℕ) : ℝ), HasDerivAt F (F' x) x := by
    intro x hx
    exact hasDerivAt_heathBrownAtkinsonPhaseDifference
      (hu.trans htu) hu (hleft.trans hx.1)
  obtain ⟨xi, hxi, heq⟩ :=
    exists_hasDerivAt_eq_slope F F' hlt hcont hderiv
  refine ⟨xi, hxi, ?_⟩
  dsimp only [F, F'] at heq ⊢
  have hone : (((K + n + 1 : ℕ) : ℝ) - ((K + n : ℕ) : ℝ)) = 1 := by
    push_cast
    ring
  rw [hone, div_one] at heq
  rw [heathBrownAtkinsonPhaseDifference] at heq
  unfold heathBrownAtkinsonIncreasingDifferenceNat
  rw [← heathBrownAtkinsonRealPhase_natCast,
    ← heathBrownAtkinsonRealPhase_natCast,
    ← heathBrownAtkinsonRealPhase_natCast,
    ← heathBrownAtkinsonRealPhase_natCast]
  simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using heq

/-- Uniform unit-increment bounds obtained from the pointwise derivative
estimate. -/
theorem heathBrownAtkinsonIncreasingDifferenceNat_increment_bounds
    {t u : ℝ} {K N : ℕ}
    (hu : 0 < u) (htu : u < t) (hK : 0 < K)
    (hblock : (((K + N + 2 : ℕ) : ℝ)) ≤ u)
    (htUpper : t ≤ 2 * u) :
    ∀ n ≤ N,
      heathBrownAtkinsonFirstDerivativeLower u t K (K + N + 1) ≤
          heathBrownAtkinsonIncreasingDifferenceNat t u K (n + 1) -
            heathBrownAtkinsonIncreasingDifferenceNat t u K n ∧
        heathBrownAtkinsonIncreasingDifferenceNat t u K (n + 1) -
            heathBrownAtkinsonIncreasingDifferenceNat t u K n ≤
          heathBrownAtkinsonFirstDerivativeUpper u t K (K + N + 1) := by
  intro n hn
  obtain ⟨xi, hxi, heq⟩ :=
    exists_heathBrownAtkinsonIncreasingDifferenceNat_increment hu htu hK
      (K := K) (n := n)
  have hAxi : (K : ℝ) ≤ xi := by
    have hKle : (K : ℝ) ≤ ((K + n : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_add_right K n
    exact hKle.trans hxi.1.le
  have hxiB : xi ≤ ((K + N + 1 : ℕ) : ℝ) := by
    have hcast : ((K + n + 1 : ℕ) : ℝ) ≤
        ((K + N + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show K + n + 1 ≤ K + N + 1 by omega)
    exact hxi.2.le.trans hcast
  have hBu : ((K + N + 1 : ℕ) : ℝ) ≤ u := by
    exact_mod_cast hblock.trans' (by
      exact_mod_cast (show K + N + 1 ≤ K + N + 2 by omega))
  have hb := heathBrownAtkinsonRealSlopeDifference_box_bounds
    hu htu (by exact_mod_cast hK) hAxi hxiB hBu htUpper
  rw [heq] at hb
  simpa only [Nat.cast_add, Nat.cast_one] using hb

/-- The unit increments of the positively sloped phase orientation decrease
with the summation index. -/
theorem heathBrownAtkinsonIncreasingDifferenceNat_increment_anti
    {t u : ℝ} {K N : ℕ}
    (hu : 0 < u) (htu : u < t) (hK : 0 < K)
    (hblock : (((K + N + 2 : ℕ) : ℝ)) ≤ u)
    (htUpper : t ≤ 2 * u) :
    ∀ n < N,
      heathBrownAtkinsonIncreasingDifferenceNat t u K (n + 2) -
          heathBrownAtkinsonIncreasingDifferenceNat t u K (n + 1) ≤
        heathBrownAtkinsonIncreasingDifferenceNat t u K (n + 1) -
          heathBrownAtkinsonIncreasingDifferenceNat t u K n := by
  intro n hn
  have hsecond :=
    (heathBrownAtkinsonPositiveDifferenceNat_secondDifference_bounds
      hu htu hK hblock htUpper n hn).1
  have hlam := heathBrownAtkinsonBProcessLambda_pos
    (N := N) hu htu hK
  unfold heathBrownAtkinsonPositiveDifferenceNat at hsecond
  unfold heathBrownAtkinsonIncreasingDifferenceNat
  linarith

/-- The first-derivative form of Kusmin--Landau for the exact phase
difference.  The upper-scale hypothesis is the source's small-frequency
case; it keeps every period-endpoint condition explicit. -/
theorem heathBrownAtkinsonIncreasingDifference_KL
    {t u : ℝ} {K N : ℕ}
    (hu : 0 < u) (htu : u < t) (hK : 0 < K)
    (hblock : (((K + N + 2 : ℕ) : ℝ)) ≤ u)
    (htUpper : t ≤ 2 * u)
    (hsmall :
      heathBrownAtkinsonFirstDerivativeUpper u t K (K + N + 1) ≤
        Real.pi) :
    ‖∑ n ∈ Finset.range (N + 1),
        RiemannZeta.GuthMaynard.unitaryPhase
          (heathBrownAtkinsonIncreasingDifferenceNat t u K n)‖ ≤
      2 * Real.pi /
        heathBrownAtkinsonFirstDerivativeLower u t K (K + N + 1) := by
  let δ := heathBrownAtkinsonFirstDerivativeLower u t K (K + N + 1)
  have hKreal : 0 < (K : ℝ) := by exact_mod_cast hK
  have hBreal : 0 < ((K + N + 1 : ℕ) : ℝ) := by positivity
  have hBexpr : 0 < (K : ℝ) + (N : ℝ) + 1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using hBreal
  have hδ : 0 < δ := by
    unfold δ heathBrownAtkinsonFirstDerivativeLower
    exact div_pos (mul_pos Real.pi_pos (sub_pos.mpr htu))
      (mul_pos hBexpr (heathBrownAtkinsonSlopeUpper_pos hu hKreal))
  have hb := heathBrownAtkinsonIncreasingDifferenceNat_increment_bounds
    hu htu hK hblock htUpper
  have hδpi : δ ≤ Real.pi := by
    exact (hb 0 (Nat.zero_le N)).1.trans
      ((hb 0 (Nat.zero_le N)).2.trans hsmall)
  apply RiemannZeta.GuthMaynard.kusminLandau_one_period_decreasing
      (heathBrownAtkinsonIncreasingDifferenceNat t u K) N δ hδ
  · intro n hn
    exact (hb n hn).1
  · intro n hn
    have hupp := (hb n hn).2.trans hsmall
    linarith
  · exact heathBrownAtkinsonIncreasingDifferenceNat_increment_anti
      hu htu hK hblock htUpper


end

end GafniTao
