import GafniTao.HeathBrownAtkinsonPhase

/-!
# Differential identities for Heath--Brown's Atkinson phase

This file proves the normalization and the first two differential identities
used in Heath--Brown (1978), between equations (11) and (16).  All identities
retain the literal phase from equation (11); the normalized phase is an
algebraic convenience, not a replacement source object.
-/

open Real

namespace GafniTao

noncomputable section

/-- The dimensionless ratio `pi*n/(2*T)` in the Atkinson phase. -/
def heathBrownAtkinsonRatio (T : ℝ) (n : ℕ) : ℝ :=
  Real.pi * (n : ℝ) / (2 * T)

/-- The positive square-root coordinate used to normalize the phase. -/
def heathBrownAtkinsonRoot (T : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (heathBrownAtkinsonRatio T n)

/-- An algebraically normalized version of Heath--Brown's exact phase. -/
def heathBrownAtkinsonNormalizedPhase (T : ℝ) (n : ℕ) : ℝ :=
  2 * T *
      (Real.arsinh (heathBrownAtkinsonRoot T n) +
        heathBrownAtkinsonRoot T n *
          Real.sqrt (1 + (heathBrownAtkinsonRoot T n) ^ 2)) -
    Real.pi / 4

/-- The radical term in equation (11) equals its normalized product form. -/
theorem heathBrownAtkinsonRadical_eq
    {T : ℝ} {n : ℕ} (hT : 0 < T) (hn : 0 < n) :
    Real.sqrt
        (2 * Real.pi * (n : ℝ) * T +
          Real.pi ^ (2 : ℕ) * (n : ℝ) ^ (2 : ℕ)) =
      2 * T * Real.sqrt (heathBrownAtkinsonRatio T n) *
        Real.sqrt (1 + heathBrownAtkinsonRatio T n) := by
  have hq : 0 < heathBrownAtkinsonRatio T n := by
    unfold heathBrownAtkinsonRatio
    positivity
  have hradicand : 0 ≤
      2 * Real.pi * (n : ℝ) * T +
        Real.pi ^ (2 : ℕ) * (n : ℝ) ^ (2 : ℕ) := by
    positivity
  have hleftsq := Real.sq_sqrt hradicand
  have hqsq := Real.sq_sqrt hq.le
  have honesq := Real.sq_sqrt
    (show 0 ≤ 1 + heathBrownAtkinsonRatio T n by positivity)
  unfold heathBrownAtkinsonRatio at hqsq honesq ⊢
  apply sq_eq_sq_iff_eq_or_eq_neg.mp
    (show
      (Real.sqrt
        (2 * Real.pi * (n : ℝ) * T +
          Real.pi ^ (2 : ℕ) * (n : ℝ) ^ (2 : ℕ))) ^ 2 =
        (2 * T * Real.sqrt (Real.pi * (n : ℝ) / (2 * T)) *
          Real.sqrt (1 + Real.pi * (n : ℝ) / (2 * T))) ^ 2 by
      rw [hleftsq, mul_pow, mul_pow, hqsq, honesq]
      field_simp [hT.ne'])
  |>.resolve_right (by
    intro hneg
    have hright : 0 <
        2 * T * Real.sqrt (Real.pi * (n : ℝ) / (2 * T)) *
          Real.sqrt (1 + Real.pi * (n : ℝ) / (2 * T)) := by
      positivity
    have hleft := Real.sqrt_nonneg
      (2 * Real.pi * (n : ℝ) * T +
        Real.pi ^ (2 : ℕ) * (n : ℝ) ^ (2 : ℕ))
    linarith)

/-- On the physical range, the normalized expression is exactly the source
phase from equation (11). -/
theorem heathBrownAtkinsonPhase_eq_normalized
    {T : ℝ} {n : ℕ} (hT : 0 < T) (hn : 0 < n) :
    heathBrownAtkinsonPhase T n =
      heathBrownAtkinsonNormalizedPhase T n := by
  rw [heathBrownAtkinsonPhase, heathBrownAtkinsonNormalizedPhase,
    heathBrownAtkinsonRoot, heathBrownAtkinsonRadical_eq hT hn]
  have hq : 0 ≤ heathBrownAtkinsonRatio T n := by
    unfold heathBrownAtkinsonRatio
    positivity
  rw [Real.sq_sqrt hq]
  unfold heathBrownAtkinsonRatio
  ring

/-- Derivative of the dimensionless ratio with respect to height. -/
theorem hasDerivAt_heathBrownAtkinsonRatio
    {T : ℝ} (n : ℕ) (hT : 0 < T) :
    HasDerivAt (fun u => heathBrownAtkinsonRatio u n)
      (-(heathBrownAtkinsonRatio T n) / T) T := by
  unfold heathBrownAtkinsonRatio
  convert ((hasDerivAt_const T (Real.pi * (n : ℝ))).div
    ((hasDerivAt_id T).const_mul 2) (by positivity : 2 * T ≠ 0)) using 1
  simp only [id_eq]
  field_simp [hT.ne']
  ring

/-- Derivative of the square-root coordinate with respect to height. -/
theorem hasDerivAt_heathBrownAtkinsonRoot
    {T : ℝ} {n : ℕ} (hT : 0 < T) (hn : 0 < n) :
    HasDerivAt (fun u => heathBrownAtkinsonRoot u n)
      (-(heathBrownAtkinsonRoot T n) / (2 * T)) T := by
  have hq : 0 < heathBrownAtkinsonRatio T n := by
    unfold heathBrownAtkinsonRatio
    positivity
  have hs := (hasDerivAt_heathBrownAtkinsonRatio n hT).sqrt hq.ne'
  unfold heathBrownAtkinsonRoot
  convert hs using 1
  have hsquare := Real.sq_sqrt hq.le
  field_simp [hT.ne', (Real.sqrt_pos.2 hq).ne']
  nlinarith

/-- The normalized phase has the exact first derivative recorded in
Heath--Brown's calculation. -/
theorem hasDerivAt_heathBrownAtkinsonNormalizedPhase
    {T : ℝ} {n : ℕ} (hT : 0 < T) (hn : 0 < n) :
    HasDerivAt (fun u => heathBrownAtkinsonNormalizedPhase u n)
      (2 * Real.arsinh (heathBrownAtkinsonRoot T n)) T := by
  have hx := hasDerivAt_heathBrownAtkinsonRoot hT hn
  let x : ℝ := heathBrownAtkinsonRoot T n
  let xp : ℝ := -x / (2 * T)
  let s : ℝ := Real.sqrt (1 + x ^ 2)
  let sp : ℝ := (xp * x + x * xp) / (2 * s)
  have hx' : HasDerivAt (fun u => heathBrownAtkinsonRoot u n) xp T := by
    simpa only [x, xp] using hx
  have hspos : 0 < s := by
    dsimp only [s, x]
    positivity
  have hinside : HasDerivAt
      (fun u => 1 + heathBrownAtkinsonRoot u n *
        heathBrownAtkinsonRoot u n)
      (xp * x + x * xp) T := by
    simpa only [zero_add, x] using
      (hasDerivAt_const T (1 : ℝ)).add (hx'.mul hx')
  have hs : HasDerivAt
      (fun u => Real.sqrt (1 + (heathBrownAtkinsonRoot u n) ^ 2))
      sp T := by
    have hne : 1 + heathBrownAtkinsonRoot T n *
        heathBrownAtkinsonRoot T n ≠ 0 := by
      have hsquare := sq_nonneg (heathBrownAtkinsonRoot T n)
      nlinarith
    have hs0 := hinside.sqrt hne
    simpa only [pow_two, sp, s, x] using hs0
  have hsum : HasDerivAt
      (fun u => Real.arsinh (heathBrownAtkinsonRoot u n) +
        heathBrownAtkinsonRoot u n *
          Real.sqrt (1 + (heathBrownAtkinsonRoot u n) ^ 2))
      (s⁻¹ * xp + (xp * s + x * sp)) T := by
    simpa only [x, s, sp] using hx'.arsinh.add (hx'.mul hs)
  have htwoT : HasDerivAt (fun u : ℝ => 2 * u) 2 T := by
    simpa only [mul_one] using (hasDerivAt_id T).const_mul 2
  have hsub := (htwoT.mul hsum).sub
    (hasDerivAt_const T (Real.pi / 4))
  have hsub' :
      HasDerivAt (fun u => heathBrownAtkinsonNormalizedPhase u n)
        (2 * (Real.arsinh x + x * s) +
          2 * T * (s⁻¹ * xp + (xp * s + x * sp)) - 0) T := by
    convert hsub using 1
  have hsquare : s ^ 2 = 1 + x ^ 2 := by
    dsimp only [s]
    exact Real.sq_sqrt (by positivity)
  have halg :
      2 * (Real.arsinh x + x * s) +
          2 * T * (s⁻¹ * xp + (xp * s + x * sp)) - 0 =
        2 * Real.arsinh x := by
    dsimp only [xp, sp]
    field_simp [hT.ne', hspos.ne']
    linear_combination 2 * x * hsquare
  exact hsub'.congr_deriv halg

/-- Exact first derivative of Heath--Brown's literal equation-(11) phase. -/
theorem hasDerivAt_heathBrownAtkinsonPhase
    {T : ℝ} {n : ℕ} (hT : 0 < T) (hn : 0 < n) :
    HasDerivAt (fun u => heathBrownAtkinsonPhase u n)
      (2 * Real.arsinh (heathBrownAtkinsonRoot T n)) T := by
  have hnorm := hasDerivAt_heathBrownAtkinsonNormalizedPhase hT hn
  have hev : (fun u => heathBrownAtkinsonPhase u n) =ᶠ[nhds T]
      (fun u => heathBrownAtkinsonNormalizedPhase u n) := by
    filter_upwards [eventually_gt_nhds hT] with u hu
    exact heathBrownAtkinsonPhase_eq_normalized hu hn
  exact hnorm.congr_of_eventuallyEq hev

/-- Derivative of the exact phase slope.  This is the curvature scale used
in the local Atkinson comparison. -/
theorem hasDerivAt_heathBrownAtkinsonPhaseSlope
    {T : ℝ} {n : ℕ} (hT : 0 < T) (hn : 0 < n) :
    HasDerivAt
      (fun u => 2 * Real.arsinh (heathBrownAtkinsonRoot u n))
      (-heathBrownAtkinsonRoot T n /
        (T * Real.sqrt (1 + (heathBrownAtkinsonRoot T n) ^ 2))) T := by
  have hx := hasDerivAt_heathBrownAtkinsonRoot hT hn
  have h := hx.arsinh.const_mul 2
  have hspos : 0 <
      Real.sqrt (1 + (heathBrownAtkinsonRoot T n) ^ 2) := by
    positivity
  have halg :
      2 * (Real.sqrt
          (1 + (heathBrownAtkinsonRoot T n) ^ 2))⁻¹ *
          (-heathBrownAtkinsonRoot T n / (2 * T)) =
        -heathBrownAtkinsonRoot T n /
          (T * Real.sqrt
            (1 + (heathBrownAtkinsonRoot T n) ^ 2)) := by
    field_simp [hT.ne', hspos.ne']
  have halg' :
      2 * (Real.sqrt
          (1 + (heathBrownAtkinsonRoot T n) ^ 2))⁻¹ •
          (-heathBrownAtkinsonRoot T n / (2 * T)) =
        -heathBrownAtkinsonRoot T n /
          (T * Real.sqrt
            (1 + (heathBrownAtkinsonRoot T n) ^ 2)) := by
    simpa only [smul_eq_mul, mul_assoc] using halg
  exact h.congr_deriv halg'


end

end GafniTao
