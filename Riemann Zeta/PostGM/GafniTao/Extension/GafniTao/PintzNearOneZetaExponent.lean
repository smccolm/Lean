import GafniTao.HeathBrownEP1Statement
import GafniTao.HeathBrownEPHalfBlock

/-!
# The zeta exponent needed in Pintz's strict near-one segment

Pintz applies his zeta estimate at real part `sigma = 1 - u` with
`0 <= u <= 1/12`.  On precisely this range the raw `AB` estimate, the
order-four derivative estimate, and Heath--Brown's `49/80` saving fit below
the coefficient `1/2` in Pintz (2.19).  The lemmas in this file retain the
physical logarithmic scale `tau`; no full-range Heath--Brown theorem is
asserted.
-/

namespace GafniTao

noncomputable section

/-- The unweighted `N`-exponent which becomes Pintz's zeta exponent after
the exact `n^(-sigma)` Abel weight is inserted and `t = N^tau` is used. -/
noncomputable def pintzNearOneUnweightedTarget
    (sigma epsilon tau : ℝ) : ℝ :=
  sigma + tau * ((1 / 2 : ℝ) * (1 - sigma) ^ (3 / 2 : ℝ) + epsilon)

private theorem nearOne_three_halves_eq_sqrt_cube
    {u : ℝ} (hu : 0 ≤ u) :
    u ^ (3 / 2 : ℝ) = (Real.sqrt u) ^ 3 := by
  rw [show (3 / 2 : ℝ) = (1 / 2 : ℝ) * (3 : ℕ) by norm_num,
    Real.rpow_mul_natCast]
  rw [show u ^ (1 / 2 : ℝ) = Real.sqrt u by
    exact (Real.sqrt_eq_rpow u).symm]
  exact hu

/-- The small numerical margin at the endpoint of the order-four range.
This is the only non-linear inequality needed for that range. -/
theorem pintz_nearOne_kfour_endpoint
    {u : ℝ} (hu : 0 ≤ u) (huUpper : u ≤ 1 / 12) :
    u - 1 / 24 ≤ (7 / 4 : ℝ) * u ^ (3 / 2 : ℝ) := by
  let r : ℝ := Real.sqrt u
  let a : ℝ := 13 / 45
  have hr : 0 ≤ r := Real.sqrt_nonneg u
  have hrsq : r ^ 2 = u := by
    dsimp only [r]
    exact Real.sq_sqrt hu
  have hra : r ≤ a := by
    have haNonneg : 0 ≤ a := by norm_num [a]
    apply (sq_le_sq₀ hr haNonneg).mp
    dsimp only [a]
    rw [hrsq]
    norm_num at huUpper ⊢
    linarith
  have hrSqLe : r ^ 2 ≤ a ^ 2 := by nlinarith
  have hraMul : r * a ≤ a ^ 2 := by
    have haNonneg : 0 ≤ a := by norm_num [a]
    nlinarith
  have hrSqMul : r ^ 2 ≤ r * a := by
    nlinarith
  have hbracket :
      42 * (r ^ 2 + r * a + a ^ 2) - 24 * (r + a) ≤ 0 := by
    dsimp only [a] at *
    nlinarith
  have hdiff :
      0 ≤ (r - a) *
        (42 * (r ^ 2 + r * a + a ^ 2) - 24 * (r + a)) :=
    mul_nonneg_of_nonpos_of_nonpos (by linarith) hbracket
  have hfactor :
      42 * r ^ 3 - 24 * r ^ 2 + 1 -
          (42 * a ^ 3 - 24 * a ^ 2 + 1) =
        (r - a) *
          (42 * (r ^ 2 + r * a + a ^ 2) - 24 * (r + a)) := by
    ring
  have haValue : 0 < 42 * a ^ 3 - 24 * a ^ 2 + 1 := by
    norm_num [a]
  have hpoly : 0 ≤ 42 * r ^ 3 - 24 * r ^ 2 + 1 := by
    rw [← hfactor] at hdiff
    linarith
  rw [nearOne_three_halves_eq_sqrt_cube hu]
  change u - 1 / 24 ≤ (7 / 4 : ℝ) * r ^ 3
  rw [← hrsq]
  nlinarith

/-- In the entire `AB` range the weighted exponent is already nonpositive. -/
theorem pintz_nearOne_AB_exponent_le
    {sigma epsilon tau : ℝ}
    (hsigmaUpper : sigma ≤ 1) (hsigmaLower : 11 / 12 ≤ sigma)
    (hepsilon : 0 ≤ epsilon) (htauLow : 2 ≤ tau)
    (htauHigh : tau ≤ 5 / 2) :
    (tau + 3) / 6 ≤ pintzNearOneUnweightedTarget sigma epsilon tau := by
  have hu : 0 ≤ 1 - sigma := by linarith
  have hpow : 0 ≤ (1 - sigma) ^ (3 / 2 : ℝ) :=
    Real.rpow_nonneg hu _
  unfold pintzNearOneUnweightedTarget
  nlinarith

/-- The first order-four monomial fits below the coefficient-one-half target
on `5/2 <= tau <= 7/2`. -/
theorem pintz_nearOne_kfour_first_exponent_le
    {sigma epsilon tau : ℝ}
    (hsigmaUpper : sigma ≤ 1) (hsigmaLower : 11 / 12 ≤ sigma)
    (hepsilon : 0 ≤ epsilon) (htauLow : 5 / 2 ≤ tau)
    (htauHigh : tau ≤ 7 / 2) :
    heathBrownLogFirstExponent 4 epsilon tau ≤
      pintzNearOneUnweightedTarget sigma epsilon tau := by
  let u : ℝ := 1 - sigma
  let q : ℝ := (1 / 2 : ℝ) * u ^ (3 / 2 : ℝ)
  have hu : 0 ≤ u := by dsimp only [u]; linarith
  have huUpper : u ≤ 1 / 12 := by dsimp only [u]; linarith
  have hendpoint := pintz_nearOne_kfour_endpoint hu huUpper
  have hpowLe : u ^ (3 / 2 : ℝ) ≤ u := by
    let r : ℝ := Real.sqrt u
    have hr : 0 ≤ r := Real.sqrt_nonneg u
    have hrsq : r ^ 2 = u := by
      dsimp only [r]
      exact Real.sq_sqrt hu
    have hrOne : r ≤ 1 := by
      have : r ^ 2 ≤ 1 := by rw [hrsq]; linarith
      nlinarith
    rw [nearOne_three_halves_eq_sqrt_cube hu]
    change r ^ 3 ≤ u
    rw [← hrsq]
    nlinarith
  have hqUpper : q ≤ 1 / 12 := by
    dsimp only [q]
    nlinarith
  have hcore : u + (tau - 4) / 12 ≤ tau * q := by
    have htauTerm :
        tau * (1 / 12 - q) ≤ (7 / 2 : ℝ) * (1 / 12 - q) :=
      mul_le_mul_of_nonneg_right htauHigh (by linarith)
    dsimp only [q] at hendpoint ⊢
    nlinarith
  unfold heathBrownLogFirstExponent pintzNearOneUnweightedTarget
  dsimp only [u, q] at hcore
  nlinarith

theorem pintz_nearOne_kfour_second_exponent_le
    {sigma epsilon tau : ℝ}
    (hsigmaUpper : sigma ≤ 1) (hsigmaLower : 11 / 12 ≤ sigma)
    (hepsilon : 0 ≤ epsilon) (htauLow : 5 / 2 ≤ tau) :
    heathBrownLogSecondExponent 4 epsilon ≤
      pintzNearOneUnweightedTarget sigma epsilon tau := by
  have hu : 0 ≤ 1 - sigma := by linarith
  have hpow : 0 ≤ (1 - sigma) ^ (3 / 2 : ℝ) :=
    Real.rpow_nonneg hu _
  unfold heathBrownLogSecondExponent pintzNearOneUnweightedTarget
  norm_num
  nlinarith

theorem pintz_nearOne_kfour_third_exponent_le
    {sigma epsilon tau : ℝ}
    (hsigmaUpper : sigma ≤ 1) (hsigmaLower : 11 / 12 ≤ sigma)
    (hepsilon : 0 ≤ epsilon) (htauLow : 5 / 2 ≤ tau) :
    heathBrownLogThirdExponent 4 epsilon tau ≤
      pintzNearOneUnweightedTarget sigma epsilon tau := by
  have hu : 0 ≤ 1 - sigma := by linarith
  have hpow : 0 ≤ (1 - sigma) ^ (3 / 2 : ℝ) :=
    Real.rpow_nonneg hu _
  unfold heathBrownLogThirdExponent pintzNearOneUnweightedTarget
  norm_num
  nlinarith

/-- On the order-four scale the unweighted target is monotone in the real
part throughout Pintz's near-one interval. -/
theorem pintzNearOneUnweightedTarget_lower_endpoint_le
    {sigma epsilon tau : ℝ}
    (hsigmaUpper : sigma ≤ 1) (hsigmaLower : 11 / 12 ≤ sigma)
    (htauNonneg : 0 ≤ tau) (htauUpper : tau ≤ 7 / 2) :
    pintzNearOneUnweightedTarget (11 / 12) epsilon tau ≤
      pintzNearOneUnweightedTarget sigma epsilon tau := by
  let u : ℝ := 1 - sigma
  let v : ℝ := 1 / 12
  let r : ℝ := Real.sqrt u
  let s : ℝ := Real.sqrt v
  have hu : 0 ≤ u := by dsimp only [u]; linarith
  have huv : u ≤ v := by dsimp only [u, v]; linarith
  have hv : 0 ≤ v := by norm_num [v]
  have hr : 0 ≤ r := Real.sqrt_nonneg u
  have hs : 0 ≤ s := Real.sqrt_nonneg v
  have hrsq : r ^ 2 = u := by
    dsimp only [r]
    exact Real.sq_sqrt hu
  have hssq : s ^ 2 = v := by
    dsimp only [s]
    exact Real.sq_sqrt hv
  have hrs : r ≤ s := Real.sqrt_le_sqrt huv
  have hsThird : s ≤ 1 / 3 := by
    have : s ^ 2 ≤ (1 / 3 : ℝ) ^ 2 := by rw [hssq]; norm_num [v]
    nlinarith
  have hsum : r ^ 2 + r * s + s ^ 2 ≤
      (3 / 2 : ℝ) * s * (r + s) := by
    have hfactor :
        (3 / 2 : ℝ) * s * (r + s) -
            (r ^ 2 + r * s + s ^ 2) =
          (s - r) * (r + s / 2) := by ring
    have hp : 0 ≤ (s - r) * (r + s / 2) := by positivity
    nlinarith
  have hsumHalf : r ^ 2 + r * s + s ^ 2 ≤
      (1 / 2 : ℝ) * (r + s) := by
    calc
      r ^ 2 + r * s + s ^ 2 ≤
          (3 / 2 : ℝ) * s * (r + s) := hsum
      _ ≤ (1 / 2 : ℝ) * (r + s) := by
        have hrsNonneg : 0 ≤ r + s := by positivity
        nlinarith
  have hcube : s ^ 3 - r ^ 3 ≤ (1 / 2 : ℝ) * (s ^ 2 - r ^ 2) := by
    have hleft : s ^ 3 - r ^ 3 =
        (s - r) * (r ^ 2 + r * s + s ^ 2) := by ring
    have hright : s ^ 2 - r ^ 2 = (s - r) * (r + s) := by ring
    rw [hleft, hright]
    have hmul := mul_le_mul_of_nonneg_left hsumHalf (sub_nonneg.mpr hrs)
    nlinarith
  have hupow : u ^ (3 / 2 : ℝ) = r ^ 3 :=
    (nearOne_three_halves_eq_sqrt_cube hu).trans rfl
  have hvpow : v ^ (3 / 2 : ℝ) = s ^ 3 :=
    (nearOne_three_halves_eq_sqrt_cube hv).trans rfl
  have hpowerDiff :
      v ^ (3 / 2 : ℝ) - u ^ (3 / 2 : ℝ) ≤ (1 / 2 : ℝ) * (v - u) := by
    rw [hupow, hvpow, ← hrsq, ← hssq]
    exact hcube
  have hdiffNonneg : 0 ≤ v - u := sub_nonneg.mpr huv
  unfold pintzNearOneUnweightedTarget
  dsimp only [u, v] at hpowerDiff hdiffNonneg ⊢
  norm_num at hpowerDiff hdiffNonneg ⊢
  nlinarith

/-- The `49/80` source saving yields the coefficient `1/2` target on every
large logarithmic scale. -/
theorem pintz_nearOne_EP1_exponent_le
    {sigma epsilon tau : ℝ}
    (hsigmaUpper : sigma ≤ 1) (hepsilon : 0 ≤ epsilon)
    (htau : 7 / 2 ≤ tau) :
    heathBrownEP1Target epsilon tau ≤
      pintzNearOneUnweightedTarget sigma epsilon tau := by
  let u : ℝ := 1 - sigma
  have hu : 0 ≤ u := by dsimp only [u]; linarith
  have htauPos : 0 < tau := by linarith
  have hsource := heathBrown_zeta_exponent_le hu htauPos
  have hkappa := heathBrownZetaKappa_lt_half
  have hupow : 0 ≤ u ^ (3 / 2 : ℝ) := Real.rpow_nonneg hu _
  have hhalf :
      u / tau - 49 / (80 * tau ^ 3) ≤
        (1 / 2 : ℝ) * u ^ (3 / 2 : ℝ) := by
    exact hsource.trans (mul_le_mul_of_nonneg_right hkappa.le hupow)
  have htauSq : 0 < tau ^ 2 := sq_pos_of_pos htauPos
  have hscaled := mul_le_mul_of_nonneg_left hhalf htauPos.le
  have hleft :
      tau * (u / tau - 49 / (80 * tau ^ 3)) =
        u - 49 / (80 * tau ^ 2) := by
    field_simp [htauPos.ne']
  rw [hleft] at hscaled
  unfold heathBrownEP1Target pintzNearOneUnweightedTarget
  dsimp only [u] at hhalf ⊢
  dsimp only [u] at hscaled
  have htauOne : 1 ≤ tau := by linarith
  nlinarith

#print axioms pintz_nearOne_kfour_endpoint
#print axioms pintz_nearOne_AB_exponent_le
#print axioms pintz_nearOne_kfour_first_exponent_le
#print axioms pintz_nearOne_kfour_second_exponent_le
#print axioms pintz_nearOne_kfour_third_exponent_le
#print axioms pintzNearOneUnweightedTarget_lower_endpoint_le
#print axioms pintz_nearOne_EP1_exponent_le

end

end GafniTao
