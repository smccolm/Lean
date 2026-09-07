import GafniTao.HeathBrownAtkinsonPhaseBounds

/-!
# The Atkinson phase as a function of the summation variable

Heath--Brown's use of the `(1/2,1/2)` exponent pair differentiates the
equation-(11) phase with respect to the (temporarily real) summation
variable.  This file retains the literal source phase and proves its exact
first derivative.  The normalized square-root coordinate is used only
inside the proof.
-/

open Real

namespace GafniTao

noncomputable section

/-- The literal equation-(11) Atkinson phase with a real summation
variable. -/
def heathBrownAtkinsonRealPhase (T x : ℝ) : ℝ :=
  2 * T * Real.arsinh (Real.sqrt (Real.pi * x / (2 * T))) +
    Real.sqrt (2 * Real.pi * x * T + Real.pi ^ (2 : ℕ) * x ^ (2 : ℕ)) -
    Real.pi / 4

/-- The dimensionless coordinate `pi*x/(2*T)` for a real index. -/
def heathBrownAtkinsonRealRatio (T x : ℝ) : ℝ :=
  Real.pi * x / (2 * T)

/-- The square-root coordinate for a real index. -/
def heathBrownAtkinsonRealRoot (T x : ℝ) : ℝ :=
  Real.sqrt (heathBrownAtkinsonRealRatio T x)

/-- The normalized real-index phase. -/
def heathBrownAtkinsonRealNormalizedPhase (T x : ℝ) : ℝ :=
  2 * T *
      (Real.arsinh (heathBrownAtkinsonRealRoot T x) +
        heathBrownAtkinsonRealRoot T x *
          Real.sqrt (1 + (heathBrownAtkinsonRealRoot T x) ^ 2)) -
    Real.pi / 4

/-- The real-index phase restricts to the source phase on natural
indices. -/
theorem heathBrownAtkinsonRealPhase_natCast (T : ℝ) (n : ℕ) :
    heathBrownAtkinsonRealPhase T n = heathBrownAtkinsonPhase T n := by
  rfl

/-- Algebraic normalization of the literal real-index phase. -/
theorem heathBrownAtkinsonRealPhase_eq_normalized
    {T x : ℝ} (hT : 0 < T) (hx : 0 < x) :
    heathBrownAtkinsonRealPhase T x =
      heathBrownAtkinsonRealNormalizedPhase T x := by
  have hq : 0 < heathBrownAtkinsonRealRatio T x := by
    unfold heathBrownAtkinsonRealRatio
    positivity
  have hradicand :
      0 ≤ 2 * Real.pi * x * T + Real.pi ^ (2 : ℕ) * x ^ (2 : ℕ) := by
    positivity
  have hleftsq := Real.sq_sqrt hradicand
  have hqsq := Real.sq_sqrt hq.le
  have honesq := Real.sq_sqrt (show
      0 ≤ 1 + heathBrownAtkinsonRealRatio T x by positivity)
  have hradical :
      Real.sqrt
          (2 * Real.pi * x * T + Real.pi ^ (2 : ℕ) * x ^ (2 : ℕ)) =
        2 * T * Real.sqrt (heathBrownAtkinsonRealRatio T x) *
          Real.sqrt (1 + heathBrownAtkinsonRealRatio T x) := by
    apply sq_eq_sq_iff_eq_or_eq_neg.mp
      (show
        (Real.sqrt
            (2 * Real.pi * x * T +
              Real.pi ^ (2 : ℕ) * x ^ (2 : ℕ))) ^ 2 =
          (2 * T * Real.sqrt (heathBrownAtkinsonRealRatio T x) *
            Real.sqrt (1 + heathBrownAtkinsonRealRatio T x)) ^ 2 by
        rw [hleftsq, mul_pow, mul_pow, hqsq, honesq]
        unfold heathBrownAtkinsonRealRatio
        field_simp [hT.ne'])
    |>.resolve_right (by
      intro hneg
      have hright : 0 <
          2 * T * Real.sqrt (heathBrownAtkinsonRealRatio T x) *
            Real.sqrt (1 + heathBrownAtkinsonRealRatio T x) := by
        positivity
      have hleft := Real.sqrt_nonneg
        (2 * Real.pi * x * T + Real.pi ^ (2 : ℕ) * x ^ (2 : ℕ))
      linarith)
  rw [heathBrownAtkinsonRealPhase,
    heathBrownAtkinsonRealNormalizedPhase, hradical,
    heathBrownAtkinsonRealRoot]
  rw [Real.sq_sqrt hq.le]
  unfold heathBrownAtkinsonRealRatio
  ring

/-- Derivative of the real-index ratio. -/
theorem hasDerivAt_heathBrownAtkinsonRealRatio
    {T x : ℝ} :
    HasDerivAt (heathBrownAtkinsonRealRatio T) (Real.pi / (2 * T)) x := by
  have h : HasDerivAt (fun u : ℝ => (Real.pi / (2 * T)) * u)
      (Real.pi / (2 * T)) x := by
    simpa only [id_eq, mul_one] using
      (hasDerivAt_id x).const_mul (Real.pi / (2 * T))
  convert h using 1
  funext u
  unfold heathBrownAtkinsonRealRatio
  ring

/-- Derivative of the real-index square-root coordinate. -/
theorem hasDerivAt_heathBrownAtkinsonRealRoot
    {T x : ℝ} (hT : 0 < T) (hx : 0 < x) :
    HasDerivAt (heathBrownAtkinsonRealRoot T)
      (heathBrownAtkinsonRealRoot T x / (2 * x)) x := by
  have hq : 0 < heathBrownAtkinsonRealRatio T x := by
    unfold heathBrownAtkinsonRealRatio
    positivity
  have hs := (hasDerivAt_heathBrownAtkinsonRealRatio (T := T) (x := x)).sqrt hq.ne'
  have hrootpos : 0 < heathBrownAtkinsonRealRoot T x := by
    unfold heathBrownAtkinsonRealRoot
    exact Real.sqrt_pos.2 hq
  have hsquare : (heathBrownAtkinsonRealRoot T x) ^ 2 =
      heathBrownAtkinsonRealRatio T x := by
    unfold heathBrownAtkinsonRealRoot
    exact Real.sq_sqrt hq.le
  have halg :
      Real.pi / (2 * T) /
          (2 * Real.sqrt (heathBrownAtkinsonRealRatio T x)) =
        heathBrownAtkinsonRealRoot T x / (2 * x) := by
    rw [show Real.sqrt (heathBrownAtkinsonRealRatio T x) =
      heathBrownAtkinsonRealRoot T x by rfl]
    have hcross :
        2 * T * (heathBrownAtkinsonRealRoot T x) ^ 2 = Real.pi * x := by
      rw [hsquare]
      unfold heathBrownAtkinsonRealRatio
      field_simp [hT.ne']
    field_simp [hT.ne', hx.ne', hrootpos.ne']
    nlinarith [hcross]
  exact hs.congr_deriv halg

/-- The exact first derivative with respect to the real summation variable.
This is the phase slope used in the source exponent-pair argument. -/
theorem hasDerivAt_heathBrownAtkinsonRealNormalizedPhase
    {T x : ℝ} (hT : 0 < T) (hx : 0 < x) :
    HasDerivAt (heathBrownAtkinsonRealNormalizedPhase T)
      (Real.sqrt (2 * Real.pi * T / x + Real.pi ^ (2 : ℕ))) x := by
  have hr := hasDerivAt_heathBrownAtkinsonRealRoot hT hx
  let r : ℝ := heathBrownAtkinsonRealRoot T x
  let rp : ℝ := r / (2 * x)
  let s : ℝ := Real.sqrt (1 + r ^ 2)
  let sp : ℝ := (rp * r + r * rp) / (2 * s)
  have hr' : HasDerivAt (heathBrownAtkinsonRealRoot T) rp x := by
    simpa only [r, rp] using hr
  have hspos : 0 < s := by
    dsimp only [s, r]
    positivity
  have hinside : HasDerivAt
      (fun u => 1 + heathBrownAtkinsonRealRoot T u *
        heathBrownAtkinsonRealRoot T u)
      (rp * r + r * rp) x := by
    simpa only [zero_add, r] using
      (hasDerivAt_const x (1 : ℝ)).add (hr'.mul hr')
  have hs : HasDerivAt
      (fun u => Real.sqrt (1 + (heathBrownAtkinsonRealRoot T u) ^ 2))
      sp x := by
    have hne : 1 + heathBrownAtkinsonRealRoot T x *
        heathBrownAtkinsonRealRoot T x ≠ 0 := by
      nlinarith [sq_nonneg (heathBrownAtkinsonRealRoot T x)]
    have hs0 := hinside.sqrt hne
    simpa only [pow_two, sp, s, r] using hs0
  have hsum : HasDerivAt
      (fun u => Real.arsinh (heathBrownAtkinsonRealRoot T u) +
        heathBrownAtkinsonRealRoot T u *
          Real.sqrt (1 + (heathBrownAtkinsonRealRoot T u) ^ 2))
      (s⁻¹ * rp + (rp * s + r * sp)) x := by
    simpa only [r, s, sp] using hr'.arsinh.add (hr'.mul hs)
  have hphase := hsum.const_mul (2 * T) |>.sub
    (hasDerivAt_const x (Real.pi / 4))
  have hsquare : s ^ 2 = 1 + r ^ 2 := by
    dsimp only [s]
    exact Real.sq_sqrt (by positivity)
  have hq : r ^ 2 = Real.pi * x / (2 * T) := by
    dsimp only [r, heathBrownAtkinsonRealRoot]
    rw [Real.sq_sqrt]
    · rfl
    · unfold heathBrownAtkinsonRealRatio
      positivity
  have hderiv :
      2 * T * (s⁻¹ * rp + (rp * s + r * sp)) - 0 =
        2 * T * r * s / x := by
    dsimp only [rp, sp]
    field_simp [hT.ne', hx.ne', hspos.ne']
    ring_nf
    rw [hsquare]
    ring
  have hsqtarget :
      (2 * T * r * s / x) ^ 2 =
        2 * Real.pi * T / x + Real.pi ^ (2 : ℕ) := by
    have hqmul : 2 * T * r ^ 2 = Real.pi * x := by
      field_simp [hT.ne'] at hq
      nlinarith
    have hinner : 2 * T * (1 + r ^ 2) = 2 * T + Real.pi * x := by
      nlinarith [hqmul]
    calc
      (2 * T * r * s / x) ^ 2 =
          (2 * T * r ^ 2) * (2 * T * s ^ 2) / x ^ 2 := by ring
      _ = (Real.pi * x) * (2 * T * (1 + r ^ 2)) / x ^ 2 := by
        rw [hqmul, hsquare]
      _ = (Real.pi * x) * (2 * T + Real.pi * x) / x ^ 2 := by
        rw [hinner]
      _ = 2 * Real.pi * T / x + Real.pi ^ (2 : ℕ) := by
        field_simp [hx.ne']
  have hnonneg : 0 ≤ 2 * T * r * s / x := by
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by positivity) (Real.sqrt_nonneg _)) hspos.le)
      hx.le
  have htarget_nonneg :
      0 ≤ Real.sqrt (2 * Real.pi * T / x + Real.pi ^ (2 : ℕ)) :=
    Real.sqrt_nonneg _
  have hradicand :
      0 ≤ 2 * Real.pi * T / x + Real.pi ^ (2 : ℕ) := by
    positivity
  have hsqrt_sq := Real.sq_sqrt hradicand
  have heq :
      2 * T * r * s / x =
        Real.sqrt (2 * Real.pi * T / x + Real.pi ^ (2 : ℕ)) := by
    nlinarith
  exact hphase.congr_deriv (hderiv.trans heq)

/-- Exact first derivative of the literal equation-(11) real-index phase. -/
theorem hasDerivAt_heathBrownAtkinsonRealPhase
    {T x : ℝ} (hT : 0 < T) (hx : 0 < x) :
    HasDerivAt (heathBrownAtkinsonRealPhase T)
      (Real.sqrt (2 * Real.pi * T / x + Real.pi ^ (2 : ℕ))) x := by
  have hnorm := hasDerivAt_heathBrownAtkinsonRealNormalizedPhase hT hx
  have hev : heathBrownAtkinsonRealPhase T =ᶠ[nhds x]
      heathBrownAtkinsonRealNormalizedPhase T := by
    filter_upwards [eventually_gt_nhds hx] with u hu
    exact heathBrownAtkinsonRealPhase_eq_normalized hT hu
  exact hnorm.congr_of_eventuallyEq hev


end

end GafniTao
