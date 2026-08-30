import PrimeShell.AmplitudeFamily
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Support

namespace PrimeShell

noncomputable section

open Function Metric Set

/-- The normalized center of each Prime Shell band. -/
def shellBandCenter : ℝ := 999 / 2000

/-- The radius on which each band is identically one before normalization. -/
def shellBandInnerRadius : ℝ := 1 / 4000

/-- The outer support radius of each band.  The two supports reach, but do
not cross, the endpoints `-1/2` and `1/2`. -/
def shellBandOuterRadius : ℝ := 1 / 2000

theorem shellBandInnerRadius_pos : 0 < shellBandInnerRadius := by
  norm_num [shellBandInnerRadius]

theorem shellBandInner_lt_outer :
    shellBandInnerRadius < shellBandOuterRadius := by
  norm_num [shellBandInnerRadius, shellBandOuterRadius]

/-- The right-hand smooth bump. -/
def shellRightBump : ContDiffBump shellBandCenter :=
  ⟨shellBandInnerRadius, shellBandOuterRadius,
    shellBandInnerRadius_pos, shellBandInner_lt_outer⟩

/-- The reflected left-hand smooth bump. -/
def shellLeftBump : ContDiffBump (-shellBandCenter) :=
  ⟨shellBandInnerRadius, shellBandOuterRadius,
    shellBandInnerRadius_pos, shellBandInner_lt_outer⟩

/-- A concrete disconnected amplitude.  Division by two gives a uniform
`[0,1]` bound without needing disjointness in the analytic entry theorem. -/
def twoBandAmplitude (s : ℝ) : ℝ :=
  (shellRightBump s + shellLeftBump s) / 2

theorem shellRightBump_neg (s : ℝ) :
    shellRightBump (-s) = shellLeftBump s := by
  simp only [shellRightBump, shellLeftBump, ContDiffBump.apply]
  rw [show (-s - shellBandCenter) = -(s - -shellBandCenter) by ring]
  rw [smul_neg, ContDiffBumpBase.symmetric]

theorem shellLeftBump_neg (s : ℝ) :
    shellLeftBump (-s) = shellRightBump s := by
  simpa only [neg_neg] using (shellRightBump_neg (-s)).symm

theorem twoBandAmplitude_even (s : ℝ) :
    twoBandAmplitude (-s) = twoBandAmplitude s := by
  simp only [twoBandAmplitude, shellRightBump_neg, shellLeftBump_neg]
  ring

theorem twoBandAmplitude_nonneg (s : ℝ) : 0 ≤ twoBandAmplitude s := by
  unfold twoBandAmplitude
  have hr := shellRightBump.nonneg (x := s)
  have hl := shellLeftBump.nonneg (x := s)
  linarith

theorem twoBandAmplitude_le_one (s : ℝ) : twoBandAmplitude s ≤ 1 := by
  unfold twoBandAmplitude
  have hr := shellRightBump.le_one (x := s)
  have hl := shellLeftBump.le_one (x := s)
  linarith

theorem twoBandAmplitude_contDiff : ContDiff ℝ 3 twoBandAmplitude := by
  exact (shellRightBump.contDiff.add shellLeftBump.contDiff).div_const 2

private theorem iteratedDeriv_hasCompactSupport
    {f : ℝ → ℝ} (hf : HasCompactSupport f) (i : ℕ) :
    HasCompactSupport (iteratedDeriv i f) := by
  induction i with
  | zero => simpa using hf
  | succ i hi =>
      rw [iteratedDeriv_succ]
      exact hi.deriv

private theorem exists_iteratedDeriv_abs_bound
    {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f) (hfc : HasCompactSupport f)
    (i : ℕ) (hi : i ≤ 3) :
    ∃ B : ℝ, ∀ s : ℝ, |iteratedDeriv i f s| ≤ B := by
  have hcont : Continuous (iteratedDeriv i f) :=
    hf.continuous_iteratedDeriv i (by exact_mod_cast hi)
  have hcompact := iteratedDeriv_hasCompactSupport hfc i
  have hbdd : BddAbove (range fun s : ℝ => |iteratedDeriv i f s|) :=
    hcont.abs.bddAbove_range_of_hasCompactSupport hcompact.abs
  obtain ⟨B, hB⟩ := hbdd
  exact ⟨B, fun s => hB (mem_range_self s)⟩

theorem twoBandAmplitude_hasCompactSupport :
    HasCompactSupport twoBandAmplitude := by
  have hsum := shellRightBump.hasCompactSupport.add shellLeftBump.hasCompactSupport
  have hscaled := hsum.smul_left (f := fun _ : ℝ => (1 / 2 : ℝ))
  have heq : twoBandAmplitude =
      (fun _ : ℝ => (1 / 2 : ℝ)) *
        ((shellRightBump : ℝ → ℝ) + (shellLeftBump : ℝ → ℝ)) := by
    funext s
    simp [twoBandAmplitude, div_eq_mul_inv, mul_comm]
  rw [heq]
  simpa [Pi.smul_apply, smul_eq_mul] using hscaled

theorem twoBandAmplitude_deriv_bound :
    ∃ H : ℝ, 1 ≤ H ∧
      ∀ i : ℕ, i ≤ 3 → ∀ s : ℝ, |iteratedDeriv i twoBandAmplitude s| ≤ H := by
  obtain ⟨B0, hB0⟩ := exists_iteratedDeriv_abs_bound
    twoBandAmplitude_contDiff twoBandAmplitude_hasCompactSupport 0 (by omega)
  obtain ⟨B1, hB1⟩ := exists_iteratedDeriv_abs_bound
    twoBandAmplitude_contDiff twoBandAmplitude_hasCompactSupport 1 (by omega)
  obtain ⟨B2, hB2⟩ := exists_iteratedDeriv_abs_bound
    twoBandAmplitude_contDiff twoBandAmplitude_hasCompactSupport 2 (by omega)
  obtain ⟨B3, hB3⟩ := exists_iteratedDeriv_abs_bound
    twoBandAmplitude_contDiff twoBandAmplitude_hasCompactSupport 3 (by omega)
  let H := max 1 (max B0 (max B1 (max B2 B3)))
  refine ⟨H, le_max_left _ _, ?_⟩
  intro i hi s
  interval_cases i
  · exact (hB0 s).trans (le_max_of_le_right (le_max_left _ _))
  · exact (hB1 s).trans
      (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))
  · exact (hB2 s).trans
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))))
  · exact (hB3 s).trans
      (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_right _ _))))

/-- The concrete disconnected amplitude satisfies the exact analytic
contract needed by the extended explicit formula. -/
theorem twoBandAmplitude_profile : AmplitudeProfile twoBandAmplitude := by
  exact ⟨twoBandAmplitude_even, twoBandAmplitude_contDiff,
    twoBandAmplitude_nonneg, twoBandAmplitude_le_one,
    twoBandAmplitude_deriv_bound⟩

/-- Both bump supports are contained in the source interval `[-1/2,1/2]`. -/
theorem twoBandAmplitude_eq_zero_of_half_le_abs
    {s : ℝ} (hs : 1 / 2 ≤ |s|) : twoBandAmplitude s = 0 := by
  have hr : shellRightBump s = 0 := by
    apply shellRightBump.zero_of_le_dist
    rw [Real.dist_eq]
    dsimp [shellRightBump]
    unfold shellBandCenter shellBandOuterRadius
    rcases le_total 0 s with hs0 | hs0
    · rw [abs_of_nonneg hs0] at hs
      rw [abs_of_nonneg]
      · linarith
      · linarith
    · rw [abs_of_nonpos hs0] at hs
      rw [abs_of_nonpos]
      · linarith
      · linarith
  have hl : shellLeftBump s = 0 := by
    apply shellLeftBump.zero_of_le_dist
    rw [Real.dist_eq]
    dsimp [shellLeftBump]
    unfold shellBandCenter shellBandOuterRadius
    rcases le_total 0 s with hs0 | hs0
    · rw [abs_of_nonneg hs0] at hs
      rw [abs_of_nonneg]
      · linarith
      · linarith
    · rw [abs_of_nonpos hs0] at hs
      rw [abs_of_nonpos]
      · linarith
      · linarith
  simp [twoBandAmplitude, hr, hl]

/-- The right band is genuinely present. -/
theorem twoBandAmplitude_center_pos :
    0 < twoBandAmplitude shellBandCenter := by
  unfold twoBandAmplitude
  have hr : shellRightBump shellBandCenter = 1 := by
    apply shellRightBump.one_of_mem_closedBall
    simp [shellRightBump, shellBandInnerRadius_pos.le]
  rw [hr]
  have hl := shellLeftBump.nonneg (x := shellBandCenter)
  linarith

/-- The two band centers produce a normalized source difference of exactly
`999/1000`, already inside the MRT-compatible high shell. -/
theorem shellBand_center_difference :
    shellBandCenter - (-shellBandCenter) = 999 / 1000 := by
  norm_num [shellBandCenter]

/-- Membership in one of the two normalized amplitude bands. -/
def InTwoBand (s : ℝ) : Prop :=
  |s - shellBandCenter| < shellBandOuterRadius ∨
    |s + shellBandCenter| < shellBandOuterRadius

theorem inTwoBand_of_twoBandAmplitude_ne_zero
    {s : ℝ} (hs : twoBandAmplitude s ≠ 0) : InTwoBand s := by
  by_cases hr : shellRightBump s = 0
  · have hl : shellLeftBump s ≠ 0 := by
      intro hl
      apply hs
      simp [twoBandAmplitude, hr, hl]
    right
    have hmem : s ∈ Function.support shellLeftBump := hl
    rw [shellLeftBump.support_eq, mem_ball, Real.dist_eq] at hmem
    simpa [shellLeftBump, sub_neg_eq_add] using hmem
  · left
    have hmem : s ∈ Function.support shellRightBump := hr
    rw [shellRightBump.support_eq, mem_ball, Real.dist_eq] at hmem
    simpa [shellRightBump] using hmem

/-- The exact normalized difference-set support: same-band pairs lie near
zero, while cross-band pairs lie near `±2*shellBandCenter`. -/
def InTwoBandDifferenceSet (y : ℝ) : Prop :=
  |y| < 2 * shellBandOuterRadius ∨
    |y - 2 * shellBandCenter| < 2 * shellBandOuterRadius ∨
    |y + 2 * shellBandCenter| < 2 * shellBandOuterRadius

theorem inTwoBandDifferenceSet_of
    {s t : ℝ} (hs : InTwoBand s) (ht : InTwoBand t) :
    InTwoBandDifferenceSet (t - s) := by
  rcases hs with hs | hs <;> rcases ht with ht | ht
  · left
    rw [abs_lt] at hs ht ⊢
    constructor <;> linarith
  · right; right
    rw [abs_lt] at hs ht ⊢
    constructor <;> linarith
  · right; left
    rw [abs_lt] at hs ht ⊢
    constructor <;> linarith
  · left
    rw [abs_lt] at hs ht ⊢
    constructor <;> linarith

/-- The concrete amplitude-modulated physical test function. -/
def twoBandWindow (P : Zeta23.Params) (T u : ℝ) : ℝ :=
  twoBandAmplitude (u / P.L T) * P.phi T u

/-- Its squared-window autocorrelation, which is the source-side function
appearing in the prime diagonal and off-diagonal trace. -/
def twoBandSourceAutocorr (P : Zeta23.Params) (T y : ℝ) : ℝ :=
  Zeta23.Params.autocorr (fun u => twoBandWindow P T u ^ 2) y

theorem twoBandSourceAutocorr_eq_zero_of_not_mem_differenceSet
    {P : Zeta23.Params} {T y : ℝ} (hL : P.L T ≠ 0)
    (hy : ¬ InTwoBandDifferenceSet (y / P.L T)) :
    twoBandSourceAutocorr P T y = 0 := by
  unfold twoBandSourceAutocorr Zeta23.Params.autocorr
  have hpoint : (fun u : ℝ => twoBandWindow P T u ^ 2 *
      twoBandWindow P T (u + y) ^ 2) = 0 := by
    funext u
    by_cases hu : twoBandWindow P T u = 0
    · simp [hu]
    by_cases huy : twoBandWindow P T (u + y) = 0
    · simp [huy]
    exfalso
    apply hy
    have hqu : twoBandAmplitude (u / P.L T) ≠ 0 := by
      intro hzero
      apply hu
      simp [twoBandWindow, hzero]
    have hquy : twoBandAmplitude ((u + y) / P.L T) ≠ 0 := by
      intro hzero
      apply huy
      simp [twoBandWindow, hzero]
    have hgeom := inTwoBandDifferenceSet_of
      (inTwoBand_of_twoBandAmplitude_ne_zero hqu)
      (inTwoBand_of_twoBandAmplitude_ne_zero hquy)
    have heq : (u + y) / P.L T - u / P.L T = y / P.L T := by
      field_simp
      ring
    rwa [heq] at hgeom
  rw [hpoint]
  simp

/-- The abstract source autocorrelation above is definitionally the `g`
attached to the concrete `atV (q²)` family. -/
theorem atTwoBand_g_eq
    {P : Zeta23.Params} {T : ℝ} (hw : P.w ≠ 0) :
    (P.atV (amplitudeSq twoBandAmplitude) T).g T =
      twoBandSourceAutocorr P T := by
  funext y
  unfold Zeta23.Params.g twoBandSourceAutocorr twoBandWindow
  rw [atAmplitude_phi twoBandAmplitude_profile T hw]

/-- Consequently the actual source-side `g` has no mass outside the exact
low-frequency and high-shell difference-set regions. -/
theorem atTwoBand_g_eq_zero_of_not_mem_differenceSet
    {P : Zeta23.Params} {T y : ℝ} (hw : P.w ≠ 0) (hL : P.L T ≠ 0)
    (hy : ¬ InTwoBandDifferenceSet (y / P.L T)) :
    (P.atV (amplitudeSq twoBandAmplitude) T).g T y = 0 := by
  rw [atTwoBand_g_eq hw]
  exact twoBandSourceAutocorr_eq_zero_of_not_mem_differenceSet hL hy

/-- The center of the positive source shell, at the concrete full-chain
bandwidth, lies strictly beyond the MRT exponent `33/25`. -/
theorem concrete_shell_center_exceeds_mrt_threshold :
    (33 / 25 : ℝ) <
      concretePrimeShellParams.lam * (2 * shellBandCenter) := by
  norm_num [concretePrimeShellParams, shellBandCenter]

/-- The entire cross-band source shell, not merely its center, lies beyond
the MRT threshold with a strict rational margin. -/
theorem concrete_shell_lower_edge_exceeds_mrt_threshold :
    (33 / 25 : ℝ) < concretePrimeShellParams.lam *
      (2 * shellBandCenter - 2 * shellBandOuterRadius) := by
  norm_num [concretePrimeShellParams, shellBandCenter, shellBandOuterRadius]

end

end PrimeShell
