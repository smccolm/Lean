import GafniTao.NearOneInputs
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Source-facing Vinogradov--Korobov zero-free region

The published zero-free region is a statement about every actual zeta zero.
The right-edge argument consumes a statement about the multiplicity-weighted
count in a whole rectangle.  This file records the exact rectangle statement
and proves the consumer bridge.  In particular, the count-level conclusion is
not accepted as an unrelated hypothesis.
-/

namespace GafniTao

/-- The denominator in the Vinogradov--Korobov zero-free width. -/
noncomputable def vinogradovKorobovDenominator (T : ℝ) : ℝ :=
  Real.log T ^ (2 / 3 : ℝ) *
    Real.log (Real.log T) ^ (1 / 3 : ℝ)

/-- Rectangle-uniform source form of the Vinogradov--Korobov region.  Every
nontrivial zeta zero of height at most `T` lies strictly to the left of the
displayed boundary.  The fixed lower height is exposed explicitly. -/
def VinogradovKorobovRectangleZeroFree (c T₀ : ℝ) : Prop :=
  ∀ ⦃T : ℝ⦄, T₀ ≤ T →
    0 ≤ c / vinogradovKorobovDenominator T ∧
    c / vinogradovKorobovDenominator T ≤ 1 ∧
    ∀ ⦃rho : ℂ⦄, rho ∈ zeroSet 0 T →
      rho.re < 1 - c / vinogradovKorobovDenominator T

/-- The physical denominator is monotone once the first logarithm is at
least one.  This is the scale comparison needed when a pointwise theorem at
height `|γ|` is used uniformly for every zero in a rectangle of height `T`. -/
theorem monotoneOn_vinogradovKorobovDenominator :
    MonotoneOn vinogradovKorobovDenominator (Set.Ici (Real.exp 1)) := by
  intro x hx y hy hxy
  have hxPos : 0 < x := (Real.exp_pos 1).trans_le hx
  have hyPos : 0 < y := hxPos.trans_le hxy
  have hlogXY : Real.log x ≤ Real.log y :=
    Real.strictMonoOn_log.monotoneOn hxPos hyPos hxy
  have hOneLogX : 1 ≤ Real.log x := by
    simpa only [Real.log_exp] using
      Real.strictMonoOn_log.monotoneOn (Real.exp_pos 1) hxPos hx
  have hOneLogY : 1 ≤ Real.log y := hOneLogX.trans hlogXY
  have hloglogXY : Real.log (Real.log x) ≤ Real.log (Real.log y) :=
    Real.strictMonoOn_log.monotoneOn (lt_of_lt_of_le zero_lt_one hOneLogX)
      (lt_of_lt_of_le zero_lt_one hOneLogY) hlogXY
  rw [vinogradovKorobovDenominator, vinogradovKorobovDenominator]
  exact mul_le_mul
    (Real.rpow_le_rpow (le_trans zero_le_one hOneLogX)
      hlogXY (by norm_num))
    (Real.rpow_le_rpow (Real.log_nonneg hOneLogX) hloglogXY (by norm_num))
    (Real.rpow_nonneg (Real.log_nonneg hOneLogX) _)
    (Real.rpow_nonneg (le_trans zero_le_one hOneLogY) _)

/-- Above `exp(exp 1)` both logarithmic factors in the physical denominator
are strictly positive. -/
theorem vinogradovKorobovDenominator_pos {T : ℝ}
    (hT : Real.exp (Real.exp 1) ≤ T) :
    0 < vinogradovKorobovDenominator T := by
  have hExpOnePos : 0 < Real.exp 1 := Real.exp_pos 1
  have hTPos : 0 < T := (Real.exp_pos (Real.exp 1)).trans_le hT
  have hLogLower : Real.exp 1 ≤ Real.log T := by
    simpa only [Real.log_exp] using
      Real.strictMonoOn_log.monotoneOn (Real.exp_pos (Real.exp 1)) hTPos hT
  have hLogPos : 0 < Real.log T := hExpOnePos.trans_le hLogLower
  have hLogLogPos : 0 < Real.log (Real.log T) :=
    Real.log_pos (lt_of_lt_of_le
      (by simpa only [Real.exp_zero] using
        (Real.exp_lt_exp.mpr (show (0 : ℝ) < 1 by norm_num))) hLogLower)
  exact mul_pos (Real.rpow_pos_of_pos hLogPos _) (Real.rpow_pos_of_pos hLogLogPos _)

/-- Direct pointwise source form of the published zero-free theorem.  This is
deliberately a statement about actual zeta zeros, not about a separately
supplied zero-count function. -/
def VinogradovKorobovPointwiseZeroFree (c H : ℝ) : Prop :=
  ∀ ⦃rho : ℂ⦄, riemannZeta rho = 0 → H ≤ |rho.im| →
    rho.re < 1 - c / vinogradovKorobovDenominator |rho.im|

/-- A pointwise Vinogradov--Korobov theorem gives the required uniform right
edge for the high zeros in every enclosing rectangle. -/
theorem vinogradovKorobov_high_zero_uniform
    {c H T : ℝ}
    (hc : 0 ≤ c)
    (hH : Real.exp (Real.exp 1) ≤ H)
    (hPointwise : VinogradovKorobovPointwiseZeroFree c H)
    {rho : ℂ} (hrho : rho ∈ zeroSet 0 T) (hrhoHigh : H ≤ |rho.im|) :
    rho.re < 1 - c / vinogradovKorobovDenominator T := by
  have hAbsUpper : |rho.im| ≤ T := by
    change rho ∈ RiemannZeta.GuthMaynard.zerosInRect 0 1 (-T) T at hrho
    rw [RiemannZeta.GuthMaynard.zerosInRect,
      Set.Finite.mem_toFinset, Set.mem_inter_iff] at hrho
    have hrect :=
      (RiemannZeta.GuthMaynard.mem_ZeroRectangle 0 1 (-T) T rho).mp hrho.1
    exact abs_le.mpr hrect.2.2
  have hAbsBase : Real.exp 1 ≤ |rho.im| :=
    (le_trans (by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by norm_num)) hH).trans hrhoHigh
  have hTBase : Real.exp 1 ≤ T := hAbsBase.trans hAbsUpper
  have hDenomMono :
      vinogradovKorobovDenominator |rho.im| ≤
        vinogradovKorobovDenominator T :=
    monotoneOn_vinogradovKorobovDenominator hAbsBase hTBase hAbsUpper
  have hDenomAbsPos : 0 < vinogradovKorobovDenominator |rho.im| :=
    vinogradovKorobovDenominator_pos (hH.trans hrhoHigh)
  have hWidth :
      c / vinogradovKorobovDenominator T ≤
        c / vinogradovKorobovDenominator |rho.im| :=
    div_le_div_of_nonneg_left hc hDenomAbsPos hDenomMono
  have hZero : riemannZeta rho = 0 := by
    change rho ∈ RiemannZeta.GuthMaynard.zerosInRect 0 1 (-T) T at hrho
    rw [RiemannZeta.GuthMaynard.zerosInRect,
      Set.Finite.mem_toFinset, Set.mem_inter_iff] at hrho
    exact hrho.2
  exact (hPointwise hZero hrhoHigh).trans_le (by linarith)

/-- A finite family of strictly positive real quantities has a single
strictly positive lower bound.  This elementary lemma is used to patch the
finitely many zeros below the height where Ford's theorem applies. -/
theorem exists_pos_lowerBound_finset {α : Type*} (s : Finset α) (f : α → ℝ)
    (hf : ∀ x ∈ s, 0 < f x) :
    ∃ d : ℝ, 0 < d ∧ ∀ x ∈ s, d ≤ f x := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, zero_lt_one, by simp⟩
  | @insert a s ha ih =>
      obtain ⟨d, hdPos, hd⟩ := ih (fun x hx => hf x (Finset.mem_insert_of_mem hx))
      refine ⟨min d (f a), lt_min hdPos (hf a (by simp)), ?_⟩
      intro x hx
      rw [Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hd x hx)

/-- A zero of a taller rectangle whose height is at most `H` belongs to the
literal frozen rectangle of height `H`. -/
theorem mem_zeroSet_of_abs_im_le {H T : ℝ} {rho : ℂ}
    (hrho : rho ∈ zeroSet 0 T) (hrhoHeight : |rho.im| ≤ H) :
    rho ∈ zeroSet 0 H := by
  change rho ∈ RiemannZeta.GuthMaynard.zerosInRect 0 1 (-T) T at hrho
  rw [RiemannZeta.GuthMaynard.zerosInRect,
    Set.Finite.mem_toFinset, Set.mem_inter_iff] at hrho
  change rho ∈ RiemannZeta.GuthMaynard.zerosInRect 0 1 (-H) H
  rw [RiemannZeta.GuthMaynard.zerosInRect,
    Set.Finite.mem_toFinset, Set.mem_inter_iff]
  refine ⟨(RiemannZeta.GuthMaynard.mem_ZeroRectangle 0 1 (-H) H rho).mpr ?_, hrho.2⟩
  have hrect :=
    (RiemannZeta.GuthMaynard.mem_ZeroRectangle 0 1 (-T) T rho).mp hrho.1
  exact ⟨hrect.1, hrect.2.1, (abs_le.mp hrhoHeight).1,
    (abs_le.mp hrhoHeight).2⟩

/-- The pointwise published theorem extends to a rectangle-uniform theorem
after shrinking its positive constant.  The shrinkage is not an oracle: it
is the explicit minimum of the high-zero constant, the finite low-zero gap,
and the denominator at the source height. -/
theorem exists_vinogradovKorobovRectangleZeroFree_of_pointwise
    {c H : ℝ}
    (hc : 0 < c)
    (hH : Real.exp (Real.exp 1) ≤ H)
    (hPointwise : VinogradovKorobovPointwiseZeroFree c H) :
    ∃ c' : ℝ, 0 < c' ∧ c' ≤ c ∧
      VinogradovKorobovRectangleZeroFree c' H := by
  classical
  have hLowGap : ∀ rho ∈ zeroSet 0 H, 0 < 1 - rho.re := by
    intro rho hrho
    change rho ∈ RiemannZeta.GuthMaynard.zerosInRect 0 1 (-H) H at hrho
    rw [RiemannZeta.GuthMaynard.zerosInRect,
      Set.Finite.mem_toFinset, Set.mem_inter_iff] at hrho
    have hrect :=
      (RiemannZeta.GuthMaynard.mem_ZeroRectangle 0 1 (-H) H rho).mp hrho.1
    have hre : rho.re < 1 := lt_of_le_of_ne hrect.2.1 fun heq =>
      (riemannZeta_ne_zero_of_one_le_re heq.ge) hrho.2
    linarith
  obtain ⟨d, hdPos, hd⟩ :=
    exists_pos_lowerBound_finset (zeroSet 0 H) (fun rho => 1 - rho.re) hLowGap
  let D := vinogradovKorobovDenominator H
  have hDPos : 0 < D := vinogradovKorobovDenominator_pos hH
  let m := min c (min (d * D) D)
  have hmPos : 0 < m := lt_min hc (lt_min (mul_pos hdPos hDPos) hDPos)
  let c' := m / 2
  have hc'Pos : 0 < c' := div_pos hmPos (by norm_num)
  have hc'LeC : c' ≤ c :=
    (div_le_self hmPos.le (by norm_num)).trans (min_le_left _ _)
  refine ⟨c', hc'Pos, hc'LeC, ?_⟩
  intro T hHT
  have hTBase : Real.exp (Real.exp 1) ≤ T := hH.trans hHT
  have hDenomTPos : 0 < vinogradovKorobovDenominator T :=
    vinogradovKorobovDenominator_pos hTBase
  have hDenomMono : D ≤ vinogradovKorobovDenominator T := by
    apply monotoneOn_vinogradovKorobovDenominator
    · exact (le_trans (by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr (by norm_num)) hH)
    · exact (le_trans (by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr (by norm_num)) hTBase)
    · exact hHT
  have hc'LeD : c' ≤ D :=
    (div_le_self hmPos.le (by norm_num)).trans
      ((min_le_right c _).trans (min_le_right _ _))
  have hc'LtDGap : c' < d * D := by
    have hmLe : m ≤ d * D :=
      (min_le_right c _).trans (min_le_left _ _)
    dsimp [c']
    linarith
  have hWidthNonneg : 0 ≤ c' / vinogradovKorobovDenominator T :=
    div_nonneg hc'Pos.le hDenomTPos.le
  have hWidthLeOne : c' / vinogradovKorobovDenominator T ≤ 1 := by
    rw [div_le_one hDenomTPos]
    exact hc'LeD.trans hDenomMono
  refine ⟨hWidthNonneg, hWidthLeOne, ?_⟩
  intro rho hrho
  by_cases hrhoHigh : H ≤ |rho.im|
  · have hHigh := vinogradovKorobov_high_zero_uniform hc.le hH hPointwise hrho hrhoHigh
    have hWidthMono :
        c' / vinogradovKorobovDenominator T ≤
          c / vinogradovKorobovDenominator T :=
      (div_le_div_iff_of_pos_right hDenomTPos).mpr hc'LeC
    exact hHigh.trans_le (by linarith)
  · have hrhoLow : rho ∈ zeroSet 0 H :=
      mem_zeroSet_of_abs_im_le hrho (le_of_lt (lt_of_not_ge hrhoHigh))
    have hGap := hd rho hrhoLow
    have hWidthAtH : c' / D < d := by
      rw [div_lt_iff₀ hDPos]
      exact hc'LtDGap
    have hWidthMono :
        c' / vinogradovKorobovDenominator T ≤ c' / D :=
      div_le_div_of_nonneg_left hc'Pos.le hDPos hDenomMono
    linarith

/-- Raising the left edge only removes zeros from the frozen finite
rectangle. -/
theorem zeroSet_subset_zeroSet_zero {sigma T : ℝ} (hsigma : 0 ≤ sigma) :
    zeroSet sigma T ⊆ zeroSet 0 T := by
  intro rho hrho
  change rho ∈ RiemannZeta.GuthMaynard.zerosInRect sigma 1 (-T) T at hrho
  change rho ∈ RiemannZeta.GuthMaynard.zerosInRect 0 1 (-T) T
  rw [RiemannZeta.GuthMaynard.zerosInRect,
    Set.Finite.mem_toFinset, Set.mem_inter_iff] at hrho ⊢
  have hrect :=
    (RiemannZeta.GuthMaynard.mem_ZeroRectangle sigma 1 (-T) T rho).mp
      hrho.1
  refine ⟨(RiemannZeta.GuthMaynard.mem_ZeroRectangle 0 1 (-T) T rho).mpr
    ⟨hsigma.trans hrect.1, hrect.2⟩, hrho.2⟩

/-- The rectangle zero-free theorem kills the actual finite zero set after
moving its left edge to `1-eta`. -/
theorem zeroSet_eq_empty_of_vinogradovKorobovRectangleZeroFree
    {c T₀ eta T : ℝ}
    (hZeroFree : VinogradovKorobovRectangleZeroFree c T₀)
    (hetaOne : eta ≤ 1)
    (hT₀ : T₀ ≤ T)
    (heta : eta ≤ c / vinogradovKorobovDenominator T) :
    zeroSet (1 - eta) T = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro rho hrho
  have hrhoZero : rho ∈ zeroSet 0 T :=
    zeroSet_subset_zeroSet_zero (by linarith) hrho
  have hright := (hZeroFree hT₀).2.2 hrhoZero
  change rho ∈ RiemannZeta.GuthMaynard.zerosInRect (1 - eta) 1 (-T) T at hrho
  rw [RiemannZeta.GuthMaynard.zerosInRect,
    Set.Finite.mem_toFinset, Set.mem_inter_iff] at hrho
  have hrect :=
    (RiemannZeta.GuthMaynard.mem_ZeroRectangle
      (1 - eta) 1 (-T) T rho).mp hrho.1
  have hleft : 1 - c / vinogradovKorobovDenominator T ≤ 1 - eta := by
    linarith
  linarith

/-- Exact source-to-consumer bridge for equation (2.6): the direct
rectangle zero-free theorem implies vanishing of the actual
analytic-multiplicity-weighted zero count. -/
theorem vinogradovKorobovCountVanishing_of_rectangleZeroFree
    {c T₀ : ℝ}
    (hZeroFree : VinogradovKorobovRectangleZeroFree c T₀) :
    VinogradovKorobovCountVanishing c T₀ := by
  intro eta T hetaPos hT₀ heta
  have hetaOne : eta ≤ 1 := heta.trans (hZeroFree hT₀).2.1
  have hset :=
    zeroSet_eq_empty_of_vinogradovKorobovRectangleZeroFree hZeroFree
      hetaOne hT₀
      (by simpa [vinogradovKorobovDenominator] using heta)
  rw [zeroCount_eq_weighted_sum, hset]
  simp

end GafniTao
