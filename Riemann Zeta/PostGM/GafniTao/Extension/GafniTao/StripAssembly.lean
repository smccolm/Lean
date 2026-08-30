import GafniTao.FourthMoment
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Half-open strip assembly

This file begins the exact finite assembly in Gafni--Tao equation (2.7).
Unlike the closed rectangles convenient for zero counting, the source
partition uses the disjoint half-open strips `[j/J,(j+1)/J)`.  We assign every
zero to its unique strip by a natural floor, prove that the line `Re rho = 1`
contributes no zero, recover the complete zero sum, and prove the precise
finite pigeonhole threshold `delta/J`.
-/

open Complex Finset Set
open Asymptotics Filter Topology
open scoped BigOperators

namespace GafniTao

open RiemannZeta.GuthMaynard

/-- The source strip index `floor (J * Re rho)`. -/
noncomputable def zeroStripIndex (J : ℕ) (rho : ℂ) : ℕ :=
  ⌊(J : ℝ) * rho.re⌋₊

/-- The exact half-open strip cut out of the finite full zero set. -/
noncomputable def halfOpenStripZeros (J j : ℕ) (T : ℝ) : Finset ℂ :=
  (zeroSet 0 T).filter (fun rho => zeroStripIndex J rho = j)

/-- Endpoint form of a source half-open strip. -/
noncomputable def halfOpenZeroStrip
    (sigmaLower sigmaUpper T : ℝ) : Finset ℂ :=
  (zeroSet 0 T).filter
    (fun rho => sigmaLower ≤ rho.re ∧ rho.re < sigmaUpper)

/-- The equation-(2.4) sum over the exact half-open strip indexed by `j`. -/
noncomputable def halfOpenStripIncrementSum
    (J j : ℕ) (T tau x : ℝ) : ℂ :=
  ∑ rho ∈ halfOpenStripZeros J j T,
    (zeroMultiplicity rho : ℂ) * zeroIncrementTerm tau x rho

/-- Equation-(2.4) sum over a half-open strip with literal real endpoints. -/
noncomputable def halfOpenZeroStripIncrementSum
    (sigmaLower sigmaUpper T tau x : ℝ) : ℂ :=
  ∑ rho ∈ halfOpenZeroStrip sigmaLower sigmaUpper T,
    (zeroMultiplicity rho : ℂ) * zeroIncrementTerm tau x rho

/-- The full equation-(2.4) sum over all zeros with `0 <= Re rho <= 1`. -/
noncomputable def fullZeroIncrementSum (T tau x : ℝ) : ℂ :=
  ∑ rho ∈ zeroSet 0 T,
    (zeroMultiplicity rho : ℂ) * zeroIncrementTerm tau x rho

/-- Membership in the frozen zero set exposes the rectangle inequalities and
the actual zeta-zero equation. -/
theorem mem_zeroSet_zero_data {T : ℝ} {rho : ℂ}
    (hrho : rho ∈ zeroSet 0 T) :
    0 ≤ rho.re ∧ rho.re ≤ 1 ∧ -T ≤ rho.im ∧ rho.im ≤ T ∧
      riemannZeta rho = 0 := by
  change rho ∈ RiemannZeta.GuthMaynard.zerosInRect 0 1 (-T) T at hrho
  rw [RiemannZeta.GuthMaynard.zerosInRect,
    Set.Finite.mem_toFinset, Set.mem_inter_iff] at hrho
  have hrect :=
    (RiemannZeta.GuthMaynard.mem_ZeroRectangle 0 1 (-T) T rho).mp hrho.1
  exact ⟨hrect.1, hrect.2.1, hrect.2.2.1, hrect.2.2.2, hrho.2⟩

/-- There are no members of the actual zero set on `Re rho = 1`. -/
theorem re_lt_one_of_mem_zeroSet {T : ℝ} {rho : ℂ}
    (hrho : rho ∈ zeroSet 0 T) : rho.re < 1 := by
  have hdata := mem_zeroSet_zero_data hrho
  exact lt_of_le_of_ne hdata.2.1 fun hre =>
    (riemannZeta_ne_zero_of_one_le_re hre.ge) hdata.2.2.2.2

/-- Every source zero has an index in `Finset.range J`. -/
theorem zeroStripIndex_lt {J : ℕ} (hJ : 0 < J) {T : ℝ} {rho : ℂ}
    (hrho : rho ∈ zeroSet 0 T) : zeroStripIndex J rho < J := by
  have hreNonneg : 0 ≤ rho.re := (mem_zeroSet_zero_data hrho).1
  have hprodNonneg : 0 ≤ (J : ℝ) * rho.re := mul_nonneg (by positivity) hreNonneg
  rw [zeroStripIndex, Nat.floor_lt hprodNonneg]
  have hre := re_lt_one_of_mem_zeroSet hrho
  exact (mul_lt_mul_of_pos_left hre (by exact_mod_cast hJ)).trans_eq (by ring)

/-- The floor index is equivalent to the literal source interval
`j/J <= Re rho < (j+1)/J`. -/
theorem zeroStripIndex_eq_iff
    {J j : ℕ} (hJ : 0 < J) {rho : ℂ} (hre : 0 ≤ rho.re) :
    zeroStripIndex J rho = j ↔
      (j : ℝ) / J ≤ rho.re ∧ rho.re < (j + 1 : ℕ) / J := by
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  have hprod : 0 ≤ (J : ℝ) * rho.re := mul_nonneg hJr.le hre
  constructor
  · intro hidx
    have hlower : (j : ℝ) ≤ (J : ℝ) * rho.re := by
      rw [← hidx]
      exact Nat.floor_le hprod
    have hupper : (J : ℝ) * rho.re < (j : ℝ) + 1 := by
      rw [← hidx]
      exact Nat.lt_floor_add_one ((J : ℝ) * rho.re)
    constructor
    · exact (div_le_iff₀ hJr).2 (by simpa [mul_comm] using hlower)
    · rw [lt_div_iff₀ hJr]
      simpa [Nat.cast_add, Nat.cast_one, mul_comm] using hupper
  · rintro ⟨hlower, hupper⟩
    have hlower' : (j : ℝ) ≤ (J : ℝ) * rho.re := by
      exact (div_le_iff₀ hJr).1 hlower |>.trans_eq (by ring)
    have hupper' : (J : ℝ) * rho.re < (j + 1 : ℕ) := by
      simpa [mul_comm] using (lt_div_iff₀ hJr).1 hupper
    apply Nat.eq_of_le_of_lt_succ
    · exact Nat.le_floor hlower'
    · exact (Nat.floor_lt hprod).2 (by exact_mod_cast hupper')

theorem mem_halfOpenStripZeros_iff
    {J j : ℕ} (hJ : 0 < J) {T : ℝ} {rho : ℂ} :
    rho ∈ halfOpenStripZeros J j T ↔
      rho ∈ zeroSet 0 T ∧
        (j : ℝ) / J ≤ rho.re ∧ rho.re < (j + 1 : ℕ) / J := by
  rw [halfOpenStripZeros, Finset.mem_filter]
  constructor
  · rintro ⟨hrho, hidx⟩
    exact ⟨hrho,
      (zeroStripIndex_eq_iff hJ (mem_zeroSet_zero_data hrho).1).mp hidx⟩
  · rintro ⟨hrho, hinterval⟩
    exact ⟨hrho,
      (zeroStripIndex_eq_iff hJ (mem_zeroSet_zero_data hrho).1).mpr hinterval⟩

theorem halfOpenStripZeros_eq_endpointStrip
    {J : ℕ} (hJ : 0 < J) (j : ℕ) (T : ℝ) :
    halfOpenStripZeros J j T =
      halfOpenZeroStrip ((j : ℝ) / J) ((j + 1 : ℕ) / J) T := by
  ext rho
  rw [mem_halfOpenStripZeros_iff hJ, halfOpenZeroStrip, Finset.mem_filter]

theorem halfOpenStripIncrementSum_eq_endpointSum
    {J : ℕ} (hJ : 0 < J) (j : ℕ) (T tau x : ℝ) :
    halfOpenStripIncrementSum J j T tau x =
      halfOpenZeroStripIncrementSum
        ((j : ℝ) / J) ((j + 1 : ℕ) / J) T tau x := by
  rw [halfOpenStripIncrementSum, halfOpenZeroStripIncrementSum,
    halfOpenStripZeros_eq_endpointStrip hJ]

/-- A closed zero rectangle is the disjoint union of its half-open part and
its upper boundary. -/
theorem zerosInRect_eq_halfOpen_union_upperBoundary
    {sigmaLower sigmaUpper T : ℝ}
    (hsigmaLower : 0 ≤ sigmaLower) (hsigmaOrder : sigmaLower ≤ sigmaUpper)
    (hsigmaUpper : sigmaUpper ≤ 1) :
    RiemannZeta.GuthMaynard.zerosInRect
        sigmaLower sigmaUpper (-T) T =
      halfOpenZeroStrip sigmaLower sigmaUpper T ∪
        RiemannZeta.GuthMaynard.zerosInRect
          sigmaUpper sigmaUpper (-T) T := by
  ext rho
  simp only [Finset.mem_union, halfOpenZeroStrip, Finset.mem_filter]
  constructor
  · intro hrho
    have hrhoData : rho ∈ zeroSet 0 T := by
      apply RiemannZeta.GuthMaynard.zerosInRect_subset_of_rect_subset
        sigmaLower sigmaUpper (-T) T 0 1 (-T) T
      · exact RiemannZeta.GuthMaynard.ZeroRectangle_subset
          sigmaLower sigmaUpper (-T) T 0 1 (-T) T
            hsigmaLower hsigmaUpper le_rfl le_rfl
      · exact hrho
    have hrhoRect : rho ∈ RiemannZeta.GuthMaynard.ZeroRectangle
        sigmaLower sigmaUpper (-T) T := by
      rw [RiemannZeta.GuthMaynard.zerosInRect,
        Set.Finite.mem_toFinset, Set.mem_inter_iff] at hrho
      exact hrho.1
    have hbounds :=
      (RiemannZeta.GuthMaynard.mem_ZeroRectangle
        sigmaLower sigmaUpper (-T) T rho).mp hrhoRect
    rcases lt_or_eq_of_le hbounds.2.1 with hlt | heq
    · exact Or.inl ⟨hrhoData, hbounds.1, hlt⟩
    · right
      rw [RiemannZeta.GuthMaynard.zerosInRect,
        Set.Finite.mem_toFinset, Set.mem_inter_iff]
      constructor
      · exact (RiemannZeta.GuthMaynard.mem_ZeroRectangle
          sigmaUpper sigmaUpper (-T) T rho).mpr
            ⟨heq.ge, heq.le, hbounds.2.2.1, hbounds.2.2.2⟩
      · exact (mem_zeroSet_zero_data hrhoData).2.2.2.2
  · rintro (hrho | hrho)
    · rcases hrho with ⟨hrhoFull, hlower, hupper⟩
      rw [RiemannZeta.GuthMaynard.zerosInRect,
        Set.Finite.mem_toFinset, Set.mem_inter_iff]
      have hdata := mem_zeroSet_zero_data hrhoFull
      constructor
      · exact (RiemannZeta.GuthMaynard.mem_ZeroRectangle
          sigmaLower sigmaUpper (-T) T rho).mpr
            ⟨hlower, hupper.le, hdata.2.2.1, hdata.2.2.2.1⟩
      · exact hdata.2.2.2.2
    · apply RiemannZeta.GuthMaynard.zerosInRect_subset_of_rect_subset
        sigmaUpper sigmaUpper (-T) T sigmaLower sigmaUpper (-T) T
      · exact RiemannZeta.GuthMaynard.ZeroRectangle_subset
          sigmaUpper sigmaUpper (-T) T sigmaLower sigmaUpper (-T) T
            hsigmaOrder le_rfl le_rfl le_rfl
      · exact hrho

theorem disjoint_halfOpenZeroStrip_upperBoundary
    (sigmaLower sigmaUpper T : ℝ) :
    Disjoint (halfOpenZeroStrip sigmaLower sigmaUpper T)
      (RiemannZeta.GuthMaynard.zerosInRect
        sigmaUpper sigmaUpper (-T) T) := by
  rw [Finset.disjoint_left]
  intro rho hrhoOpen hrhoBoundary
  have hopen := (Finset.mem_filter.mp hrhoOpen).2.2
  have hrect : rho ∈ RiemannZeta.GuthMaynard.ZeroRectangle
      sigmaUpper sigmaUpper (-T) T := by
    rw [RiemannZeta.GuthMaynard.zerosInRect,
      Set.Finite.mem_toFinset, Set.mem_inter_iff] at hrhoBoundary
    exact hrhoBoundary.1
  have heq :=
    (RiemannZeta.GuthMaynard.mem_ZeroRectangle
      sigmaUpper sigmaUpper (-T) T rho).mp hrect
  exact (not_lt_of_ge heq.1) hopen

/-- Exact sum identity separating an internal upper boundary from the source
half-open strip. -/
theorem zeroStripIncrementSum_eq_halfOpen_add_upperBoundary
    {sigmaLower sigmaUpper T tau x : ℝ}
    (hsigmaLower : 0 ≤ sigmaLower) (hsigmaOrder : sigmaLower ≤ sigmaUpper)
    (hsigmaUpper : sigmaUpper ≤ 1) :
    zeroStripIncrementSum sigmaLower sigmaUpper T tau x =
      halfOpenZeroStripIncrementSum sigmaLower sigmaUpper T tau x +
        zeroStripIncrementSum sigmaUpper sigmaUpper T tau x := by
  classical
  unfold zeroStripIncrementSum halfOpenZeroStripIncrementSum
  rw [zerosInRect_eq_halfOpen_union_upperBoundary
    hsigmaLower hsigmaOrder hsigmaUpper]
  exact Finset.sum_union
    (disjoint_halfOpenZeroStrip_upperBoundary sigmaLower sigmaUpper T)

/-- The source half-open strip sum is the closed strip sum with its upper
boundary removed. -/
theorem halfOpenZeroStripIncrementSum_eq_sub_upperBoundary
    {sigmaLower sigmaUpper T tau x : ℝ}
    (hsigmaLower : 0 ≤ sigmaLower) (hsigmaOrder : sigmaLower ≤ sigmaUpper)
    (hsigmaUpper : sigmaUpper ≤ 1) :
    halfOpenZeroStripIncrementSum sigmaLower sigmaUpper T tau x =
      zeroStripIncrementSum sigmaLower sigmaUpper T tau x -
        zeroStripIncrementSum sigmaUpper sigmaUpper T tau x := by
  have h := zeroStripIncrementSum_eq_halfOpen_add_upperBoundary
    (T := T) (tau := tau) (x := x)
    hsigmaLower hsigmaOrder hsigmaUpper
  exact eq_sub_of_add_eq h.symm

/-- Half-open version of the logarithmic finite zero sum. -/
noncomputable def logarithmicHalfOpenZeroStripSum
    (sigmaLower sigmaUpper T tau X u : ℝ) : ℂ :=
  ∑ rho ∈ halfOpenZeroStrip sigmaLower sigmaUpper T,
    stripZeroCoefficient tau X rho * Complex.exp ((u : ℂ) * rho)

theorem logarithmicZeroStripSum_eq_halfOpen_add_upperBoundary
    {sigmaLower sigmaUpper T tau X u : ℝ}
    (hsigmaLower : 0 ≤ sigmaLower) (hsigmaOrder : sigmaLower ≤ sigmaUpper)
    (hsigmaUpper : sigmaUpper ≤ 1) :
    logarithmicZeroStripSum sigmaLower sigmaUpper T tau X u =
      logarithmicHalfOpenZeroStripSum sigmaLower sigmaUpper T tau X u +
        logarithmicZeroStripSum sigmaUpper sigmaUpper T tau X u := by
  classical
  unfold logarithmicZeroStripSum logarithmicHalfOpenZeroStripSum
  rw [zerosInRect_eq_halfOpen_union_upperBoundary
    hsigmaLower hsigmaOrder hsigmaUpper]
  exact Finset.sum_union
    (disjoint_halfOpenZeroStrip_upperBoundary sigmaLower sigmaUpper T)

theorem halfOpenZeroStripIncrementSum_mul_exp_eq_logarithmic
    {sigmaLower sigmaUpper T tau X u : ℝ}
    (htau : 0 < tau) (hX : 0 ≤ X) :
    halfOpenZeroStripIncrementSum sigmaLower sigmaUpper T tau
        (X * Real.exp u) =
      logarithmicHalfOpenZeroStripSum
        sigmaLower sigmaUpper T tau X u := by
  rw [halfOpenZeroStripIncrementSum]
  unfold logarithmicHalfOpenZeroStripSum stripZeroCoefficient
  apply Finset.sum_congr rfl
  intro rho hrho
  rw [zeroIncrementTerm_eq_cpow_mul_coefficient htau
    (mul_nonneg hX (Real.exp_pos u).le)]
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hX
    (Real.exp_pos u).le]
  have hexp : ((Real.exp u : ℝ) : ℂ) ^ rho =
      Complex.exp ((u : ℂ) * rho) := by
    rw [Complex.cpow_def_of_ne_zero]
    · have hlog : Complex.log ((Real.exp u : ℝ) : ℂ) = (u : ℂ) := by
        have h := Complex.log_ofReal_mul (Real.exp_pos u)
          (x := (1 : ℂ)) one_ne_zero
        simpa [Real.log_exp] using h
      rw [hlog]
    · exact Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero u)
  rw [hexp]
  ring

/-- Normalized physical second moment for the literal half-open strip. -/
noncomputable def halfOpenZeroStripPhysicalSecondMoment
    (sigmaLower sigmaUpper T tau X : ℝ) : ℝ :=
  (1 / X) * ∫ x : ℝ in X..2 * X,
    ‖halfOpenZeroStripIncrementSum sigmaLower sigmaUpper T tau x‖ ^ 2

/-- Normalized physical fourth moment for the literal half-open strip. -/
noncomputable def halfOpenZeroStripPhysicalFourthMoment
    (sigmaLower sigmaUpper T tau X : ℝ) : ℝ :=
  (1 / X) * ∫ x : ℝ in X..2 * X,
    ‖halfOpenZeroStripIncrementSum sigmaLower sigmaUpper T tau x‖ ^ 4

theorem halfOpenZeroStripPhysicalSecondMoment_nonneg
    {sigmaLower sigmaUpper T tau X : ℝ} (hX : 0 < X) :
    0 ≤ halfOpenZeroStripPhysicalSecondMoment
      sigmaLower sigmaUpper T tau X := by
  unfold halfOpenZeroStripPhysicalSecondMoment
  apply mul_nonneg (one_div_nonneg.mpr hX.le)
  apply intervalIntegral.integral_nonneg (by linarith)
  intro x hx
  positivity

theorem halfOpenZeroStripPhysicalFourthMoment_nonneg
    {sigmaLower sigmaUpper T tau X : ℝ} (hX : 0 < X) :
    0 ≤ halfOpenZeroStripPhysicalFourthMoment
      sigmaLower sigmaUpper T tau X := by
  unfold halfOpenZeroStripPhysicalFourthMoment
  apply mul_nonneg (one_div_nonneg.mpr hX.le)
  apply intervalIntegral.integral_nonneg (by linarith)
  intro x hx
  positivity

theorem halfOpenZeroStripPhysicalSecondMoment_eq_logarithmic
    {sigmaLower sigmaUpper T tau X : ℝ}
    (htau : 0 < tau) (hX : 0 < X) :
    halfOpenZeroStripPhysicalSecondMoment
        sigmaLower sigmaUpper T tau X =
      ∫ u : ℝ in 0..Real.log 2,
        ‖logarithmicHalfOpenZeroStripSum
          sigmaLower sigmaUpper T tau X u‖ ^ 2 * Real.exp u := by
  let g : ℝ → ℝ := fun x =>
    ‖halfOpenZeroStripIncrementSum sigmaLower sigmaUpper T tau x‖ ^ 2
  let f : ℝ → ℝ := fun u => X * Real.exp u
  have hSub :
      (∫ u : ℝ in 0..Real.log 2, (g ∘ f) u * f u) =
        ∫ x : ℝ in X..2 * X, g x := by
    have hChange := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
      (a := (0 : ℝ)) (b := Real.log 2) (f := f) (f' := f) (g := g)
      (by fun_prop)
      (by
        intro u hu
        exact (Real.hasDerivAt_exp u).const_mul X)
      (by
        intro u hu
        exact mul_nonneg hX.le (Real.exp_pos u).le)
    simpa [f, Real.exp_log (by norm_num : (0 : ℝ) < 2), mul_comm] using hChange
  unfold halfOpenZeroStripPhysicalSecondMoment
  change (1 / X) * (∫ x : ℝ in X..2 * X, g x) = _
  rw [← hSub]
  have hFactor :
      (∫ u : ℝ in 0..Real.log 2, (g ∘ f) u * f u) =
        X * ∫ u : ℝ in 0..Real.log 2, (g ∘ f) u * Real.exp u := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u hu
    simp only [f]
    ring
  rw [hFactor]
  field_simp [hX.ne']
  apply intervalIntegral.integral_congr
  intro u hu
  change ‖halfOpenZeroStripIncrementSum sigmaLower sigmaUpper T tau
      (X * Real.exp u)‖ ^ 2 * Real.exp u = _
  rw [halfOpenZeroStripIncrementSum_mul_exp_eq_logarithmic htau hX.le]

theorem halfOpenZeroStripPhysicalFourthMoment_eq_logarithmic
    {sigmaLower sigmaUpper T tau X : ℝ}
    (htau : 0 < tau) (hX : 0 < X) :
    halfOpenZeroStripPhysicalFourthMoment
        sigmaLower sigmaUpper T tau X =
      ∫ u : ℝ in 0..Real.log 2,
        ‖logarithmicHalfOpenZeroStripSum
          sigmaLower sigmaUpper T tau X u‖ ^ 4 * Real.exp u := by
  let g : ℝ → ℝ := fun x =>
    ‖halfOpenZeroStripIncrementSum sigmaLower sigmaUpper T tau x‖ ^ 4
  let f : ℝ → ℝ := fun u => X * Real.exp u
  have hSub :
      (∫ u : ℝ in 0..Real.log 2, (g ∘ f) u * f u) =
        ∫ x : ℝ in X..2 * X, g x := by
    have hChange := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
      (a := (0 : ℝ)) (b := Real.log 2) (f := f) (f' := f) (g := g)
      (by fun_prop)
      (by
        intro u hu
        exact (Real.hasDerivAt_exp u).const_mul X)
      (by
        intro u hu
        exact mul_nonneg hX.le (Real.exp_pos u).le)
    simpa [f, Real.exp_log (by norm_num : (0 : ℝ) < 2), mul_comm] using hChange
  unfold halfOpenZeroStripPhysicalFourthMoment
  change (1 / X) * (∫ x : ℝ in X..2 * X, g x) = _
  rw [← hSub]
  have hFactor :
      (∫ u : ℝ in 0..Real.log 2, (g ∘ f) u * f u) =
        X * ∫ u : ℝ in 0..Real.log 2, (g ∘ f) u * Real.exp u := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u hu
    simp only [f]
    ring
  rw [hFactor]
  field_simp [hX.ne']
  apply intervalIntegral.integral_congr
  intro u hu
  change ‖halfOpenZeroStripIncrementSum sigmaLower sigmaUpper T tau
      (X * Real.exp u)‖ ^ 4 * Real.exp u = _
  rw [halfOpenZeroStripIncrementSum_mul_exp_eq_logarithmic htau hX.le]

theorem norm_logarithmicHalfOpenZeroStripSum_sq_le
    {sigmaLower sigmaUpper T tau X u : ℝ}
    (hsigmaLower : 0 ≤ sigmaLower) (hsigmaOrder : sigmaLower ≤ sigmaUpper)
    (hsigmaUpper : sigmaUpper ≤ 1) :
    ‖logarithmicHalfOpenZeroStripSum
        sigmaLower sigmaUpper T tau X u‖ ^ 2 ≤
      2 * (‖logarithmicZeroStripSum
          sigmaLower sigmaUpper T tau X u‖ ^ 2 +
        ‖logarithmicZeroStripSum
          sigmaUpper sigmaUpper T tau X u‖ ^ 2) := by
  have hsum := logarithmicZeroStripSum_eq_halfOpen_add_upperBoundary
    (T := T) (tau := tau) (X := X) (u := u)
    hsigmaLower hsigmaOrder hsigmaUpper
  have hopen : logarithmicHalfOpenZeroStripSum
      sigmaLower sigmaUpper T tau X u =
        logarithmicZeroStripSum sigmaLower sigmaUpper T tau X u -
          logarithmicZeroStripSum sigmaUpper sigmaUpper T tau X u :=
    eq_sub_of_add_eq hsum.symm
  rw [hopen]
  have hnorm := norm_sub_le
    (logarithmicZeroStripSum sigmaLower sigmaUpper T tau X u)
    (logarithmicZeroStripSum sigmaUpper sigmaUpper T tau X u)
  have hc : 0 ≤ ‖logarithmicZeroStripSum sigmaLower sigmaUpper T tau X u -
      logarithmicZeroStripSum sigmaUpper sigmaUpper T tau X u‖ := norm_nonneg _
  have ha : 0 ≤ ‖logarithmicZeroStripSum
      sigmaLower sigmaUpper T tau X u‖ := norm_nonneg _
  have hb : 0 ≤ ‖logarithmicZeroStripSum
      sigmaUpper sigmaUpper T tau X u‖ := norm_nonneg _
  nlinarith [sq_nonneg
    (‖logarithmicZeroStripSum sigmaLower sigmaUpper T tau X u‖ -
      ‖logarithmicZeroStripSum sigmaUpper sigmaUpper T tau X u‖)]

theorem norm_logarithmicHalfOpenZeroStripSum_fourth_le
    {sigmaLower sigmaUpper T tau X u : ℝ}
    (hsigmaLower : 0 ≤ sigmaLower) (hsigmaOrder : sigmaLower ≤ sigmaUpper)
    (hsigmaUpper : sigmaUpper ≤ 1) :
    ‖logarithmicHalfOpenZeroStripSum
        sigmaLower sigmaUpper T tau X u‖ ^ 4 ≤
      8 * (‖logarithmicZeroStripSum
          sigmaLower sigmaUpper T tau X u‖ ^ 4 +
        ‖logarithmicZeroStripSum
          sigmaUpper sigmaUpper T tau X u‖ ^ 4) := by
  have hsum := logarithmicZeroStripSum_eq_halfOpen_add_upperBoundary
    (T := T) (tau := tau) (X := X) (u := u)
    hsigmaLower hsigmaOrder hsigmaUpper
  have hopen : logarithmicHalfOpenZeroStripSum
      sigmaLower sigmaUpper T tau X u =
        logarithmicZeroStripSum sigmaLower sigmaUpper T tau X u -
          logarithmicZeroStripSum sigmaUpper sigmaUpper T tau X u :=
    eq_sub_of_add_eq hsum.symm
  rw [hopen]
  let a := ‖logarithmicZeroStripSum sigmaLower sigmaUpper T tau X u‖
  let b := ‖logarithmicZeroStripSum sigmaUpper sigmaUpper T tau X u‖
  have hnorm :
      ‖logarithmicZeroStripSum sigmaLower sigmaUpper T tau X u -
        logarithmicZeroStripSum sigmaUpper sigmaUpper T tau X u‖ ≤ a + b :=
    norm_sub_le _ _
  have hpow :
      ‖logarithmicZeroStripSum sigmaLower sigmaUpper T tau X u -
        logarithmicZeroStripSum sigmaUpper sigmaUpper T tau X u‖ ^ 4 ≤
        (a + b) ^ 4 := by
    exact pow_le_pow_left₀ (norm_nonneg _) hnorm 4
  have hpoly : 0 ≤ (a - b) ^ 2 *
      (7 * a ^ 2 + 10 * a * b + 7 * b ^ 2) := by positivity
  have hab : (a + b) ^ 4 ≤ 8 * (a ^ 4 + b ^ 4) := by
    nlinarith
  exact hpow.trans hab

/-- The exact half-open second moment is controlled by a closed strip and its
upper boundary.  The factor `2` is the sharp elementary square loss used to
preserve the source partition without dropping boundary zeros. -/
theorem halfOpenZeroStripPhysicalSecondMoment_le_closed_add_boundary
    {sigmaLower sigmaUpper T tau X : ℝ}
    (hsigmaLower : 0 ≤ sigmaLower) (hsigmaOrder : sigmaLower ≤ sigmaUpper)
    (hsigmaUpper : sigmaUpper ≤ 1) (htau : 0 < tau) (hX : 0 < X) :
    halfOpenZeroStripPhysicalSecondMoment
        sigmaLower sigmaUpper T tau X ≤
      2 * (zeroStripPhysicalSecondMoment
          sigmaLower sigmaUpper T tau X +
        zeroStripPhysicalSecondMoment sigmaUpper sigmaUpper T tau X) := by
  rw [halfOpenZeroStripPhysicalSecondMoment_eq_logarithmic htau hX,
    zeroStripPhysicalSecondMoment_eq_logarithmic htau hX,
    zeroStripPhysicalSecondMoment_eq_logarithmic htau hX]
  let qo : ℝ → ℝ := fun u =>
    ‖logarithmicHalfOpenZeroStripSum
      sigmaLower sigmaUpper T tau X u‖ ^ 2
  let qc : ℝ → ℝ := fun u =>
    ‖logarithmicZeroStripSum sigmaLower sigmaUpper T tau X u‖ ^ 2
  let qb : ℝ → ℝ := fun u =>
    ‖logarithmicZeroStripSum sigmaUpper sigmaUpper T tau X u‖ ^ 2
  have hqo : Continuous qo := by
    unfold qo logarithmicHalfOpenZeroStripSum
    fun_prop
  have hqc : Continuous qc := by
    unfold qc logarithmicZeroStripSum
    fun_prop
  have hqb : Continuous qb := by
    unfold qb logarithmicZeroStripSum
    fun_prop
  have hlogTwo : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  calc
    (∫ u : ℝ in 0..Real.log 2, qo u * Real.exp u) ≤
        ∫ u : ℝ in 0..Real.log 2,
          (2 * (qc u + qb u)) * Real.exp u := by
      apply intervalIntegral.integral_mono_on hlogTwo
        ((hqo.mul Real.continuous_exp).intervalIntegrable 0 (Real.log 2))
        (((continuous_const.mul (hqc.add hqb)).mul
          Real.continuous_exp).intervalIntegrable 0 (Real.log 2))
      intro u hu
      exact mul_le_mul_of_nonneg_right
        (norm_logarithmicHalfOpenZeroStripSum_sq_le
          hsigmaLower hsigmaOrder hsigmaUpper) (Real.exp_pos u).le
    _ = ∫ u : ℝ in 0..Real.log 2,
        2 * (qc u * Real.exp u + qb u * Real.exp u) := by
      apply intervalIntegral.integral_congr
      intro u hu
      ring
    _ = 2 * ∫ u : ℝ in 0..Real.log 2,
        (qc u * Real.exp u + qb u * Real.exp u) := by
      rw [intervalIntegral.integral_const_mul]
    _ = 2 * ((∫ u : ℝ in 0..Real.log 2, qc u * Real.exp u) +
        ∫ u : ℝ in 0..Real.log 2, qb u * Real.exp u) := by
      congr 1
      exact intervalIntegral.integral_add
        ((hqc.mul Real.continuous_exp).intervalIntegrable 0 (Real.log 2))
        ((hqb.mul Real.continuous_exp).intervalIntegrable 0 (Real.log 2))

/-- Fourth-moment analogue of the exact half-open boundary transfer. -/
theorem halfOpenZeroStripPhysicalFourthMoment_le_closed_add_boundary
    {sigmaLower sigmaUpper T tau X : ℝ}
    (hsigmaLower : 0 ≤ sigmaLower) (hsigmaOrder : sigmaLower ≤ sigmaUpper)
    (hsigmaUpper : sigmaUpper ≤ 1) (htau : 0 < tau) (hX : 0 < X) :
    halfOpenZeroStripPhysicalFourthMoment
        sigmaLower sigmaUpper T tau X ≤
      8 * (zeroStripPhysicalFourthMoment
          sigmaLower sigmaUpper T tau X +
        zeroStripPhysicalFourthMoment sigmaUpper sigmaUpper T tau X) := by
  rw [halfOpenZeroStripPhysicalFourthMoment_eq_logarithmic htau hX,
    zeroStripPhysicalFourthMoment_eq_logarithmic htau hX,
    zeroStripPhysicalFourthMoment_eq_logarithmic htau hX]
  let qo : ℝ → ℝ := fun u =>
    ‖logarithmicHalfOpenZeroStripSum
      sigmaLower sigmaUpper T tau X u‖ ^ 4
  let qc : ℝ → ℝ := fun u =>
    ‖logarithmicZeroStripSum sigmaLower sigmaUpper T tau X u‖ ^ 4
  let qb : ℝ → ℝ := fun u =>
    ‖logarithmicZeroStripSum sigmaUpper sigmaUpper T tau X u‖ ^ 4
  have hqo : Continuous qo := by
    unfold qo logarithmicHalfOpenZeroStripSum
    fun_prop
  have hqc : Continuous qc := by
    unfold qc logarithmicZeroStripSum
    fun_prop
  have hqb : Continuous qb := by
    unfold qb logarithmicZeroStripSum
    fun_prop
  have hlogTwo : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  calc
    (∫ u : ℝ in 0..Real.log 2, qo u * Real.exp u) ≤
        ∫ u : ℝ in 0..Real.log 2,
          (8 * (qc u + qb u)) * Real.exp u := by
      apply intervalIntegral.integral_mono_on hlogTwo
        ((hqo.mul Real.continuous_exp).intervalIntegrable 0 (Real.log 2))
        (((continuous_const.mul (hqc.add hqb)).mul
          Real.continuous_exp).intervalIntegrable 0 (Real.log 2))
      intro u hu
      exact mul_le_mul_of_nonneg_right
        (norm_logarithmicHalfOpenZeroStripSum_fourth_le
          hsigmaLower hsigmaOrder hsigmaUpper) (Real.exp_pos u).le
    _ = ∫ u : ℝ in 0..Real.log 2,
        8 * (qc u * Real.exp u + qb u * Real.exp u) := by
      apply intervalIntegral.integral_congr
      intro u hu
      ring
    _ = 8 * ∫ u : ℝ in 0..Real.log 2,
        (qc u * Real.exp u + qb u * Real.exp u) := by
      rw [intervalIntegral.integral_const_mul]
    _ = 8 * ((∫ u : ℝ in 0..Real.log 2, qc u * Real.exp u) +
        ∫ u : ℝ in 0..Real.log 2, qb u * Real.exp u) := by
      congr 1
      exact intervalIntegral.integral_add
        ((hqc.mul Real.continuous_exp).intervalIntegrable 0 (Real.log 2))
        ((hqb.mul Real.continuous_exp).intervalIntegrable 0 (Real.log 2))

/-- Raising the real-part cutoff shrinks the actual finite zero set. -/
theorem zeroSet_subset_of_sigma_le {sigmaLower sigmaUpper T : ℝ}
    (hsigma : sigmaLower ≤ sigmaUpper) :
    zeroSet sigmaUpper T ⊆ zeroSet sigmaLower T := by
  apply RiemannZeta.GuthMaynard.zerosInRect_subset_of_rect_subset
    sigmaUpper 1 (-T) T sigmaLower 1 (-T) T
  exact RiemannZeta.GuthMaynard.ZeroRectangle_subset
    sigmaUpper 1 (-T) T sigmaLower 1 (-T) T hsigma le_rfl le_rfl le_rfl

theorem zeroCount_anti_sigma {sigmaLower sigmaUpper T : ℝ}
    (hsigma : sigmaLower ≤ sigmaUpper) :
    zeroCount sigmaUpper T ≤ zeroCount sigmaLower T := by
  rw [zeroCount_eq_weighted_sum, zeroCount_eq_weighted_sum]
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (zeroSet_subset_of_sigma_le hsigma)
  intro rho hrho hnot
  exact Nat.zero_le _

/-- Pointwise half-open form of Lemma 2.2.  The upper boundary removed from
the closed strip is bounded using the same lower-edge zero count, so no
unrelated boundary density hypothesis is introduced. -/
theorem norm_halfOpenZeroStripIncrementSum_le_physicalMajorant
    {J theta sigmaLower sigmaUpper X x : ℝ}
    (hX : 1 ≤ X) (hxLower : X ≤ x) (hxUpper : x ≤ 2 * X)
    (hsigmaLowerPos : 0 < sigmaLower)
    (hsigmaOrder : sigmaLower ≤ sigmaUpper)
    (hsigmaUpper : sigmaUpper ≤ 1) :
    ‖halfOpenZeroStripIncrementSum sigmaLower sigmaUpper
        (explicitFormulaHeight J theta X) (localTau X theta) x‖ ≤
      2 * 2 ^ sigmaUpper *
        zeroStripPhysicalMajorant J theta sigmaLower sigmaUpper X := by
  have hsigmaUpperNonneg : 0 ≤ sigmaUpper :=
    hsigmaLowerPos.le.trans hsigmaOrder
  rw [halfOpenZeroStripIncrementSum_eq_sub_upperBoundary
    hsigmaLowerPos.le hsigmaOrder hsigmaUpper]
  have hClosed := norm_zeroStripIncrementSum_le_physicalMajorant
    (J := J) (theta := theta) hX hxLower hxUpper hsigmaLowerPos
      hsigmaUpperNonneg hsigmaUpper
  have hBoundary := norm_zeroStripIncrementSum_le_physicalMajorant
    (J := J) (theta := theta) (sigmaLower := sigmaUpper)
      (sigmaUpper := sigmaUpper) hX hxLower hxUpper
      (hsigmaLowerPos.trans_le hsigmaOrder) hsigmaUpperNonneg hsigmaUpper
  have hMajorantMono :
      zeroStripPhysicalMajorant J theta sigmaUpper sigmaUpper X ≤
        zeroStripPhysicalMajorant J theta sigmaLower sigmaUpper X := by
    unfold zeroStripPhysicalMajorant
    have hCount :
        (zeroCount sigmaUpper (explicitFormulaHeight J theta X) : ℝ) ≤
          (zeroCount sigmaLower (explicitFormulaHeight J theta X) : ℝ) := by
      exact_mod_cast zeroCount_anti_sigma
        (T := explicitFormulaHeight J theta X) hsigmaOrder
    exact mul_le_mul_of_nonneg_left hCount (Real.rpow_nonneg (by positivity) _)
  calc
    ‖zeroStripIncrementSum sigmaLower sigmaUpper
          (explicitFormulaHeight J theta X) (localTau X theta) x -
        zeroStripIncrementSum sigmaUpper sigmaUpper
          (explicitFormulaHeight J theta X) (localTau X theta) x‖ ≤
        ‖zeroStripIncrementSum sigmaLower sigmaUpper
          (explicitFormulaHeight J theta X) (localTau X theta) x‖ +
        ‖zeroStripIncrementSum sigmaUpper sigmaUpper
          (explicitFormulaHeight J theta X) (localTau X theta) x‖ :=
      norm_sub_le _ _
    _ ≤ 2 ^ sigmaUpper *
          zeroStripPhysicalMajorant J theta sigmaLower sigmaUpper X +
        2 ^ sigmaUpper *
          zeroStripPhysicalMajorant J theta sigmaUpper sigmaUpper X :=
      add_le_add hClosed hBoundary
    _ ≤ 2 ^ sigmaUpper *
          zeroStripPhysicalMajorant J theta sigmaLower sigmaUpper X +
        2 ^ sigmaUpper *
          zeroStripPhysicalMajorant J theta sigmaLower sigmaUpper X := by
      gcongr
    _ = 2 * 2 ^ sigmaUpper *
          zeroStripPhysicalMajorant J theta sigmaLower sigmaUpper X := by ring

/-- Literal supremum of the source half-open strip on the physical interval. -/
noncomputable def halfOpenZeroStripPhysicalSup
    (J theta sigmaLower sigmaUpper X : ℝ) : ℝ :=
  sSup ((fun x : ℝ =>
    ‖halfOpenZeroStripIncrementSum sigmaLower sigmaUpper
      (explicitFormulaHeight J theta X) (localTau X theta) x‖) ''
        Set.Icc X (2 * X))

theorem halfOpenZeroStripPhysicalSup_le_majorant
    {J theta sigmaLower sigmaUpper X : ℝ}
    (hX : 1 ≤ X) (hsigmaLowerPos : 0 < sigmaLower)
    (hsigmaOrder : sigmaLower ≤ sigmaUpper)
    (hsigmaUpper : sigmaUpper ≤ 1) :
    halfOpenZeroStripPhysicalSup J theta sigmaLower sigmaUpper X ≤
      2 * 2 ^ sigmaUpper *
        zeroStripPhysicalMajorant J theta sigmaLower sigmaUpper X := by
  unfold halfOpenZeroStripPhysicalSup
  apply csSup_le
  · refine ⟨‖halfOpenZeroStripIncrementSum sigmaLower sigmaUpper
        (explicitFormulaHeight J theta X) (localTau X theta) X‖, ?_⟩
    exact ⟨X, ⟨le_rfl, by nlinarith⟩, rfl⟩
  · intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact norm_halfOpenZeroStripIncrementSum_le_physicalMajorant
      hX hx.1 hx.2 hsigmaLowerPos hsigmaOrder hsigmaUpper

theorem norm_halfOpenZeroStripIncrementSum_le_physicalSup
    {J theta sigmaLower sigmaUpper X x : ℝ}
    (hX : 1 ≤ X) (hxLower : X ≤ x) (hxUpper : x ≤ 2 * X)
    (hsigmaLowerPos : 0 < sigmaLower)
    (hsigmaOrder : sigmaLower ≤ sigmaUpper)
    (hsigmaUpper : sigmaUpper ≤ 1) :
    ‖halfOpenZeroStripIncrementSum sigmaLower sigmaUpper
        (explicitFormulaHeight J theta X) (localTau X theta) x‖ ≤
      halfOpenZeroStripPhysicalSup J theta sigmaLower sigmaUpper X := by
  unfold halfOpenZeroStripPhysicalSup
  apply le_csSup
  · refine ⟨2 * 2 ^ sigmaUpper *
      zeroStripPhysicalMajorant J theta sigmaLower sigmaUpper X, ?_⟩
    intro y hy
    rcases hy with ⟨z, hz, rfl⟩
    exact norm_halfOpenZeroStripIncrementSum_le_physicalMajorant
      (J := J) (theta := theta) hX hz.1 hz.2 hsigmaLowerPos
        hsigmaOrder hsigmaUpper
  · exact ⟨x, ⟨hxLower, hxUpper⟩, rfl⟩

/-- Half-open source-form Lemma 2.2.  Its proof consumes the literal strip
sum and only the actual density envelope at the strip's lower edge. -/
theorem halfOpenZeroStripPhysicalSup_epsilonBound
    {J theta sigmaLower sigmaUpper a : ℝ}
    (hJ : 0 < J) (hthetaUpper : theta < 1)
    (ha : 0 ≤ a) (hsigmaLowerPos : 0 < sigmaLower)
    (hsigmaOrder : sigmaLower ≤ sigmaUpper)
    (hsigmaUpper : sigmaUpper ≤ 1)
    (hDensity : ZeroDensityEnvelope sigmaLower a) :
    EpsilonExponentBound
      (halfOpenZeroStripPhysicalSup J theta sigmaLower sigmaUpper)
      ((1 - theta) * (a * (1 - sigmaLower)) + theta + sigmaUpper - 1) := by
  have hMajorant := zeroStripPhysicalMajorant_epsilonBound
    (sigmaUpper := sigmaUpper) hJ hthetaUpper ha
      (hsigmaOrder.trans hsigmaUpper) hDensity
  have hSupToMajorant :
      RiemannZeta.GuthMaynard.EpsilonPowerBound
        (halfOpenZeroStripPhysicalSup J theta sigmaLower sigmaUpper)
        (zeroStripPhysicalMajorant J theta sigmaLower sigmaUpper) := by
    intro eps heps
    have hFixed :
        (fun X : ℝ =>
          |halfOpenZeroStripPhysicalSup J theta sigmaLower sigmaUpper X|) =O[atTop]
          (fun X : ℝ =>
            |zeroStripPhysicalMajorant J theta sigmaLower sigmaUpper X|) := by
      apply IsBigO.of_bound (2 * 2 ^ sigmaUpper)
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
      have hSupLe := halfOpenZeroStripPhysicalSup_le_majorant
        (J := J) (theta := theta) hX hsigmaLowerPos hsigmaOrder hsigmaUpper
      have hMajorantNonneg :
          0 ≤ zeroStripPhysicalMajorant J theta sigmaLower sigmaUpper X := by
        unfold zeroStripPhysicalMajorant
        positivity
      have hSetBounded : BddAbove
          ((fun x : ℝ =>
            ‖halfOpenZeroStripIncrementSum sigmaLower sigmaUpper
              (explicitFormulaHeight J theta X) (localTau X theta) x‖) ''
                Set.Icc X (2 * X)) := by
        refine ⟨2 * 2 ^ sigmaUpper *
          zeroStripPhysicalMajorant J theta sigmaLower sigmaUpper X, ?_⟩
        intro y hy
        rcases hy with ⟨x, hx, rfl⟩
        exact norm_halfOpenZeroStripIncrementSum_le_physicalMajorant
          (J := J) (theta := theta) hX hx.1 hx.2 hsigmaLowerPos
            hsigmaOrder hsigmaUpper
      have hSupNonneg :
          0 ≤ halfOpenZeroStripPhysicalSup
            J theta sigmaLower sigmaUpper X := by
        unfold halfOpenZeroStripPhysicalSup
        have hElem :
            ‖halfOpenZeroStripIncrementSum sigmaLower sigmaUpper
              (explicitFormulaHeight J theta X) (localTau X theta) X‖ ∈
              ((fun x : ℝ =>
                ‖halfOpenZeroStripIncrementSum sigmaLower sigmaUpper
                  (explicitFormulaHeight J theta X) (localTau X theta) x‖) ''
                    Set.Icc X (2 * X)) :=
          ⟨X, ⟨le_rfl, by nlinarith⟩, rfl⟩
        exact (norm_nonneg _).trans (le_csSup hSetBounded hElem)
      simp only [Real.norm_eq_abs,
        abs_of_nonneg hSupNonneg, abs_of_nonneg hMajorantNonneg]
      simpa only [mul_comm] using hSupLe
    exact hFixed.trans
      ((RiemannZeta.GuthMaynard.EpsilonPowerBound.refl
        (zeroStripPhysicalMajorant J theta sigmaLower sigmaUpper)) eps heps)
  exact hSupToMajorant.trans hMajorant

theorem resonantZeroQuadruples_subset_of_sigma_le
    {sigmaLower sigmaUpper T : ℝ} (hsigma : sigmaLower ≤ sigmaUpper) :
    resonantZeroQuadruples sigmaUpper T ⊆
      resonantZeroQuadruples sigmaLower T := by
  intro q hq
  rw [mem_resonantZeroQuadruples] at hq ⊢
  exact ⟨zeroSet_subset_of_sigma_le hsigma hq.1,
    zeroSet_subset_of_sigma_le hsigma hq.2.1,
    zeroSet_subset_of_sigma_le hsigma hq.2.2.1,
    zeroSet_subset_of_sigma_le hsigma hq.2.2.2.1,
    hq.2.2.2.2⟩

theorem zeroAdditiveEnergyCount_anti_sigma
    {sigmaLower sigmaUpper T : ℝ} (hsigma : sigmaLower ≤ sigmaUpper) :
    zeroAdditiveEnergyCount sigmaUpper T ≤
      zeroAdditiveEnergyCount sigmaLower T := by
  unfold zeroAdditiveEnergyCount
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (resonantZeroQuadruples_subset_of_sigma_le hsigma)
  intro q hq hnot
  exact Nat.zero_le _

/-- Complete finite L² estimate for the literal half-open source strip. -/
theorem halfOpenZeroStripPhysicalSecondMoment_le_count
    (cutoff : GMSmoothCutoff) {K : ℝ} (hK : 0 ≤ K)
    (hDecay : ∀ s ∈ Set.Icc (0 : ℝ) 2, ∀ d : ℝ,
      (1 + |d|) ^ 10 *
        ‖complexifiedLogScaleBumpFourier cutoff
          ((d : ℂ) - I * (s : ℂ))‖ ≤ K)
    {sigmaLower sigmaUpper T tau X : ℝ}
    (hsigmaLower : 0 ≤ sigmaLower)
    (hsigmaOrder : sigmaLower ≤ sigmaUpper)
    (hsigmaUpper : sigmaUpper ≤ 1)
    (hT : max (Real.exp 2) 8 ≤ T)
    (htau : 0 < tau) (hX : 1 ≤ X) :
    halfOpenZeroStripPhysicalSecondMoment
        sigmaLower sigmaUpper T tau X ≤
      8 * ((K * ((X ^ sigmaUpper / tau) *
        (X ^ sigmaUpper / tau))) *
        (((3 ^ (10 : ℕ) * integerBinDecayMass) * globalLocalZeroLogConstant) *
          (Real.log T * (zeroCount sigmaLower T : ℝ)))) := by
  let B : ℝ := (K * ((X ^ sigmaUpper / tau) *
      (X ^ sigmaUpper / tau))) *
    (((3 ^ (10 : ℕ) * integerBinDecayMass) * globalLocalZeroLogConstant) *
      (Real.log T * (zeroCount sigmaLower T : ℝ)))
  have hLower := zeroStripPhysicalSecondMoment_le_count cutoff hK hDecay
    hsigmaLower hsigmaUpper hT htau hX
  have hsigmaUpperLower : 0 ≤ sigmaUpper :=
    hsigmaLower.trans hsigmaOrder
  have hBoundary := zeroStripPhysicalSecondMoment_le_count cutoff hK hDecay
    hsigmaUpperLower hsigmaUpper hT htau hX
  have hLog : 0 ≤ Real.log T := Real.log_nonneg
    ((by linarith [le_max_right (Real.exp 2) 8] : 1 ≤ T))
  have hBoundaryLe :
      zeroStripPhysicalSecondMoment sigmaUpper sigmaUpper T tau X ≤ 2 * B := by
    calc
      zeroStripPhysicalSecondMoment sigmaUpper sigmaUpper T tau X ≤
          2 * ((K * ((X ^ sigmaUpper / tau) *
            (X ^ sigmaUpper / tau))) *
            (((3 ^ (10 : ℕ) * integerBinDecayMass) * globalLocalZeroLogConstant) *
              (Real.log T * (zeroCount sigmaUpper T : ℝ)))) := hBoundary
      _ ≤ 2 * B := by
        unfold B
        have hCount : (zeroCount sigmaUpper T : ℝ) ≤
            (zeroCount sigmaLower T : ℝ) := by
          exact_mod_cast zeroCount_anti_sigma (T := T) hsigmaOrder
        have hInner : Real.log T * (zeroCount sigmaUpper T : ℝ) ≤
            Real.log T * (zeroCount sigmaLower T : ℝ) :=
          mul_le_mul_of_nonneg_left hCount hLog
        have hPrefix : 0 ≤ 2 *
            (K * ((X ^ sigmaUpper / tau) * (X ^ sigmaUpper / tau))) *
            ((3 ^ (10 : ℕ) * integerBinDecayMass) * globalLocalZeroLogConstant) := by
          have hR : 0 ≤ X ^ sigmaUpper / tau :=
            div_nonneg (Real.rpow_nonneg (by positivity) _) htau.le
          exact mul_nonneg
            (mul_nonneg (by positivity) (mul_nonneg hK (mul_nonneg hR hR)))
            (mul_nonneg
              (mul_nonneg (by positivity) integerBinDecayMass_nonneg)
              globalLocalZeroLogConstant_pos.le)
        calc
          2 * (K * (X ^ sigmaUpper / tau * (X ^ sigmaUpper / tau)) *
              (3 ^ 10 * integerBinDecayMass * globalLocalZeroLogConstant *
                (Real.log T * ↑(zeroCount sigmaUpper T)))) =
              (2 * (K * ((X ^ sigmaUpper / tau) *
                (X ^ sigmaUpper / tau))) *
                ((3 ^ (10 : ℕ) * integerBinDecayMass) *
                  globalLocalZeroLogConstant)) *
                (Real.log T * (zeroCount sigmaUpper T : ℝ)) := by ring
          _ ≤ (2 * (K * ((X ^ sigmaUpper / tau) *
                (X ^ sigmaUpper / tau))) *
                ((3 ^ (10 : ℕ) * integerBinDecayMass) *
                  globalLocalZeroLogConstant)) *
                (Real.log T * (zeroCount sigmaLower T : ℝ)) :=
            mul_le_mul_of_nonneg_left hInner hPrefix
          _ = 2 * (K * (X ^ sigmaUpper / tau *
              (X ^ sigmaUpper / tau)) *
              (3 ^ 10 * integerBinDecayMass * globalLocalZeroLogConstant *
                (Real.log T * ↑(zeroCount sigmaLower T)))) := by ring
  have hHalf := halfOpenZeroStripPhysicalSecondMoment_le_closed_add_boundary
    (T := T) (tau := tau) (X := X) (by linarith) hsigmaOrder hsigmaUpper
    htau (zero_lt_one.trans_le hX)
  calc
    halfOpenZeroStripPhysicalSecondMoment sigmaLower sigmaUpper T tau X ≤
        2 * (zeroStripPhysicalSecondMoment sigmaLower sigmaUpper T tau X +
          zeroStripPhysicalSecondMoment sigmaUpper sigmaUpper T tau X) := hHalf
    _ ≤ 2 * (2 * B + 2 * B) := by gcongr
    _ = 8 * B := by ring

/-- Complete finite L⁴ estimate for the literal half-open source strip. -/
theorem halfOpenZeroStripPhysicalFourthMoment_le_count
    (cutoff : GMSmoothCutoff) {K : ℝ} (hK : 0 ≤ K)
    (hDecay : ∀ s ∈ Set.Icc (0 : ℝ) 4, ∀ d : ℝ,
      (1 + |d|) ^ 10 *
        ‖complexifiedLogScaleBumpFourier cutoff
          ((d : ℂ) - I * (s : ℂ))‖ ≤ K)
    {sigmaLower sigmaUpper T tau X : ℝ}
    (hsigmaLower : 1 / 2 ≤ sigmaLower)
    (hsigmaOrder : sigmaLower ≤ sigmaUpper)
    (hsigmaUpper : sigmaUpper ≤ 1)
    (htau : 0 < tau) (hX : 1 ≤ X) :
    halfOpenZeroStripPhysicalFourthMoment
        sigmaLower sigmaUpper T tau X ≤
      32 * ((K * (((X ^ sigmaUpper / tau) *
        (X ^ sigmaUpper / tau)) *
        ((X ^ sigmaUpper / tau) * (X ^ sigmaUpper / tau)))) *
        ((3 ^ (10 : ℕ) * integerBinDecayMass) *
          (zeroAdditiveEnergyCount sigmaLower T : ℝ))) := by
  let B : ℝ := (K * (((X ^ sigmaUpper / tau) *
      (X ^ sigmaUpper / tau)) *
      ((X ^ sigmaUpper / tau) * (X ^ sigmaUpper / tau)))) *
    ((3 ^ (10 : ℕ) * integerBinDecayMass) *
      (zeroAdditiveEnergyCount sigmaLower T : ℝ))
  have hLower := zeroStripPhysicalFourthMoment_le_count (T := T)
    cutoff hK hDecay hsigmaLower hsigmaUpper htau hX
  have hsigmaUpperLower : 1 / 2 ≤ sigmaUpper :=
    hsigmaLower.trans hsigmaOrder
  have hBoundary := zeroStripPhysicalFourthMoment_le_count (T := T)
    cutoff hK hDecay hsigmaUpperLower hsigmaUpper htau hX
  have hBoundaryLe :
      zeroStripPhysicalFourthMoment sigmaUpper sigmaUpper T tau X ≤ 2 * B := by
    calc
      zeroStripPhysicalFourthMoment sigmaUpper sigmaUpper T tau X ≤
          2 * ((K * (((X ^ sigmaUpper / tau) *
            (X ^ sigmaUpper / tau)) *
            ((X ^ sigmaUpper / tau) * (X ^ sigmaUpper / tau)))) *
            ((3 ^ (10 : ℕ) * integerBinDecayMass) *
              (zeroAdditiveEnergyCount sigmaUpper T : ℝ))) := hBoundary
      _ ≤ 2 * B := by
        unfold B
        have hEnergy : (zeroAdditiveEnergyCount sigmaUpper T : ℝ) ≤
            (zeroAdditiveEnergyCount sigmaLower T : ℝ) := by
          exact_mod_cast zeroAdditiveEnergyCount_anti_sigma
            (T := T) hsigmaOrder
        have hPrefix : 0 ≤ 2 *
            (K * (((X ^ sigmaUpper / tau) * (X ^ sigmaUpper / tau)) *
              ((X ^ sigmaUpper / tau) * (X ^ sigmaUpper / tau)))) *
            (3 ^ (10 : ℕ) * integerBinDecayMass) := by
          have hR : 0 ≤ X ^ sigmaUpper / tau :=
            div_nonneg (Real.rpow_nonneg (by positivity) _) htau.le
          exact mul_nonneg
            (mul_nonneg (by positivity)
              (mul_nonneg hK (mul_nonneg (mul_nonneg hR hR)
                (mul_nonneg hR hR))))
            (mul_nonneg (by positivity) integerBinDecayMass_nonneg)
        calc
          2 * (K * (X ^ sigmaUpper / tau * (X ^ sigmaUpper / tau) *
              (X ^ sigmaUpper / tau * (X ^ sigmaUpper / tau))) *
              (3 ^ 10 * integerBinDecayMass *
                ↑(zeroAdditiveEnergyCount sigmaUpper T))) =
              (2 * (K * (((X ^ sigmaUpper / tau) *
                (X ^ sigmaUpper / tau)) * ((X ^ sigmaUpper / tau) *
                  (X ^ sigmaUpper / tau)))) *
                (3 ^ (10 : ℕ) * integerBinDecayMass)) *
                (zeroAdditiveEnergyCount sigmaUpper T : ℝ) := by ring
          _ ≤ (2 * (K * (((X ^ sigmaUpper / tau) *
                (X ^ sigmaUpper / tau)) * ((X ^ sigmaUpper / tau) *
                  (X ^ sigmaUpper / tau)))) *
                (3 ^ (10 : ℕ) * integerBinDecayMass)) *
                (zeroAdditiveEnergyCount sigmaLower T : ℝ) :=
            mul_le_mul_of_nonneg_left hEnergy hPrefix
          _ = 2 * (K * (X ^ sigmaUpper / tau *
              (X ^ sigmaUpper / tau) * (X ^ sigmaUpper / tau *
                (X ^ sigmaUpper / tau))) *
              (3 ^ 10 * integerBinDecayMass *
                ↑(zeroAdditiveEnergyCount sigmaLower T))) := by ring
  have hHalf := halfOpenZeroStripPhysicalFourthMoment_le_closed_add_boundary
    (T := T) (tau := tau) (X := X) (by linarith) hsigmaOrder hsigmaUpper
    htau (zero_lt_one.trans_le hX)
  calc
    halfOpenZeroStripPhysicalFourthMoment sigmaLower sigmaUpper T tau X ≤
        8 * (zeroStripPhysicalFourthMoment sigmaLower sigmaUpper T tau X +
          zeroStripPhysicalFourthMoment sigmaUpper sigmaUpper T tau X) := hHalf
    _ ≤ 8 * (2 * B + 2 * B) := by gcongr
    _ = 32 * B := by ring

theorem halfOpenZeroStripPhysicalSecondMoment_le_majorant
    (cutoff : GMSmoothCutoff) {K : ℝ} (hK : 0 ≤ K)
    (hDecay : ∀ s ∈ Set.Icc (0 : ℝ) 2, ∀ d : ℝ,
      (1 + |d|) ^ 10 *
        ‖complexifiedLogScaleBumpFourier cutoff
          ((d : ℂ) - I * (s : ℂ))‖ ≤ K)
    {J theta sigmaLower sigmaUpper X : ℝ}
    (hsigmaLower : 0 ≤ sigmaLower)
    (hsigmaOrder : sigmaLower ≤ sigmaUpper)
    (hsigmaUpper : sigmaUpper ≤ 1)
    (hHeight : max (Real.exp 2) 8 ≤ explicitFormulaHeight J theta X)
    (hX : 1 ≤ X) :
    halfOpenZeroStripPhysicalSecondMoment sigmaLower sigmaUpper
        (explicitFormulaHeight J theta X) (localTau X theta) X ≤
      (8 * K *
        ((3 ^ (10 : ℕ) * integerBinDecayMass) * globalLocalZeroLogConstant)) *
        zeroStripSecondPhysicalMajorant
          J theta sigmaLower sigmaUpper X := by
  have hXPos : 0 < X := zero_lt_one.trans_le hX
  have hFinite := halfOpenZeroStripPhysicalSecondMoment_le_count
    (T := explicitFormulaHeight J theta X) (tau := localTau X theta) (X := X)
      cutoff hK hDecay hsigmaLower hsigmaOrder hsigmaUpper hHeight
      (localTau_pos hXPos) hX
  have hScale : X ^ sigmaUpper / localTau X theta =
      X ^ (theta + sigmaUpper - 1) := rpow_div_localTau hXPos
  unfold zeroStripSecondPhysicalMajorant
  calc
    halfOpenZeroStripPhysicalSecondMoment sigmaLower sigmaUpper
        (explicitFormulaHeight J theta X) (localTau X theta) X ≤
      8 * ((K * ((X ^ (theta + sigmaUpper - 1)) *
        (X ^ (theta + sigmaUpper - 1)))) *
        (((3 ^ (10 : ℕ) * integerBinDecayMass) * globalLocalZeroLogConstant) *
          (Real.log (explicitFormulaHeight J theta X) *
            (zeroCount sigmaLower (explicitFormulaHeight J theta X) : ℝ)))) := by
      simpa only [hScale] using hFinite
    _ = (8 * K *
        ((3 ^ (10 : ℕ) * integerBinDecayMass) * globalLocalZeroLogConstant)) *
        ((X ^ (theta + sigmaUpper - 1) *
          X ^ (theta + sigmaUpper - 1)) *
          (Real.log (explicitFormulaHeight J theta X) *
            (zeroCount sigmaLower (explicitFormulaHeight J theta X) : ℝ))) := by
      ring

/-- Half-open, boundary-corrected source form of Gafni--Tao Lemma 2.3. -/
theorem halfOpenZeroStripPhysicalSecondMoment_epsilonBound
    (cutoff : GMSmoothCutoff)
    {J theta sigmaLower sigmaUpper a : ℝ}
    (hJ : 0 < J) (htheta : theta < 1) (ha : 0 ≤ a)
    (hsigmaLower : 0 ≤ sigmaLower)
    (hsigmaOrder : sigmaLower ≤ sigmaUpper)
    (hsigmaUpper : sigmaUpper ≤ 1)
    (hDensity : ZeroDensityEnvelope sigmaLower a) :
    EpsilonExponentBound
      (fun X => halfOpenZeroStripPhysicalSecondMoment sigmaLower sigmaUpper
        (explicitFormulaHeight J theta X) (localTau X theta) X)
      ((1 - theta) * (a * (1 - sigmaLower)) +
        2 * theta + 2 * sigmaUpper - 2) := by
  obtain ⟨K, hK, hDecay⟩ :=
    exists_complexifiedLogScaleBumpFourier_tenfold_decay cutoff
  let C : ℝ := 8 * K *
    ((3 ^ (10 : ℕ) * integerBinDecayMass) * globalLocalZeroLogConstant)
  have hHeightEventually :
      ∀ᶠ X : ℝ in Filter.atTop,
        max (Real.exp 2) 8 ≤ explicitFormulaHeight J theta X :=
    (tendsto_explicitFormulaHeight_atTop hJ htheta).eventually
      (Filter.eventually_ge_atTop _)
  have hDomination :
      RiemannZeta.GuthMaynard.EpsilonPowerBound
        (fun X => halfOpenZeroStripPhysicalSecondMoment sigmaLower sigmaUpper
          (explicitFormulaHeight J theta X) (localTau X theta) X)
        (zeroStripSecondPhysicalMajorant J theta sigmaLower sigmaUpper) := by
    intro eps heps
    have hFixed :
        (fun X : ℝ =>
          |halfOpenZeroStripPhysicalSecondMoment sigmaLower sigmaUpper
            (explicitFormulaHeight J theta X) (localTau X theta) X|) =O[Filter.atTop]
          (fun X : ℝ =>
            |zeroStripSecondPhysicalMajorant
              J theta sigmaLower sigmaUpper X|) := by
      apply Asymptotics.IsBigO.of_bound C
      filter_upwards [hHeightEventually,
        Filter.eventually_ge_atTop (Real.exp 1)] with X hHeight hXLarge
      have hExpOne : 1 < Real.exp 1 := by
        simpa only [Real.exp_zero] using
          Real.exp_lt_exp.mpr (zero_lt_one : (0 : ℝ) < 1)
      have hXOne : 1 ≤ X := hExpOne.le.trans hXLarge
      have hXPos : 0 < X := zero_lt_one.trans hExpOne |>.trans_le hXLarge
      have hPoint := halfOpenZeroStripPhysicalSecondMoment_le_majorant
        cutoff hK hDecay hsigmaLower hsigmaOrder hsigmaUpper hHeight hXOne
      have hMomentNonneg : 0 ≤ halfOpenZeroStripPhysicalSecondMoment
          sigmaLower sigmaUpper (explicitFormulaHeight J theta X)
            (localTau X theta) X := by
        unfold halfOpenZeroStripPhysicalSecondMoment
        apply mul_nonneg (one_div_nonneg.mpr hXPos.le)
        apply intervalIntegral.integral_nonneg (by linarith)
        intro x hx
        exact sq_nonneg _
      have hMajorantNonneg : 0 ≤ zeroStripSecondPhysicalMajorant
          J theta sigmaLower sigmaUpper X := by
        unfold zeroStripSecondPhysicalMajorant
        exact mul_nonneg
          (mul_nonneg (Real.rpow_nonneg hXPos.le _)
            (Real.rpow_nonneg hXPos.le _))
          (mul_nonneg (Real.log_nonneg (by
            exact (Real.one_lt_exp_iff.mpr (by norm_num)).le.trans
              (le_trans (le_max_left _ _) hHeight))) (by positivity))
      rw [Real.norm_eq_abs, abs_abs, abs_of_nonneg hMomentNonneg,
        Real.norm_eq_abs, abs_abs, abs_of_nonneg hMajorantNonneg]
      simpa [C] using hPoint
    exact hFixed.trans
      ((RiemannZeta.GuthMaynard.EpsilonPowerBound.refl
        (zeroStripSecondPhysicalMajorant
          J theta sigmaLower sigmaUpper)) eps heps)
  exact hDomination.trans
    (zeroStripSecondPhysicalMajorant_epsilonBound hJ htheta ha
      (hsigmaOrder.trans hsigmaUpper) hDensity)

theorem halfOpenZeroStripPhysicalFourthMoment_le_majorant
    (cutoff : GMSmoothCutoff) {K : ℝ} (hK : 0 ≤ K)
    (hDecay : ∀ s ∈ Set.Icc (0 : ℝ) 4, ∀ d : ℝ,
      (1 + |d|) ^ 10 *
        ‖complexifiedLogScaleBumpFourier cutoff
          ((d : ℂ) - I * (s : ℂ))‖ ≤ K)
    {J theta sigmaLower sigmaUpper X : ℝ}
    (hsigmaLower : 1 / 2 ≤ sigmaLower)
    (hsigmaOrder : sigmaLower ≤ sigmaUpper)
    (hsigmaUpper : sigmaUpper ≤ 1)
    (hX : 1 ≤ X) :
    halfOpenZeroStripPhysicalFourthMoment sigmaLower sigmaUpper
        (explicitFormulaHeight J theta X) (localTau X theta) X ≤
      (32 * K * (3 ^ (10 : ℕ) * integerBinDecayMass)) *
        zeroStripFourthPhysicalMajorant
          J theta sigmaLower sigmaUpper X := by
  have hXPos : 0 < X := zero_lt_one.trans_le hX
  have hFinite := halfOpenZeroStripPhysicalFourthMoment_le_count
    (T := explicitFormulaHeight J theta X) (tau := localTau X theta) (X := X)
      cutoff hK hDecay
      hsigmaLower hsigmaOrder hsigmaUpper (localTau_pos hXPos) hX
  have hScale : X ^ sigmaUpper / localTau X theta =
      X ^ (theta + sigmaUpper - 1) := rpow_div_localTau hXPos
  unfold zeroStripFourthPhysicalMajorant
  calc
    halfOpenZeroStripPhysicalFourthMoment sigmaLower sigmaUpper
        (explicitFormulaHeight J theta X) (localTau X theta) X ≤
      32 * ((K * ((X ^ (theta + sigmaUpper - 1) *
        X ^ (theta + sigmaUpper - 1)) *
        (X ^ (theta + sigmaUpper - 1) *
          X ^ (theta + sigmaUpper - 1)))) *
        ((3 ^ (10 : ℕ) * integerBinDecayMass) *
          (zeroAdditiveEnergyCount sigmaLower
            (explicitFormulaHeight J theta X) : ℝ))) := by
      simpa only [hScale] using hFinite
    _ = (32 * K * (3 ^ (10 : ℕ) * integerBinDecayMass)) *
        (((X ^ (theta + sigmaUpper - 1) *
          X ^ (theta + sigmaUpper - 1)) *
          (X ^ (theta + sigmaUpper - 1) *
            X ^ (theta + sigmaUpper - 1))) *
          (zeroAdditiveEnergyCount sigmaLower
            (explicitFormulaHeight J theta X) : ℝ)) := by ring

/-- Half-open, boundary-corrected source form of Gafni--Tao Lemma 2.4. -/
theorem halfOpenZeroStripPhysicalFourthMoment_epsilonBound
    (cutoff : GMSmoothCutoff)
    {J theta sigmaLower sigmaUpper a : ℝ}
    (hJ : 0 < J) (htheta : theta < 1) (ha : 0 ≤ a)
    (hsigmaLower : 1 / 2 ≤ sigmaLower)
    (hsigmaOrder : sigmaLower ≤ sigmaUpper)
    (hsigmaUpper : sigmaUpper ≤ 1)
    (hEnergy : ZeroAdditiveEnergyEnvelope sigmaLower a) :
    EpsilonExponentBound
      (fun X => halfOpenZeroStripPhysicalFourthMoment sigmaLower sigmaUpper
        (explicitFormulaHeight J theta X) (localTau X theta) X)
      ((1 - theta) * (a * (1 - sigmaLower)) +
        4 * theta + 4 * sigmaUpper - 4) := by
  obtain ⟨K, hK, hDecay⟩ :=
    exists_quarticComplexifiedLogScaleBumpFourier_tenfold_decay cutoff
  let C : ℝ := 32 * K * (3 ^ (10 : ℕ) * integerBinDecayMass)
  have hDomination :
      RiemannZeta.GuthMaynard.EpsilonPowerBound
        (fun X => halfOpenZeroStripPhysicalFourthMoment sigmaLower sigmaUpper
          (explicitFormulaHeight J theta X) (localTau X theta) X)
        (zeroStripFourthPhysicalMajorant J theta sigmaLower sigmaUpper) := by
    intro eps heps
    have hFixed :
        (fun X : ℝ =>
          |halfOpenZeroStripPhysicalFourthMoment sigmaLower sigmaUpper
            (explicitFormulaHeight J theta X) (localTau X theta) X|) =O[Filter.atTop]
          (fun X : ℝ =>
            |zeroStripFourthPhysicalMajorant
              J theta sigmaLower sigmaUpper X|) := by
      apply Asymptotics.IsBigO.of_bound C
      filter_upwards [Filter.eventually_ge_atTop (Real.exp 1)] with X hXLarge
      have hExpOne : 1 < Real.exp 1 := by
        simpa only [Real.exp_zero] using
          Real.exp_lt_exp.mpr (zero_lt_one : (0 : ℝ) < 1)
      have hXOne : 1 ≤ X := hExpOne.le.trans hXLarge
      have hXPos : 0 < X := zero_lt_one.trans hExpOne |>.trans_le hXLarge
      have hPoint := halfOpenZeroStripPhysicalFourthMoment_le_majorant
        (J := J) (theta := theta) cutoff hK hDecay
          hsigmaLower hsigmaOrder hsigmaUpper hXOne
      have hMomentNonneg : 0 ≤ halfOpenZeroStripPhysicalFourthMoment
          sigmaLower sigmaUpper (explicitFormulaHeight J theta X)
            (localTau X theta) X := by
        unfold halfOpenZeroStripPhysicalFourthMoment
        apply mul_nonneg (one_div_nonneg.mpr hXPos.le)
        apply intervalIntegral.integral_nonneg (by linarith)
        intro x hx
        positivity
      have hMajorantNonneg : 0 ≤ zeroStripFourthPhysicalMajorant
          J theta sigmaLower sigmaUpper X := by
        unfold zeroStripFourthPhysicalMajorant
        exact mul_nonneg
          (mul_nonneg
            (mul_nonneg (Real.rpow_nonneg hXPos.le _)
              (Real.rpow_nonneg hXPos.le _))
            (mul_nonneg (Real.rpow_nonneg hXPos.le _)
              (Real.rpow_nonneg hXPos.le _))) (by positivity)
      rw [Real.norm_eq_abs, abs_abs, abs_of_nonneg hMomentNonneg,
        Real.norm_eq_abs, abs_abs, abs_of_nonneg hMajorantNonneg]
      simpa [C] using hPoint
    exact hFixed.trans
      ((RiemannZeta.GuthMaynard.EpsilonPowerBound.refl
        (zeroStripFourthPhysicalMajorant
          J theta sigmaLower sigmaUpper)) eps heps)
  exact hDomination.trans
    (zeroStripFourthPhysicalMajorant_epsilonBound hJ htheta ha
      (hsigmaOrder.trans hsigmaUpper) hEnergy)

/-- The exact half-open zero increment sum is continuous on every positive
physical interval.  Factoring each term as `x^rho c_rho` keeps the proof away
from the branch point of complex exponentiation at zero. -/
theorem continuousOn_halfOpenZeroStripIncrementSum
    {sigmaLower sigmaUpper T tau X : ℝ} (htau : 0 < tau) (hX : 0 < X) :
    ContinuousOn
      (halfOpenZeroStripIncrementSum sigmaLower sigmaUpper T tau)
      (Set.Icc X (2 * X)) := by
  classical
  let F : ℝ → ℂ := fun x =>
    ∑ rho ∈ halfOpenZeroStrip sigmaLower sigmaUpper T,
      (zeroMultiplicity rho : ℂ) *
        ((x : ℂ) ^ rho * zeroIncrementCoefficient tau rho)
  have hF : ContinuousOn F (Set.Icc X (2 * X)) := by
    unfold F
    apply continuousOn_finsetSum
    intro rho hrho
    apply ContinuousOn.const_mul
    apply ContinuousOn.mul
    · intro x hx
      exact (Complex.continuousAt_ofReal_cpow_const x rho
        (Or.inr (ne_of_gt (hX.trans_le hx.1)))).continuousWithinAt
    · exact continuousOn_const
  apply hF.congr
  intro x hx
  unfold F halfOpenZeroStripIncrementSum
  apply Finset.sum_congr rfl
  intro rho hrho
  rw [zeroIncrementTerm_eq_cpow_mul_coefficient htau
    (hX.le.trans hx.1)]

/-- Compact-interval Chebyshev--Markov inequality in the exact finite form
needed for both the second- and fourth-moment alternatives of equation (2.7).
The statement remains in `ENNReal`, so no finiteness or coercion is hidden. -/
theorem measure_norm_ge_pow_le_intervalIntegral
    {f : ℝ → ℂ} {a b lambda : ℝ} (p : ℕ)
    (hf : ContinuousOn f (Set.Icc a b))
    (hab : a ≤ b) (hlambda : 0 < lambda) :
    MeasureTheory.volume
        {x | x ∈ Set.Icc a b ∧ lambda ≤ ‖f x‖} ≤
      ENNReal.ofReal
        ((∫ x : ℝ in a..b, ‖f x‖ ^ p) / lambda ^ p) := by
  let q : ℝ → ℝ := fun x => ‖f x‖ ^ p / lambda ^ p
  let g : ℝ → ℝ := (Set.Icc a b).indicator q
  have hq : ContinuousOn q (Set.Icc a b) := by
    exact (hf.norm.pow p).div_const (lambda ^ p)
  have hg : MeasureTheory.Integrable g :=
    hq.integrableOn_Icc.integrable_indicator measurableSet_Icc
  have hgNonneg : 0 ≤ᵐ[MeasureTheory.volume] g := by
    filter_upwards [] with x
    by_cases hx : x ∈ Set.Icc a b
    · simp only [g, Set.indicator_of_mem hx, q]
      positivity
    · simp [g, hx]
  have hone :
      ∀ x ∈ {x | x ∈ Set.Icc a b ∧ lambda ≤ ‖f x‖}, 1 ≤ g x := by
    intro x hx
    simp only [g, Set.indicator_of_mem hx.1, q]
    have hlambdaPow : 0 < lambda ^ p := pow_pos hlambda p
    apply (le_div_iff₀ hlambdaPow).2
    simpa using pow_le_pow_left₀ hlambda.le hx.2 p
  have hm := hg.measure_le_integral hgNonneg hone
  calc
    MeasureTheory.volume {x | x ∈ Set.Icc a b ∧ lambda ≤ ‖f x‖} ≤
        ENNReal.ofReal (∫ x, g x) := hm
    _ = ENNReal.ofReal ((∫ x : ℝ in a..b, ‖f x‖ ^ p) / lambda ^ p) := by
      congr 1
      rw [show (∫ x, g x) = ∫ x in Set.Icc a b, q x by
        exact MeasureTheory.integral_indicator measurableSet_Icc]
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le hab]
      unfold q
      rw [← intervalIntegral.integral_div]

/-- Distinct source indices give disjoint half-open zero strips, including
zeros lying exactly on an internal boundary. -/
theorem disjoint_halfOpenStripZeros {J j k : ℕ} {T : ℝ} (hjk : j ≠ k) :
    Disjoint (halfOpenStripZeros J j T) (halfOpenStripZeros J k T) := by
  rw [Finset.disjoint_left]
  intro rho hrhoJ hrhoK
  have hj := (Finset.mem_filter.mp hrhoJ).2
  have hk := (Finset.mem_filter.mp hrhoK).2
  exact hjk (hj.symm.trans hk)

/-- A finite sum can be reconstructed from all fibers of an index map whose
values lie in `range J`. -/
theorem sum_range_filter_index
    {α M : Type*} [DecidableEq α] [AddCommMonoid M]
    (s : Finset α) (index : α → ℕ) (f : α → M) {J : ℕ}
    (hindex : ∀ a ∈ s, index a < J) :
    ∑ j ∈ Finset.range J, ∑ a ∈ s.filter (fun a => index a = j), f a =
      ∑ a ∈ s, f a := by
  classical
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  have hmem : index a ∈ Finset.range J := Finset.mem_range.mpr (hindex a ha)
  calc
    ∑ j ∈ Finset.range J, (if index a = j then f a else 0) =
        (if index a = index a then f a else 0) := by
      apply Finset.sum_eq_single (index a)
      · intro b hb hba
        simp [Ne.symm hba]
      · intro hnot
        exact (hnot hmem).elim
    _ = f a := by simp

/-- Exact half-open reconstruction of the full zero increment sum. -/
theorem sum_halfOpenStripIncrementSum_eq_full
    {J : ℕ} (hJ : 0 < J) (T tau x : ℝ) :
    ∑ j ∈ Finset.range J, halfOpenStripIncrementSum J j T tau x =
      fullZeroIncrementSum T tau x := by
  classical
  unfold halfOpenStripIncrementSum halfOpenStripZeros fullZeroIncrementSum
  exact sum_range_filter_index (zeroSet 0 T) (zeroStripIndex J)
    (fun rho => (zeroMultiplicity rho : ℂ) * zeroIncrementTerm tau x rho)
    (fun _ hrho => zeroStripIndex_lt hJ hrho)

/-- Exact finite pigeonhole step used before equation (2.7): a full sum above
threshold `delta` forces one of the `J` half-open strips above `delta/J`. -/
theorem exists_halfOpenStrip_norm_ge
    {J : ℕ} (hJ : 0 < J) {T tau x delta : ℝ} (hdelta : 0 < delta)
    (hlarge : delta ≤ ‖fullZeroIncrementSum T tau x‖) :
    ∃ j ∈ Finset.range J,
      delta / J ≤ ‖halfOpenStripIncrementSum J j T tau x‖ := by
  by_contra hnone
  push Not at hnone
  have hstrict :
      ∑ j ∈ Finset.range J, ‖halfOpenStripIncrementSum J j T tau x‖ < delta := by
    calc
      ∑ j ∈ Finset.range J, ‖halfOpenStripIncrementSum J j T tau x‖ <
          ∑ _j ∈ Finset.range J, delta / J := by
        apply Finset.sum_lt_sum_of_nonempty
        · exact ⟨0, Finset.mem_range.mpr hJ⟩
        · intro j hj
          exact hnone j hj
      _ = delta := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        have hJr : (J : ℝ) ≠ 0 := by exact_mod_cast hJ.ne'
        field_simp
  have htriangle :
      ‖fullZeroIncrementSum T tau x‖ ≤
        ∑ j ∈ Finset.range J, ‖halfOpenStripIncrementSum J j T tau x‖ := by
    rw [← sum_halfOpenStripIncrementSum_eq_full hJ]
    exact norm_sum_le _ _
  exact (not_lt_of_ge hlarge) (htriangle.trans_lt hstrict)

/-- The full large-zero-sum event on the physical source interval. -/
noncomputable def fullZeroLargeSet
    (T tau X delta : ℝ) : Set ℝ :=
  {x | x ∈ Set.Icc X (2 * X) ∧
    delta ≤ ‖fullZeroIncrementSum T tau x‖}

/-- The large event for the exact half-open strip indexed by `j`. -/
noncomputable def halfOpenStripLargeSet
    (J j : ℕ) (T tau X delta : ℝ) : Set ℝ :=
  {x | x ∈ Set.Icc X (2 * X) ∧
    delta / J ≤ ‖halfOpenStripIncrementSum J j T tau x‖}

/-- Event-level finite pigeonhole inclusion.  This is the exact set-theoretic
step behind the factor `J` in equation (2.7). -/
theorem fullZeroLargeSet_subset_biUnion_halfOpenStripLargeSet
    {J : ℕ} (hJ : 0 < J) {T tau X delta : ℝ} (hdelta : 0 < delta) :
    fullZeroLargeSet T tau X delta ⊆
      ⋃ j ∈ Finset.range J, halfOpenStripLargeSet J j T tau X delta := by
  intro x hx
  obtain ⟨j, hj, hlarge⟩ :=
    exists_halfOpenStrip_norm_ge hJ hdelta hx.2
  rw [Set.mem_iUnion]
  exact ⟨j, by rw [Set.mem_iUnion]; exact ⟨hj, hx.1, hlarge⟩⟩

/-- The measure of the full event is bounded by the sum of the exact strip
event measures.  Measurability is not needed for finite subadditivity. -/
theorem measure_fullZeroLargeSet_le_sum_halfOpenStripLargeSet
    {J : ℕ} (hJ : 0 < J) {T tau X delta : ℝ} (hdelta : 0 < delta) :
    MeasureTheory.volume (fullZeroLargeSet T tau X delta) ≤
      ∑ j ∈ Finset.range J,
        MeasureTheory.volume (halfOpenStripLargeSet J j T tau X delta) := by
  exact (MeasureTheory.measure_mono
    (fullZeroLargeSet_subset_biUnion_halfOpenStripLargeSet hJ hdelta)).trans
      (MeasureTheory.measure_biUnion_finset_le (Finset.range J)
        (halfOpenStripLargeSet J · T tau X delta))

/-- Exact L² Chebyshev bound for one source half-open strip.  The factor `X`
undoes the physical moment's normalization, while the literal threshold is
`delta / J`; no logarithm or endpoint loss is hidden in this statement. -/
theorem measure_halfOpenStripLargeSet_le_secondMoment
    {J : ℕ} (hJ : 0 < J) {j : ℕ} {T tau X delta : ℝ}
    (htau : 0 < tau) (hX : 0 < X) (hdelta : 0 < delta) :
    MeasureTheory.volume (halfOpenStripLargeSet J j T tau X delta) ≤
      ENNReal.ofReal
        (X * halfOpenZeroStripPhysicalSecondMoment
          ((j : ℝ) / J) ((j + 1 : ℕ) / J) T tau X /
            (delta / J) ^ 2) := by
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  have hinterval : X ≤ 2 * X := by linarith
  have hm := measure_norm_ge_pow_le_intervalIntegral
    (f := halfOpenZeroStripIncrementSum
      ((j : ℝ) / J) ((j + 1 : ℕ) / J) T tau)
    2 (continuousOn_halfOpenZeroStripIncrementSum htau hX)
      hinterval (div_pos hdelta hJr)
  have hmoment :
      (∫ x : ℝ in X..2 * X,
        ‖halfOpenZeroStripIncrementSum
          ((j : ℝ) / J) ((j + 1 : ℕ) / J) T tau x‖ ^ 2) =
        X * halfOpenZeroStripPhysicalSecondMoment
          ((j : ℝ) / J) ((j + 1 : ℕ) / J) T tau X := by
    unfold halfOpenZeroStripPhysicalSecondMoment
    field_simp [hX.ne']
  rw [halfOpenStripLargeSet]
  simp_rw [halfOpenStripIncrementSum_eq_endpointSum hJ]
  simpa only [hmoment] using hm

/-- Exact L⁴ Chebyshev bound for one source half-open strip. -/
theorem measure_halfOpenStripLargeSet_le_fourthMoment
    {J : ℕ} (hJ : 0 < J) {j : ℕ} {T tau X delta : ℝ}
    (htau : 0 < tau) (hX : 0 < X) (hdelta : 0 < delta) :
    MeasureTheory.volume (halfOpenStripLargeSet J j T tau X delta) ≤
      ENNReal.ofReal
        (X * halfOpenZeroStripPhysicalFourthMoment
          ((j : ℝ) / J) ((j + 1 : ℕ) / J) T tau X /
            (delta / J) ^ 4) := by
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  have hinterval : X ≤ 2 * X := by linarith
  have hm := measure_norm_ge_pow_le_intervalIntegral
    (f := halfOpenZeroStripIncrementSum
      ((j : ℝ) / J) ((j + 1 : ℕ) / J) T tau)
    4 (continuousOn_halfOpenZeroStripIncrementSum htau hX)
      hinterval (div_pos hdelta hJr)
  have hmoment :
      (∫ x : ℝ in X..2 * X,
        ‖halfOpenZeroStripIncrementSum
          ((j : ℝ) / J) ((j + 1 : ℕ) / J) T tau x‖ ^ 4) =
        X * halfOpenZeroStripPhysicalFourthMoment
          ((j : ℝ) / J) ((j + 1 : ℕ) / J) T tau X := by
    unfold halfOpenZeroStripPhysicalFourthMoment
    field_simp [hX.ne']
  rw [halfOpenStripLargeSet]
  simp_rw [halfOpenStripIncrementSum_eq_endpointSum hJ]
  simpa only [hmoment] using hm

/-- The literal one-strip event in equation (2.7), on the source's half-open
multiplicative interval and at the threshold `delta/(3J) * X/tau`. -/
noncomputable def equation27StripLargeSet
    (J j : ℕ) (theta delta X : ℝ) : Set ℝ :=
  {x | x ∈ Set.Ico X ((1 + delta / J) * X) ∧
    delta / (3 * J) * (X / localTau X theta) ≤
      ‖halfOpenStripIncrementSum J j
        (explicitFormulaHeight J theta X) (localTau X theta) x‖}

/-- The exact real-valued Lebesgue measure occurring on the left side of
equation (2.7) for a fixed source strip. -/
noncomputable def equation27StripMeasure
    (J j : ℕ) (theta delta X : ℝ) : ℝ :=
  (MeasureTheory.volume (equation27StripLargeSet J j theta delta X)).toReal

/-- The physical threshold `X / tau` is exactly `X^theta`. -/
theorem div_localTau_self_eq_rpow {X theta : ℝ} (hX : 0 < X) :
    X / localTau X theta = X ^ theta := by
  calc
    X / localTau X theta = X ^ (1 : ℝ) / localTau X theta := by
      rw [Real.rpow_one]
    _ = X ^ (theta + 1 - 1) := rpow_div_localTau hX
    _ = X ^ theta := by ring_nf

/-- The exact small-`A` alternative in equation (2.7): if Lemma 2.2 gives a
strict exponent below the physical threshold exponent `theta`, then the
literal half-open strip event on the literal source interval is eventually
empty. -/
theorem eventually_equation27StripLargeSet_eq_empty_of_density
    {J : ℕ} (hJ : 0 < J) {j : ℕ} {theta delta a : ℝ}
    (htheta : theta < 1) (hdelta : 0 < delta) (hdeltaOne : delta < 1)
    (ha : 0 ≤ a)
    (hsigmaLowerPos : 0 < (j : ℝ) / J)
    (hsigmaUpper : ((j + 1 : ℕ) : ℝ) / J ≤ 1)
    (hDensity : ZeroDensityEnvelope ((j : ℝ) / J) a)
    (hExponent :
      (1 - theta) * (a * (1 - (j : ℝ) / J)) +
          theta + ((j + 1 : ℕ) : ℝ) / J - 1 < theta) :
    ∀ᶠ X in atTop, equation27StripLargeSet J j theta delta X = ∅ := by
  let sigmaLower : ℝ := (j : ℝ) / J
  let sigmaUpper : ℝ := ((j + 1 : ℕ) : ℝ) / J
  let exponent : ℝ :=
    (1 - theta) * (a * (1 - sigmaLower)) + theta + sigmaUpper - 1
  let c : ℝ := delta / (3 * J)
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  have hsigmaOrder : sigmaLower ≤ sigmaUpper := by
    dsimp [sigmaLower, sigmaUpper]
    exact (div_le_div_iff_of_pos_right hJr).2 (by exact_mod_cast Nat.le_succ j)
  have hSup : EpsilonExponentBound
      (halfOpenZeroStripPhysicalSup J theta sigmaLower sigmaUpper) exponent := by
    dsimp [sigmaLower, sigmaUpper, exponent]
    exact halfOpenZeroStripPhysicalSup_epsilonBound
      hJr htheta ha hsigmaLowerPos hsigmaOrder hsigmaUpper hDensity
  have hExponent' : exponent < theta := by
    simpa [exponent, sigmaLower, sigmaUpper] using hExponent
  have hLittle := hSup.isLittleO_rpow hExponent'
  have hc : 0 < c := by
    dsimp [c]
    exact div_pos hdelta (mul_pos (by norm_num) hJr)
  have hSmall := hLittle.bound (half_pos hc)
  filter_upwards [hSmall, eventually_ge_atTop (1 : ℝ)] with X hSmallX hX
  have hXPos : 0 < X := zero_lt_one.trans_le hX
  have hJOne : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have hratio : delta / (J : ℝ) ≤ 1 :=
    (div_le_one hJr).2 (hdeltaOne.le.trans hJOne)
  have hsourceUpper : (1 + delta / (J : ℝ)) * X ≤ 2 * X := by
    nlinarith
  have hSupSmall :
      halfOpenZeroStripPhysicalSup J theta sigmaLower sigmaUpper X <
        c * X ^ theta := by
    have hSupNonneg : 0 ≤
        halfOpenZeroStripPhysicalSup J theta sigmaLower sigmaUpper X := by
      have hAtX := norm_halfOpenZeroStripIncrementSum_le_physicalSup
        (J := J) (theta := theta) (sigmaLower := sigmaLower)
        (sigmaUpper := sigmaUpper) hX le_rfl (by nlinarith)
        hsigmaLowerPos hsigmaOrder hsigmaUpper
      exact (norm_nonneg _).trans hAtX
    have hPowPos : 0 < X ^ theta := Real.rpow_pos_of_pos hXPos _
    have hSmallX' :
        halfOpenZeroStripPhysicalSup J theta sigmaLower sigmaUpper X ≤
          (c / 2) * X ^ theta := by
      simpa only [Real.norm_eq_abs, abs_abs, abs_of_nonneg hSupNonneg,
        abs_of_nonneg (Real.rpow_nonneg hXPos.le _)] using hSmallX
    exact hSmallX'.trans_lt (by nlinarith)
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  have hxSup := norm_halfOpenZeroStripIncrementSum_le_physicalSup
    (J := J) (theta := theta) (sigmaLower := sigmaLower)
    (sigmaUpper := sigmaUpper) hX hx.1.1
      (hx.1.2.le.trans hsourceUpper) hsigmaLowerPos hsigmaOrder hsigmaUpper
  have hxLarge : c * X ^ theta ≤
      ‖halfOpenZeroStripIncrementSum sigmaLower sigmaUpper
        (explicitFormulaHeight J theta X) (localTau X theta) x‖ := by
    have hsum := halfOpenStripIncrementSum_eq_endpointSum
      hJ j (explicitFormulaHeight J theta X) (localTau X theta) x
    have hthreshold :
        delta / (3 * J) * (X / localTau X theta) = c * X ^ theta := by
      rw [div_localTau_self_eq_rpow hXPos]
    rw [← hsum, ← hthreshold]
    exact hx.2
  exact (not_le_of_gt hSupSmall) (hxLarge.trans hxSup)

/-- Source-facing small-`A` consumer.  The strict `1/J` inequality is exactly
the displacement budget needed to pass from the strip's lower edge to its
upper edge.  The density envelope is derived from the genuine extended-real
`A(sigmaLower)` rather than accepted as a theorem parameter. -/
theorem eventually_equation27StripLargeSet_eq_empty_of_small_A
    {J : ℕ} (hJ : 0 < J) {j : ℕ} {theta delta epsA : ℝ}
    (htheta : theta < 1) (hdelta : 0 < delta) (hdeltaOne : delta < 1)
    (ha : 0 ≤ 1 / (1 - theta) - epsA)
    (hsigmaLowerPos : 0 < (j : ℝ) / J)
    (hsigmaUpper : ((j + 1 : ℕ) : ℝ) / J ≤ 1)
    (hA : zeroDensityExponent ((j : ℝ) / J) <
      ((1 / (1 - theta) - epsA : ℝ) : EReal))
    (hJMargin : 1 / (J : ℝ) <
      epsA * (1 - theta) * (1 - (j : ℝ) / J)) :
    ∀ᶠ X in atTop, equation27StripLargeSet J j theta delta X = ∅ := by
  have hDensity : ZeroDensityEnvelope ((j : ℝ) / J)
      (1 / (1 - theta) - epsA) :=
    zeroDensityEnvelope_of_zeroDensityExponent_lt
      ((show (j : ℝ) / J ≤ ((j + 1 : ℕ) : ℝ) / J by
        exact (div_le_div_iff_of_pos_right (by exact_mod_cast hJ)).2
          (by exact_mod_cast Nat.le_succ j)).trans hsigmaUpper) hA
  apply eventually_equation27StripLargeSet_eq_empty_of_density
    hJ htheta hdelta hdeltaOne ha hsigmaLowerPos hsigmaUpper hDensity
  have hthetaGap : 0 < 1 - theta := by linarith
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  have hStep :
      (((j + 1 : ℕ) : ℝ) / J) = (j : ℝ) / J + 1 / J := by
    push_cast
    field_simp [hJr.ne']
  rw [hStep]
  have hCancel :
      (1 - theta) *
          ((1 / (1 - theta) - epsA) * (1 - (j : ℝ) / J)) =
        (1 - (j : ℝ) / J) -
          epsA * (1 - theta) * (1 - (j : ℝ) / J) := by
    field_simp [hthetaGap.ne']
  rw [hCancel]
  linarith

/-- Exact source `A(sigmaLower) ≤ 1/(1-theta)-epsilon` branch.  Half of the
source epsilon opens the defining infimum, while the other half pays the
literal strip displacement. -/
theorem eventually_equation27StripLargeSet_eq_empty_of_small_A_le
    {J : ℕ} (hJ : 0 < J) {j : ℕ} {theta delta epsA : ℝ}
    (htheta : theta < 1) (hdelta : 0 < delta) (hdeltaOne : delta < 1)
    (hepsA : 0 < epsA)
    (ha : 0 ≤ 1 / (1 - theta) - epsA / 2)
    (hsigmaLowerPos : 0 < (j : ℝ) / J)
    (hsigmaUpper : ((j + 1 : ℕ) : ℝ) / J ≤ 1)
    (hA : zeroDensityExponent ((j : ℝ) / J) ≤
      ((1 / (1 - theta) - epsA : ℝ) : EReal))
    (hJMargin : 1 / (J : ℝ) <
      (epsA / 2) * (1 - theta) * (1 - (j : ℝ) / J)) :
    ∀ᶠ X in atTop, equation27StripLargeSet J j theta delta X = ∅ := by
  apply eventually_equation27StripLargeSet_eq_empty_of_small_A
    hJ htheta hdelta hdeltaOne ha hsigmaLowerPos hsigmaUpper
      (hA.trans_lt (by exact_mod_cast (show
        1 / (1 - theta) - epsA < 1 / (1 - theta) - epsA / 2 by linarith)))
      hJMargin

/-- An eventually empty literal strip event satisfies every real power
bound.  This is the exact bridge used by the small-`A` and right-edge
alternatives in equation (2.7). -/
theorem equation27StripMeasure_epsilonBound_of_eventually_empty
    {J j : ℕ} {theta delta q : ℝ}
    (hEmpty : ∀ᶠ X : ℝ in atTop,
      equation27StripLargeSet J j theta delta X = ∅) :
    EpsilonExponentBound
      (fun X => equation27StripMeasure J j theta delta X) q := by
  unfold EpsilonExponentBound
  intro eps _heps
  apply IsBigO.of_bound 0
  filter_upwards [hEmpty] with X hX
  simp [equation27StripMeasure, hX]

/-- The literal full-zero-sum event in equation (2.7), before the finite
half-open strip pigeonhole step. -/
noncomputable def equation27FullZeroLargeSet
    (J : ℕ) (theta delta X : ℝ) : Set ℝ :=
  {x | x ∈ Set.Ico X ((1 + delta / J) * X) ∧
    (delta / 3) * (X / localTau X theta) ≤
      ‖fullZeroIncrementSum (explicitFormulaHeight J theta X)
        (localTau X theta) x‖}

noncomputable def equation27FullZeroMeasure
    (J : ℕ) (theta delta X : ℝ) : ℝ :=
  (MeasureTheory.volume (equation27FullZeroLargeSet J theta delta X)).toReal

/-- Exact source-interval pigeonhole inclusion for equation (2.7). -/
theorem equation27FullZeroLargeSet_subset_biUnion_strip
    {J : ℕ} (hJ : 0 < J) {theta delta X : ℝ}
    (hdelta : 0 < delta) (hX : 0 < X) :
    equation27FullZeroLargeSet J theta delta X ⊆
      ⋃ j ∈ Finset.range J, equation27StripLargeSet J j theta delta X := by
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  have htau : 0 < localTau X theta := localTau_pos hX
  intro x hx
  have hFullThreshold : 0 < (delta / 3) * (X / localTau X theta) :=
    mul_pos (div_pos hdelta (by norm_num)) (div_pos hX htau)
  obtain ⟨j, hj, hlarge⟩ := exists_halfOpenStrip_norm_ge
    hJ hFullThreshold hx.2
  have hthreshold :
      ((delta / 3) * (X / localTau X theta)) / (J : ℝ) =
        delta / (3 * J) * (X / localTau X theta) := by
    field_simp [hJr.ne']
  rw [Set.mem_iUnion]
  refine ⟨j, ?_⟩
  rw [Set.mem_iUnion]
  refine ⟨hj, hx.1, ?_⟩
  rw [← hthreshold]
  exact hlarge

/-- Measure subadditivity after the exact source-interval strip
pigeonhole. -/
theorem measure_equation27FullZeroLargeSet_le_sum_strips
    {J : ℕ} (hJ : 0 < J) {theta delta X : ℝ}
    (hdelta : 0 < delta) (hX : 0 < X) :
    MeasureTheory.volume (equation27FullZeroLargeSet J theta delta X) ≤
      ∑ j ∈ Finset.range J,
        MeasureTheory.volume (equation27StripLargeSet J j theta delta X) := by
  exact (MeasureTheory.measure_mono
    (equation27FullZeroLargeSet_subset_biUnion_strip hJ hdelta hX)).trans
      (MeasureTheory.measure_biUnion_finset_le (Finset.range J)
        (equation27StripLargeSet J · theta delta X))

theorem equation27StripLargeSet_subset_sourceInterval
    (J j : ℕ) (theta delta X : ℝ) :
    equation27StripLargeSet J j theta delta X ⊆
      Set.Ico X ((1 + delta / J) * X) := by
  intro x hx
  exact hx.1

theorem measure_equation27StripLargeSet_ne_top
    (J j : ℕ) (theta delta X : ℝ) :
    MeasureTheory.volume (equation27StripLargeSet J j theta delta X) ≠ ⊤ := by
  apply ne_of_lt
  exact (MeasureTheory.measure_mono
    (equation27StripLargeSet_subset_sourceInterval J j theta delta X)).trans_lt
      measure_Ico_lt_top

/-- Real-valued finite-sum form of the exact strip pigeonhole estimate. -/
theorem equation27FullZeroMeasure_le_sum_strips
    {J : ℕ} (hJ : 0 < J) {theta delta X : ℝ}
    (hdelta : 0 < delta) (hX : 0 < X) :
    equation27FullZeroMeasure J theta delta X ≤
      ∑ j ∈ Finset.range J, equation27StripMeasure J j theta delta X := by
  have hm := measure_equation27FullZeroLargeSet_le_sum_strips
    (theta := theta) hJ hdelta hX
  have hfinite :
      (∑ j ∈ Finset.range J,
        MeasureTheory.volume (equation27StripLargeSet J j theta delta X)) ≠ ⊤ :=
    ENNReal.sum_ne_top.2 fun j hj =>
      measure_equation27StripLargeSet_ne_top J j theta delta X
  have hReal := ENNReal.toReal_mono hfinite hm
  rw [ENNReal.toReal_sum (fun j hj => by
    exact ENNReal.sum_ne_top.1 hfinite j hj)] at hReal
  simpa only [equation27FullZeroMeasure, equation27StripMeasure] using hReal

/-- Finite equation-(2.7) assembly: a common strip exponent controls the
literal full-zero event after the exact half-open pigeonhole. -/
theorem equation27FullZeroMeasure_epsilonBound
    {J : ℕ} (hJ : 0 < J) {theta delta q : ℝ}
    (hdelta : 0 < delta)
    (hStrips : ∀ j ∈ Finset.range J,
      EpsilonExponentBound
        (fun X => equation27StripMeasure J j theta delta X) q) :
    EpsilonExponentBound
      (fun X => equation27FullZeroMeasure J theta delta X) q := by
  have hSum := EpsilonExponentBound.finset_sum (Finset.range J)
    (fun j X => equation27StripMeasure J j theta delta X) hStrips
  unfold EpsilonExponentBound at hSum ⊢
  intro eps heps
  have hPointwise :
      (fun X : ℝ => |equation27FullZeroMeasure J theta delta X|) =O[atTop]
        (fun X => |∑ j ∈ Finset.range J,
          equation27StripMeasure J j theta delta X|) := by
    apply IsBigO.of_bound 1
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    have hLe := equation27FullZeroMeasure_le_sum_strips
      (theta := theta) hJ hdelta hX
    have hFullNonneg : 0 ≤ equation27FullZeroMeasure J theta delta X := by
      unfold equation27FullZeroMeasure
      positivity
    have hStripNonneg : 0 ≤ ∑ j ∈ Finset.range J,
        equation27StripMeasure J j theta delta X := by
      apply Finset.sum_nonneg
      intro j hj
      unfold equation27StripMeasure
      positivity
    rw [Real.norm_eq_abs, abs_abs, abs_of_nonneg hFullNonneg,
      Real.norm_eq_abs, abs_abs, abs_of_nonneg hStripNonneg, one_mul]
    exact hLe
  exact hPointwise.trans (hSum eps heps)

/-- The source interval in equation (2.7) lies in the physical moment interval
`[X,2X]`; the threshold agrees exactly with the finite-pigeonhole event. -/
theorem equation27StripLargeSet_subset_halfOpenStripLargeSet
    {J : ℕ} (hJ : 0 < J) {j : ℕ} {theta delta X : ℝ}
    (hdelta : 0 < delta) (hdeltaOne : delta < 1) (hX : 0 < X) :
    equation27StripLargeSet J j theta delta X ⊆
      halfOpenStripLargeSet J j
        (explicitFormulaHeight J theta X) (localTau X theta) X
        ((delta / 3) * (X / localTau X theta)) := by
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  have hJOne : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  intro x hx
  rcases hx with ⟨hxInterval, hxLarge⟩
  constructor
  · constructor
    · exact hxInterval.1
    · have hratio : delta / (J : ℝ) ≤ 1 := by
        exact (div_le_one hJr).2 (hdeltaOne.le.trans hJOne)
      have hupper : (1 + delta / (J : ℝ)) * X ≤ 2 * X := by
        nlinarith
      exact hxInterval.2.le.trans hupper
  · have hthreshold :
        ((delta / 3) * (X / localTau X theta)) / (J : ℝ) =
      delta / (3 * J) * (X / localTau X theta) := by
        field_simp [hJr.ne']
    rw [hthreshold]
    exact hxLarge

/-- Exact L² Markov estimate for the literal equation-(2.7) strip event. -/
theorem measure_equation27StripLargeSet_le_secondMoment
    {J : ℕ} (hJ : 0 < J) {j : ℕ} {theta delta X : ℝ}
    (hdelta : 0 < delta) (hdeltaOne : delta < 1) (hX : 0 < X) :
    MeasureTheory.volume (equation27StripLargeSet J j theta delta X) ≤
      ENNReal.ofReal
        (X * halfOpenZeroStripPhysicalSecondMoment
          ((j : ℝ) / J) ((j + 1 : ℕ) / J)
          (explicitFormulaHeight J theta X) (localTau X theta) X /
            (((delta / 3) * (X / localTau X theta)) / J) ^ 2) := by
  exact (MeasureTheory.measure_mono
    (equation27StripLargeSet_subset_halfOpenStripLargeSet
      hJ hdelta hdeltaOne hX)).trans
    (measure_halfOpenStripLargeSet_le_secondMoment hJ
      (localTau_pos hX) hX
      (mul_pos (div_pos hdelta (by norm_num))
        (div_pos hX (localTau_pos hX))))

/-- Exact L⁴ Markov estimate for the literal equation-(2.7) strip event. -/
theorem measure_equation27StripLargeSet_le_fourthMoment
    {J : ℕ} (hJ : 0 < J) {j : ℕ} {theta delta X : ℝ}
    (hdelta : 0 < delta) (hdeltaOne : delta < 1) (hX : 0 < X) :
    MeasureTheory.volume (equation27StripLargeSet J j theta delta X) ≤
      ENNReal.ofReal
        (X * halfOpenZeroStripPhysicalFourthMoment
          ((j : ℝ) / J) ((j + 1 : ℕ) / J)
          (explicitFormulaHeight J theta X) (localTau X theta) X /
            (((delta / 3) * (X / localTau X theta)) / J) ^ 4) := by
  exact (MeasureTheory.measure_mono
    (equation27StripLargeSet_subset_halfOpenStripLargeSet
      hJ hdelta hdeltaOne hX)).trans
    (measure_halfOpenStripLargeSet_le_fourthMoment hJ
      (localTau_pos hX) hX
      (mul_pos (div_pos hdelta (by norm_num))
        (div_pos hX (localTau_pos hX))))

/-- Real-valued form of the exact equation-(2.7) L² Markov estimate. -/
theorem equation27StripMeasure_le_secondMoment
    {J : ℕ} (hJ : 0 < J) {j : ℕ} {theta delta X : ℝ}
    (hdelta : 0 < delta) (hdeltaOne : delta < 1) (hX : 0 < X) :
    equation27StripMeasure J j theta delta X ≤
      X * halfOpenZeroStripPhysicalSecondMoment
          ((j : ℝ) / J) ((j + 1 : ℕ) / J)
          (explicitFormulaHeight J theta X) (localTau X theta) X /
        (((delta / 3) * (X / localTau X theta)) / J) ^ 2 := by
  have hm := measure_equation27StripLargeSet_le_secondMoment
    (j := j) (theta := theta) hJ hdelta hdeltaOne hX
  have hRhsNonneg :
      0 ≤ X * halfOpenZeroStripPhysicalSecondMoment
          ((j : ℝ) / J) ((j + 1 : ℕ) / J)
          (explicitFormulaHeight J theta X) (localTau X theta) X /
        (((delta / 3) * (X / localTau X theta)) / J) ^ 2 := by
    apply div_nonneg
    · exact mul_nonneg hX.le
        (halfOpenZeroStripPhysicalSecondMoment_nonneg hX)
    · positivity
  have hReal := ENNReal.toReal_mono (by simp) hm
  rw [ENNReal.toReal_ofReal hRhsNonneg] at hReal
  simpa only [equation27StripMeasure] using hReal

/-- Real-valued form of the exact equation-(2.7) L⁴ Markov estimate. -/
theorem equation27StripMeasure_le_fourthMoment
    {J : ℕ} (hJ : 0 < J) {j : ℕ} {theta delta X : ℝ}
    (hdelta : 0 < delta) (hdeltaOne : delta < 1) (hX : 0 < X) :
    equation27StripMeasure J j theta delta X ≤
      X * halfOpenZeroStripPhysicalFourthMoment
          ((j : ℝ) / J) ((j + 1 : ℕ) / J)
          (explicitFormulaHeight J theta X) (localTau X theta) X /
        (((delta / 3) * (X / localTau X theta)) / J) ^ 4 := by
  have hm := measure_equation27StripLargeSet_le_fourthMoment
    (j := j) (theta := theta) hJ hdelta hdeltaOne hX
  have hRhsNonneg :
      0 ≤ X * halfOpenZeroStripPhysicalFourthMoment
          ((j : ℝ) / J) ((j + 1 : ℕ) / J)
          (explicitFormulaHeight J theta X) (localTau X theta) X /
        (((delta / 3) * (X / localTau X theta)) / J) ^ 4 := by
    apply div_nonneg
    · exact mul_nonneg hX.le
        (halfOpenZeroStripPhysicalFourthMoment_nonneg hX)
    · positivity
  have hReal := ENNReal.toReal_mono (by simp) hm
  rw [ENNReal.toReal_ofReal hRhsNonneg] at hReal
  simpa only [equation27StripMeasure] using hReal

/-- Exact power ledger behind the L² Markov alternative: the threshold
contributes `X^(1-2 theta)` after normalization. -/
theorem secondMarkovScale_identity
    {J : ℕ} (hJ : 0 < J) {theta delta X : ℝ}
    (hdelta : 0 < delta) (hX : 0 < X) :
    X / ((((delta / 3) * (X / localTau X theta)) / J) ^ 2) =
      (9 * (J : ℝ) ^ 2 / delta ^ 2) * X ^ (1 - 2 * theta) := by
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  have htau : 0 < localTau X theta := localTau_pos hX
  have htauPow : localTau X theta ^ 2 = X ^ (2 * (1 - theta)) := by
    unfold localTau
    rw [← Real.rpow_natCast, ← Real.rpow_mul hX.le]
    congr 1
    ring
  have hXpow : X ^ (2 * (1 - theta)) / X = X ^ (1 - 2 * theta) := by
    calc
      X ^ (2 * (1 - theta)) / X =
          X ^ (2 * (1 - theta)) / X ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = X ^ (2 * (1 - theta) - 1) :=
        (Real.rpow_sub hX (2 * (1 - theta)) 1).symm
      _ = X ^ (1 - 2 * theta) := by
        congr 1
        ring
  rw [show X / ((((delta / 3) * (X / localTau X theta)) / J) ^ 2) =
      (9 * (J : ℝ) ^ 2 / delta ^ 2) *
        (localTau X theta ^ 2 / X) by
    field_simp [hJr.ne', hdelta.ne', hX.ne', htau.ne']
    ring]
  rw [htauPow, hXpow]

/-- Exact power ledger behind the L⁴ Markov alternative: the threshold
contributes `X^(1-4 theta)` after normalization. -/
theorem fourthMarkovScale_identity
    {J : ℕ} (hJ : 0 < J) {theta delta X : ℝ}
    (hdelta : 0 < delta) (hX : 0 < X) :
    X / ((((delta / 3) * (X / localTau X theta)) / J) ^ 4) =
      (81 * (J : ℝ) ^ 4 / delta ^ 4) * X ^ (1 - 4 * theta) := by
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  have htau : 0 < localTau X theta := localTau_pos hX
  have htauPow : localTau X theta ^ 4 = X ^ (4 * (1 - theta)) := by
    unfold localTau
    rw [← Real.rpow_natCast, ← Real.rpow_mul hX.le]
    congr 1
    ring
  have hXpow : X ^ (4 * (1 - theta)) / X ^ (3 : ℕ) =
      X ^ (1 - 4 * theta) := by
    rw [← Real.rpow_natCast]
    calc
      X ^ (4 * (1 - theta)) / X ^ (3 : ℝ) =
          X ^ (4 * (1 - theta) - 3) :=
            (Real.rpow_sub hX (4 * (1 - theta)) 3).symm
      _ = X ^ (1 - 4 * theta) := by
        congr 1
        ring
  rw [show X / ((((delta / 3) * (X / localTau X theta)) / J) ^ 4) =
      (81 * (J : ℝ) ^ 4 / delta ^ 4) *
        (localTau X theta ^ 4 / X ^ (3 : ℕ)) by
    field_simp [hJr.ne', hdelta.ne', hX.ne', htau.ne']
    ring]
  rw [htauPow, hXpow]

/-- The L² alternative in equation (2.7), now for the literal half-open strip
event and with the normalized moment, threshold, and `2/J` displacement all
assembled into the source exponent. -/
theorem equation27StripMeasure_second_epsilonBound
    (cutoff : GMSmoothCutoff)
    {J : ℕ} (hJ : 0 < J) {j : ℕ} {theta delta a : ℝ}
    (htheta : theta < 1) (hdelta : 0 < delta) (hdeltaOne : delta < 1)
    (ha : 0 ≤ a)
    (hsigmaLower : 0 ≤ (j : ℝ) / J)
    (hsigmaUpper : ((j + 1 : ℕ) : ℝ) / J ≤ 1)
    (hDensity : ZeroDensityEnvelope ((j : ℝ) / J) a) :
    EpsilonExponentBound
      (fun X => equation27StripMeasure J j theta delta X)
      ((1 - theta) * (a * (1 - (j : ℝ) / J)) +
        2 * (((j + 1 : ℕ) : ℝ) / J) - 1) := by
  let sigmaLower : ℝ := (j : ℝ) / J
  let sigmaUpper : ℝ := ((j + 1 : ℕ) : ℝ) / J
  let moment : ℝ → ℝ := fun X =>
    halfOpenZeroStripPhysicalSecondMoment sigmaLower sigmaUpper
      (explicitFormulaHeight J theta X) (localTau X theta) X
  let k : ℝ := 1 - 2 * theta
  let e : ℝ := (1 - theta) * (a * (1 - sigmaLower)) +
    2 * theta + 2 * sigmaUpper - 2
  let C : ℝ := 9 * (J : ℝ) ^ 2 / delta ^ 2
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  have hsigmaOrder : sigmaLower ≤ sigmaUpper := by
    dsimp [sigmaLower, sigmaUpper]
    exact (div_le_div_iff_of_pos_right hJr).2 (by exact_mod_cast Nat.le_succ j)
  have hMoment : EpsilonExponentBound moment e := by
    dsimp [moment, e, sigmaLower, sigmaUpper]
    exact halfOpenZeroStripPhysicalSecondMoment_epsilonBound cutoff
      (by exact_mod_cast hJ) htheta ha hsigmaLower hsigmaOrder hsigmaUpper hDensity
  have hDomination :
      RiemannZeta.GuthMaynard.EpsilonPowerBound
        (fun X => equation27StripMeasure J j theta delta X)
        (fun X => X ^ k * moment X) := by
    intro eps heps
    have hFixed :
        (fun X : ℝ => |equation27StripMeasure J j theta delta X|) =O[Filter.atTop]
          (fun X : ℝ => |X ^ k * moment X|) := by
      apply Asymptotics.IsBigO.of_bound C
      filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with X hX
      have hPoint := equation27StripMeasure_le_secondMoment
        (j := j) (theta := theta) hJ hdelta hdeltaOne hX
      have hScale := secondMarkovScale_identity (theta := theta) hJ hdelta hX
      have hPoint' : equation27StripMeasure J j theta delta X ≤
          C * (X ^ k * moment X) := by
        calc
          equation27StripMeasure J j theta delta X ≤
              X * moment X /
                ((((delta / 3) * (X / localTau X theta)) / J) ^ 2) := by
            simpa [moment, sigmaLower, sigmaUpper] using hPoint
          _ = (X / ((((delta / 3) * (X / localTau X theta)) / J) ^ 2)) *
              moment X := by ring
          _ = C * (X ^ k * moment X) := by
            rw [hScale]
            simp only [C, k]
            ring
      have hMeasureNonneg : 0 ≤ equation27StripMeasure J j theta delta X := by
        unfold equation27StripMeasure
        positivity
      have hMomentNonneg : 0 ≤ moment X := by
        dsimp [moment]
        exact halfOpenZeroStripPhysicalSecondMoment_nonneg hX
      have hScaledNonneg : 0 ≤ X ^ k * moment X :=
        mul_nonneg (Real.rpow_nonneg hX.le _) hMomentNonneg
      rw [Real.norm_eq_abs, abs_abs, abs_of_nonneg hMeasureNonneg,
        Real.norm_eq_abs, abs_abs, abs_of_nonneg hScaledNonneg]
      simpa [C] using hPoint'
    exact hFixed.trans
      ((RiemannZeta.GuthMaynard.EpsilonPowerBound.refl
        (fun X => X ^ k * moment X)) eps heps)
  have hScaled := hMoment.mul_left_rpow k
  have hScaledTarget :
      RiemannZeta.GuthMaynard.EpsilonPowerBound
        (fun X => X ^ k * moment X)
        (fun X => X ^
          ((1 - theta) * (a * (1 - (j : ℝ) / J)) +
            2 * (((j + 1 : ℕ) : ℝ) / J) - 1)) := by
    intro eps heps
    have H := hScaled eps heps
    apply H.congr'
    · exact Filter.Eventually.of_forall fun _ => rfl
    · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with X hX
      dsimp [k, e, sigmaLower, sigmaUpper]
      rw [← Real.rpow_add hX]
      congr 1
      ring_nf
  exact hDomination.trans hScaledTarget

/-- The L⁴ alternative in equation (2.7), with the literal half-open strip,
the exact fourth-moment threshold loss, and the full `4/J` displacement. -/
theorem equation27StripMeasure_fourth_epsilonBound
    (cutoff : GMSmoothCutoff)
    {J : ℕ} (hJ : 0 < J) {j : ℕ} {theta delta a : ℝ}
    (htheta : theta < 1) (hdelta : 0 < delta) (hdeltaOne : delta < 1)
    (ha : 0 ≤ a)
    (hsigmaLower : 1 / 2 ≤ (j : ℝ) / J)
    (hsigmaUpper : ((j + 1 : ℕ) : ℝ) / J ≤ 1)
    (hEnergy : ZeroAdditiveEnergyEnvelope ((j : ℝ) / J) a) :
    EpsilonExponentBound
      (fun X => equation27StripMeasure J j theta delta X)
      ((1 - theta) * (a * (1 - (j : ℝ) / J)) +
        4 * (((j + 1 : ℕ) : ℝ) / J) - 3) := by
  let sigmaLower : ℝ := (j : ℝ) / J
  let sigmaUpper : ℝ := ((j + 1 : ℕ) : ℝ) / J
  let moment : ℝ → ℝ := fun X =>
    halfOpenZeroStripPhysicalFourthMoment sigmaLower sigmaUpper
      (explicitFormulaHeight J theta X) (localTau X theta) X
  let k : ℝ := 1 - 4 * theta
  let e : ℝ := (1 - theta) * (a * (1 - sigmaLower)) +
    4 * theta + 4 * sigmaUpper - 4
  let C : ℝ := 81 * (J : ℝ) ^ 4 / delta ^ 4
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  have hsigmaOrder : sigmaLower ≤ sigmaUpper := by
    dsimp [sigmaLower, sigmaUpper]
    exact (div_le_div_iff_of_pos_right hJr).2 (by exact_mod_cast Nat.le_succ j)
  have hMoment : EpsilonExponentBound moment e := by
    dsimp [moment, e, sigmaLower, sigmaUpper]
    exact halfOpenZeroStripPhysicalFourthMoment_epsilonBound cutoff
      (by exact_mod_cast hJ) htheta ha hsigmaLower hsigmaOrder hsigmaUpper hEnergy
  have hDomination :
      RiemannZeta.GuthMaynard.EpsilonPowerBound
        (fun X => equation27StripMeasure J j theta delta X)
        (fun X => X ^ k * moment X) := by
    intro eps heps
    have hFixed :
        (fun X : ℝ => |equation27StripMeasure J j theta delta X|) =O[Filter.atTop]
          (fun X : ℝ => |X ^ k * moment X|) := by
      apply Asymptotics.IsBigO.of_bound C
      filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with X hX
      have hPoint := equation27StripMeasure_le_fourthMoment
        (j := j) (theta := theta) hJ hdelta hdeltaOne hX
      have hScale := fourthMarkovScale_identity (theta := theta) hJ hdelta hX
      have hPoint' : equation27StripMeasure J j theta delta X ≤
          C * (X ^ k * moment X) := by
        calc
          equation27StripMeasure J j theta delta X ≤
              X * moment X /
                ((((delta / 3) * (X / localTau X theta)) / J) ^ 4) := by
            simpa [moment, sigmaLower, sigmaUpper] using hPoint
          _ = (X / ((((delta / 3) * (X / localTau X theta)) / J) ^ 4)) *
              moment X := by ring
          _ = C * (X ^ k * moment X) := by
            rw [hScale]
            simp only [C, k]
            ring
      have hMeasureNonneg : 0 ≤ equation27StripMeasure J j theta delta X := by
        unfold equation27StripMeasure
        positivity
      have hMomentNonneg : 0 ≤ moment X := by
        dsimp [moment]
        exact halfOpenZeroStripPhysicalFourthMoment_nonneg hX
      have hScaledNonneg : 0 ≤ X ^ k * moment X :=
        mul_nonneg (Real.rpow_nonneg hX.le _) hMomentNonneg
      rw [Real.norm_eq_abs, abs_abs, abs_of_nonneg hMeasureNonneg,
        Real.norm_eq_abs, abs_abs, abs_of_nonneg hScaledNonneg]
      simpa [C] using hPoint'
    exact hFixed.trans
      ((RiemannZeta.GuthMaynard.EpsilonPowerBound.refl
        (fun X => X ^ k * moment X)) eps heps)
  have hScaled := hMoment.mul_left_rpow k
  have hScaledTarget :
      RiemannZeta.GuthMaynard.EpsilonPowerBound
        (fun X => X ^ k * moment X)
        (fun X => X ^
          ((1 - theta) * (a * (1 - (j : ℝ) / J)) +
            4 * (((j + 1 : ℕ) : ℝ) / J) - 3)) := by
    intro eps heps
    have H := hScaled eps heps
    apply H.congr'
    · exact Filter.Eventually.of_forall fun _ => rfl
    · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with X hX
      dsimp [k, e, sigmaLower, sigmaUpper]
      rw [← Real.rpow_add hX]
      congr 1
      ring_nf
  exact hDomination.trans hScaledTarget

/-- The two moment alternatives in the finite equation-(2.7) assembly.  The
input inequalities are precisely the source's `mu_2 <= mu` or `mu_4 <= mu`;
the theorem derives, rather than assumes, the strip displacement losses
`2/J` and `4/J` and returns the common `mu + 4/J` bound. -/
theorem equation27StripMeasure_epsilonBound_of_second_or_fourth
    (cutoff : GMSmoothCutoff)
    {J j : ℕ} (hJ : 0 < J) (hj : j < J)
    {theta delta aOrd aEnergy mu : ℝ}
    (htheta : theta < 1) (hdelta : 0 < delta) (hdeltaOne : delta < 1)
    (haOrd : 0 ≤ aOrd) (haEnergy : 0 ≤ aEnergy)
    (hsigmaLower : 1 / 2 ≤ (j : ℝ) / J)
    (hDensity : ZeroDensityEnvelope ((j : ℝ) / J) aOrd)
    (hEnergy : ZeroAdditiveEnergyEnvelope ((j : ℝ) / J) aEnergy)
    (hAlternative :
      (1 - theta) * (aOrd * (1 - (j : ℝ) / J)) +
          2 * ((j : ℝ) / J) - 1 ≤ mu ∨
        (1 - theta) * (aEnergy * (1 - (j : ℝ) / J)) +
          4 * ((j : ℝ) / J) - 3 ≤ mu) :
    EpsilonExponentBound
      (fun X => equation27StripMeasure J j theta delta X)
      (mu + 4 / J) := by
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  have hsigmaUpper : ((j + 1 : ℕ) : ℝ) / J ≤ 1 := by
    rw [div_le_one hJr]
    exact_mod_cast Nat.succ_le_iff.mpr hj
  have hsigmaNonneg : 0 ≤ (j : ℝ) / J :=
    le_trans (by norm_num : (0 : ℝ) ≤ 1 / 2) hsigmaLower
  rcases hAlternative with hSecond | hFourth
  · have hBound := equation27StripMeasure_second_epsilonBound cutoff
      hJ htheta hdelta hdeltaOne haOrd hsigmaNonneg hsigmaUpper hDensity
    apply hBound.mono_exponent
    have hCast : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by norm_num
    rw [hCast]
    calc
      (1 - theta) * (aOrd * (1 - (j : ℝ) / J)) +
          2 * (((j : ℝ) + 1) / J) - 1 =
        ((1 - theta) * (aOrd * (1 - (j : ℝ) / J)) +
          2 * ((j : ℝ) / J) - 1) + 2 / J := by ring
      _ ≤ mu + 2 / J := by linarith
      _ ≤ mu + 4 / J := by
        have htwofour : (2 : ℝ) / J ≤ 4 / J :=
          (div_le_div_iff_of_pos_right hJr).2 (by norm_num)
        linarith
  · have hBound := equation27StripMeasure_fourth_epsilonBound cutoff
      hJ htheta hdelta hdeltaOne haEnergy hsigmaLower hsigmaUpper hEnergy
    apply hBound.mono_exponent
    have hCast : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by norm_num
    rw [hCast]
    calc
      (1 - theta) * (aEnergy * (1 - (j : ℝ) / J)) +
          4 * (((j : ℝ) + 1) / J) - 3 =
        ((1 - theta) * (aEnergy * (1 - (j : ℝ) / J)) +
          4 * ((j : ℝ) / J) - 3) + 4 / J := by ring
      _ ≤ mu + 4 / J := by linarith

/-- Source-exponent form of the two moment alternatives.  The finite real
coefficients are strict upper approximants to the genuine extended-real
`A(sigma)` and `A*(sigma)`; their analytic envelopes are extracted from the
defining infima inside this theorem. -/
theorem equation27StripMeasure_epsilonBound_of_exponent_upper_bounds
    (cutoff : GMSmoothCutoff)
    {J j : ℕ} (hJ : 0 < J) (hj : j < J)
    {theta delta aOrd aEnergy mu : ℝ}
    (htheta : theta < 1) (hdelta : 0 < delta) (hdeltaOne : delta < 1)
    (haOrd : 0 ≤ aOrd) (haEnergy : 0 ≤ aEnergy)
    (hsigmaLower : 1 / 2 ≤ (j : ℝ) / J)
    (hOrdinaryExponent : zeroDensityExponent ((j : ℝ) / J) < (aOrd : EReal))
    (hEnergyExponent :
      zeroAdditiveEnergyExponent ((j : ℝ) / J) < (aEnergy : EReal))
    (hAlternative :
      (1 - theta) * (aOrd * (1 - (j : ℝ) / J)) +
          2 * ((j : ℝ) / J) - 1 ≤ mu ∨
        (1 - theta) * (aEnergy * (1 - (j : ℝ) / J)) +
          4 * ((j : ℝ) / J) - 3 ≤ mu) :
    EpsilonExponentBound
      (fun X => equation27StripMeasure J j theta delta X)
      (mu + 4 / J) := by
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  have hsigmaUpper : (j : ℝ) / J ≤ 1 := by
    rw [div_le_one hJr]
    exact_mod_cast hj.le
  have hDensity : ZeroDensityEnvelope ((j : ℝ) / J) aOrd :=
    zeroDensityEnvelope_of_zeroDensityExponent_lt hsigmaUpper hOrdinaryExponent
  have hEnergy : ZeroAdditiveEnergyEnvelope ((j : ℝ) / J) aEnergy :=
    zeroAdditiveEnergyEnvelope_of_zeroAdditiveEnergyExponent_lt
      hsigmaUpper hEnergyExponent
  exact equation27StripMeasure_epsilonBound_of_second_or_fourth cutoff
    hJ hj htheta hdelta hdeltaOne haOrd haEnergy hsigmaLower hDensity hEnergy
      hAlternative

end GafniTao
