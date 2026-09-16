import Tao2026.LinearAxisTypeIISourceBlock
import Tao2026.TypeISourceBlock

/-!
# Pure-linear Type I bridge

This file specializes the existing Type I high/low machinery to a nonzero
linear reciprocal coefficient and zero quadratic coefficient.  The block
cover and scalar majorants remain unchanged; empty derivative-critical sets
replace the nonzero-quadratic analytic input.
-/

open ArithmeticFunction Complex Finset Filter Topology
open scoped BigOperators zeta

namespace Tao2026

noncomputable section

set_option maxHeartbeats 800000

theorem reciprocalPhaseScale_pos_zero_quadratic
    {N X : ℝ} (hN : N ≠ 0) (hX : 0 < X) :
    0 < reciprocalPhaseScale N 0 2 X := by
  unfold reciprocalPhaseScale
  positivity

/-- The source error budget controls the pure-linear four-step effective
error throughout a dyadic window. -/
theorem reciprocalPhaseFourStepEffectiveErrorScale_zero_quadratic_le_one_of_dyadic
    (N : ℝ) {L : ℕ} {X Y : ℝ}
    (hX : 0 < X) (hY : 0 < Y) (hXY : X ≤ Y) (hYtop : Y ≤ 2 * X)
    (hN : N ≠ 0) (hLength : 1 ≤ L)
    (hbudget :
      240 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
          (reciprocalPhaseScale N 0 2 X / X ^ 5) +
        1 / 16 + 4 / reciprocalPhaseScale N 0 2 X ≤ 1) :
    reciprocalPhaseFourStepEffectiveErrorScale N 0 2 Y L ≤ 1 := by
  have hFX : 0 < reciprocalPhaseScale N 0 2 X :=
    reciprocalPhaseScale_pos_zero_quadratic hN hX
  have hFY : 0 < reciprocalPhaseScale N 0 2 Y :=
    reciprocalPhaseScale_pos_zero_quadratic hN hY
  have hscaleUpper : reciprocalPhaseScale N 0 2 Y ≤
      reciprocalPhaseScale N 0 2 X :=
    reciprocalPhaseScale_anti N 0 2 hX hXY
  have hpow : X ^ 5 ≤ Y ^ 5 := pow_le_pow_left₀ hX.le hXY 5
  have hupper : reciprocalPhaseScale N 0 2 Y / Y ^ 5 ≤
      reciprocalPhaseScale N 0 2 X / X ^ 5 := by
    calc
      reciprocalPhaseScale N 0 2 Y / Y ^ 5 ≤
          reciprocalPhaseScale N 0 2 X / Y ^ 5 :=
        div_le_div_of_nonneg_right hscaleUpper (pow_pos hY 5).le
      _ ≤ reciprocalPhaseScale N 0 2 X / X ^ 5 :=
        div_le_div_of_nonneg_left hFX.le (pow_pos hX 5) hpow
  have hscaleLower : reciprocalPhaseScale N 0 2 X ≤
      4 * reciprocalPhaseScale N 0 2 Y :=
    reciprocalPhaseScale_quadratic_le_four_mul_of_le_two_mul
      N 0 hX hY hYtop
  have hinv : 1 / reciprocalPhaseScale N 0 2 Y ≤
      4 / reciprocalPhaseScale N 0 2 X := by
    rw [div_le_div_iff₀ hFY hFX]
    simpa only [one_mul] using hscaleLower
  have hraw := reciprocalPhaseFourStepEffectiveErrorScale_le_of_scale_bounds
    N 0 Y (reciprocalPhaseScale N 0 2 X / X ^ 5)
      (4 / reciprocalPhaseScale N 0 2 X) 2 L hupper hinv hLength
  exact hraw.trans hbudget

/-- Pure-linear five-fit wrapper with the same two-term output used by the
existing Type I scalar ledger. -/
theorem norm_reciprocalPhaseSum_zero_quadratic_le_fourStepWeyl_twoTerm_of_five_fit
    (N : ℝ) (orders : Finset ℕ) (a b : ℕ) {X : ℝ}
    (hN : N ≠ 0) (hX : 0 < X)
    (hFlow : reciprocalPhaseScale N 0 2 X ≤ X ^ 4)
    (herrorSmall :
      reciprocalPhaseFourStepEffectiveErrorScale N 0 2 X (b - a) ≤ 1)
    (hLength : 1 ≤ b - a) (ha : X ≤ (a : ℝ))
    (hfit : (a : ℝ) + 5 * (b - a : ℕ) ≤ 2 * X)
    (hrFive : 5 ∈ orders) (hrSix : 6 ∈ orders) :
    let p := reciprocalPhaseFourStepTwoTermWidth N 0 2 X
    ‖reciprocalPhaseSum N 0 2 a b‖ ≤
      ((370 * orders.card + 173 : ℕ) : ℝ) *
        (480 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
          (((((5 + 2) ^ 5 : ℕ) : ℝ)) + 1) *
          (1 + Real.log ((b - a : ℕ) : ℝ)) * X * p) := by
  have hF : 0 < reciprocalPhaseScale N 0 2 X :=
    reciprocalPhaseScale_pos_zero_quadratic hN hX
  have hrangeNat :
      reciprocalPhaseFourStepOptimizedRange N 0 2 X (b - a) ≤ b - a :=
    reciprocalPhaseFourStepOptimizedRange_le_length N 0 hX hF herrorSmall
  have hrange :
      (4 * reciprocalPhaseFourStepOptimizedRange N 0 2 X (b - a) : ℕ) ≤
        4 * (b - a) := Nat.mul_le_mul_left 4 hrangeNat
  have hrangeReal :
      ((4 * reciprocalPhaseFourStepOptimizedRange N 0 2 X (b - a) : ℕ) : ℝ) ≤
        4 * (b - a : ℕ) := by exact_mod_cast hrange
  have haTop : (a : ℝ) ≤ 2 * X := by
    have hlengthNonneg : (0 : ℝ) ≤ 5 * (b - a : ℕ) := by positivity
    linarith
  have heval : (a : ℝ) + (b - a : ℕ) +
      (4 * reciprocalPhaseFourStepOptimizedRange N 0 2 X (b - a) : ℕ) ≤
        2 * X := by
    calc
      (a : ℝ) + (b - a : ℕ) +
          (4 * reciprocalPhaseFourStepOptimizedRange N 0 2 X (b - a) : ℕ) ≤
        (a : ℝ) + (b - a : ℕ) + 4 * (b - a : ℕ) := by linarith
      _ = (a : ℝ) + 5 * (b - a : ℕ) := by ring
      _ ≤ 2 * X := hfit
  exact norm_reciprocalPhaseSum_zero_quadratic_le_fourStepWeyl_twoTerm
    N orders a b hN hX hFlow herrorSmall hLength ⟨ha, haTop⟩ heval heval
      hrFive hrSix

/-- The factor-four dyadic comparison uniformizes the pure-linear local Weyl
width by the existing Type I source width. -/
theorem reciprocalPhaseFourStepTwoTermWidth_zero_quadratic_le_sourceWidth_of_dyadic
    (N : ℝ) {D Y : ℝ} (hN : N ≠ 0) (hD : 0 < D) (hY : 0 < Y)
    (hDY : D ≤ Y) (hYtop : Y ≤ 2 * D) :
    reciprocalPhaseFourStepTwoTermWidth N 0 2 Y ≤
      (reciprocalPhaseScale N 0 2 D / D ^ 5 +
        4 / reciprocalPhaseScale N 0 2 D) ^ (1 / 1024 : ℝ) := by
  have hFD := reciprocalPhaseScale_pos_zero_quadratic hN hD
  have hFY := reciprocalPhaseScale_pos_zero_quadratic hN hY
  have hscaleUpper : reciprocalPhaseScale N 0 2 Y ≤
      reciprocalPhaseScale N 0 2 D := reciprocalPhaseScale_anti N 0 2 hD hDY
  have hpow : D ^ 5 ≤ Y ^ 5 := pow_le_pow_left₀ hD.le hDY 5
  have hupper : reciprocalPhaseScale N 0 2 Y / Y ^ 5 ≤
      reciprocalPhaseScale N 0 2 D / D ^ 5 := by
    calc
      reciprocalPhaseScale N 0 2 Y / Y ^ 5 ≤
          reciprocalPhaseScale N 0 2 D / Y ^ 5 :=
        div_le_div_of_nonneg_right hscaleUpper (pow_pos hY 5).le
      _ ≤ reciprocalPhaseScale N 0 2 D / D ^ 5 :=
        div_le_div_of_nonneg_left hFD.le (pow_pos hD 5) hpow
  have hscaleLower : reciprocalPhaseScale N 0 2 D ≤
      4 * reciprocalPhaseScale N 0 2 Y :=
    reciprocalPhaseScale_quadratic_le_four_mul_of_le_two_mul N 0 hD hY hYtop
  have hinv : 1 / reciprocalPhaseScale N 0 2 Y ≤
      4 / reciprocalPhaseScale N 0 2 D := by
    rw [div_le_div_iff₀ hFY hFD]
    simpa only [one_mul] using hscaleLower
  unfold reciprocalPhaseFourStepTwoTermWidth reciprocalPhaseFourStepTwoTermError
  apply Real.rpow_le_rpow
  · positivity
  · exact add_le_add hupper hinv
  · norm_num

/-- Uniform pure-linear bound for one piece of an arbitrary Type I dyadic
subinterval. -/
theorem norm_reciprocalPhaseSum_typeIQuadraticWeylSubBlock_le_uniform_zero_quadratic
    (N : ℝ) (orders : Finset ℕ) {D a b k : ℕ}
    (hD : 10 ≤ D) (hDa : D ≤ a) (hbD : b ≤ 2 * D) (hN : N ≠ 0)
    (hFlow : reciprocalPhaseScale N 0 2 D ≤ (D : ℝ) ^ 4)
    (hbudget :
      240 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
          (reciprocalPhaseScale N 0 2 D / (D : ℝ) ^ 5) +
        1 / 16 + 4 / reciprocalPhaseScale N 0 2 D ≤ 1)
    (hrFive : 5 ∈ orders) (hrSix : 6 ∈ orders) :
    ‖reciprocalPhaseSum N 0 2
        (typeIQuadraticWeylSubBlockLower D a k)
        (typeIQuadraticWeylSubBlockUpper D a b k)‖ ≤
      typeIQuadraticWeylUniformBlockMajorant N 0 orders D := by
  let lo := typeIQuadraticWeylSubBlockLower D a k
  let hi := typeIQuadraticWeylSubBlockUpper D a b k
  by_cases hLength : 1 ≤ hi - lo
  · have hgeom := typeIQuadraticWeylSubBlock_geometry hD hDa hbD hLength
    dsimp only at hgeom
    rcases hgeom with ⟨hDloNat, hloTopNat, hlength, hfitNat⟩
    have hDposNat : 0 < D := by omega
    have hDpos : (0 : ℝ) < D := by exact_mod_cast hDposNat
    have hloposNat : 0 < lo := hDposNat.trans_le hDloNat
    have hlopos : (0 : ℝ) < lo := by exact_mod_cast hloposNat
    have hDlo : (D : ℝ) ≤ lo := by exact_mod_cast hDloNat
    have hloTop : (lo : ℝ) ≤ 2 * D := by exact_mod_cast hloTopNat
    have hlocalScalePos : 0 < reciprocalPhaseScale N 0 2 lo :=
      reciprocalPhaseScale_pos_zero_quadratic hN hlopos
    have hscaleUpper : reciprocalPhaseScale N 0 2 lo ≤
        reciprocalPhaseScale N 0 2 D := reciprocalPhaseScale_anti N 0 2 hDpos hDlo
    have hpow : (D : ℝ) ^ 4 ≤ (lo : ℝ) ^ 4 :=
      pow_le_pow_left₀ hDpos.le hDlo 4
    have hFlowLocal : reciprocalPhaseScale N 0 2 lo ≤ (lo : ℝ) ^ 4 :=
      hscaleUpper.trans (hFlow.trans hpow)
    have herrorSmall : reciprocalPhaseFourStepEffectiveErrorScale
        N 0 2 lo (hi - lo) ≤ 1 :=
      reciprocalPhaseFourStepEffectiveErrorScale_zero_quadratic_le_one_of_dyadic
        N hDpos hlopos hDlo hloTop hN hLength hbudget
    have hfit : (lo : ℝ) + 5 * (hi - lo : ℕ) ≤ 2 * (lo : ℝ) := by
      exact_mod_cast hfitNat
    have hbase :=
      norm_reciprocalPhaseSum_zero_quadratic_le_fourStepWeyl_twoTerm_of_five_fit
        N orders lo hi hN hlopos hFlowLocal herrorSmall hLength le_rfl hfit
          hrFive hrSix
    have hqD : dyadicShortIntervalLength D 10 ≤ D := by
      unfold dyadicShortIntervalLength
      exact ceilDiv_le_self_of_pos D 10 (by norm_num)
    have hlengthD : hi - lo ≤ D := hlength.trans hqD
    have hlog : Real.log ((hi - lo : ℕ) : ℝ) ≤ Real.log (D : ℝ) :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < hi - lo))
        (by exact_mod_cast hlengthD)
    have hwidth : reciprocalPhaseFourStepTwoTermWidth N 0 2 lo ≤
        typeIQuadraticWeylSourceWidth N 0 D := by
      unfold typeIQuadraticWeylSourceWidth
      exact reciprocalPhaseFourStepTwoTermWidth_zero_quadratic_le_sourceWidth_of_dyadic
        N hN hDpos hlopos hDlo hloTop
    dsimp only at hbase
    refine hbase.trans ?_
    unfold typeIQuadraticWeylUniformBlockMajorant
    have hlogNonneg : 0 ≤ 1 + Real.log ((hi - lo : ℕ) : ℝ) := by
      have hone : (1 : ℝ) ≤ (hi - lo : ℕ) := by exact_mod_cast hLength
      linarith [Real.log_nonneg hone]
    have hsourceNonneg := typeIQuadraticWeylSourceWidth_nonneg N 0 D
    have hwidthNonneg : 0 ≤ reciprocalPhaseFourStepTwoTermWidth N 0 2 lo :=
      (reciprocalPhaseFourStepTwoTermWidth_pos N 0 hlopos hlocalScalePos).le
    gcongr
  · have hle : hi ≤ lo := by omega
    have hzero : reciprocalPhaseSum N 0 2 lo hi = 0 := by
      have hIco : Finset.Ico lo hi = ∅ := Finset.Ico_eq_empty (Nat.not_lt.mpr hle)
      simp [reciprocalPhaseSum, hIco]
    change ‖reciprocalPhaseSum N 0 2 lo hi‖ ≤ _
    rw [hzero, norm_zero]
    exact typeIQuadraticWeylUniformBlockMajorant_nonneg N 0 orders (by omega)

/-- Uniform pure-linear Weyl bound on every subinterval of `[D,2D)`. -/
theorem norm_reciprocalPhaseSum_subinterval_le_typeIQuadraticWeylSource_zero_quadratic
    (N : ℝ) (orders : Finset ℕ) {D a b : ℕ}
    (hD : 10 ≤ D) (hDa : D ≤ a) (hbD : b ≤ 2 * D) (hN : N ≠ 0)
    (hFlow : reciprocalPhaseScale N 0 2 D ≤ (D : ℝ) ^ 4)
    (hbudget :
      240 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
          (reciprocalPhaseScale N 0 2 D / (D : ℝ) ^ 5) +
        1 / 16 + 4 / reciprocalPhaseScale N 0 2 D ≤ 1)
    (hrFive : 5 ∈ orders) (hrSix : 6 ∈ orders) :
    ‖reciprocalPhaseSum N 0 2 a b‖ ≤
      10 * typeIQuadraticWeylUniformBlockMajorant N 0 orders D := by
  have hDpos : 0 < D := by omega
  let count := shortIntervalBlockCount a b (dyadicShortIntervalLength D 10)
  have hcount : count ≤ 10 := by
    unfold count
    exact typeIQuadraticWeylSubBlockCount_le_ten hDpos hDa hbD
  calc
    ‖reciprocalPhaseSum N 0 2 a b‖ ≤
        ∑ k ∈ Finset.range count,
          ‖reciprocalPhaseSum N 0 2
            (typeIQuadraticWeylSubBlockLower D a k)
            (typeIQuadraticWeylSubBlockUpper D a b k)‖ := by
      simpa only [count] using
        norm_reciprocalPhaseSum_le_sum_typeIQuadraticWeylSubBlocks
          N 0 (a := a) (b := b) hDpos
    _ ≤ ∑ _k ∈ Finset.range count,
          typeIQuadraticWeylUniformBlockMajorant N 0 orders D := by
      apply Finset.sum_le_sum
      intro k _hk
      exact norm_reciprocalPhaseSum_typeIQuadraticWeylSubBlock_le_uniform_zero_quadratic
        N orders hD hDa hbD hN hFlow hbudget hrFive hrSix
    _ = (count : ℝ) * typeIQuadraticWeylUniformBlockMajorant N 0 orders D := by
      rw [Finset.sum_const, Finset.card_range]
      simp only [nsmul_eq_mul]
    _ ≤ 10 * typeIQuadraticWeylUniformBlockMajorant N 0 orders D := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast hcount
      · exact typeIQuadraticWeylUniformBlockMajorant_nonneg N 0 orders (by omega)

/-- High-scale pure-linear Vinogradov estimate on an arbitrary rounded Type I
subinterval, embedded in the existing source envelope. -/
theorem norm_reciprocalPhaseSum_subinterval_le_typeIQuadraticVinogradovAt_zero_quadratic
    (C : ℝ) (hVinogradov : VinogradovExponentialSumEstimateAt C)
    (Z A N : ℝ) {P m a b : ℕ}
    (hD : 2 ≤ P ⌈/⌉ m) (haD : P ⌈/⌉ m ≤ a)
    (hbD : b ≤ 2 * (P ⌈/⌉ m)) (hm : 0 < m) (hN : N ≠ 0)
    (hlog : 1 ≤ Real.log Z) (hA : 1 / 4 ≤ A)
    (hten : 10 ≤ (Real.log Z) ^ A)
    (hcutoff :
      let D := P ⌈/⌉ m
      let N' := N / m
      (((vinogradovDerivativeCutoff D
        (reciprocalPhaseScale N' 0 2 D) + 2 : ℕ) : ℝ)) ≤ Real.log Z)
    (hFhigh :
      let D := P ⌈/⌉ m
      let N' := N / m
      (D : ℝ) ^ 4 ≤ reciprocalPhaseScale N' 0 2 D)
    (hsmall :
      let D := P ⌈/⌉ m
      let N' := N / m
      Real.log ((Real.log Z) ^ (4 * A)) *
          (Real.log (reciprocalPhaseScale N' 0 2 D)) ^ 2 /
            (Real.log D) ^ 3 < (1 / 1000 : ℝ)) :
    ‖reciprocalPhaseSum (N / m) 0 2 a b‖ ≤
      typeIQuadraticRescaledVinogradovMajorantAt C Z A N 0 P m := by
  let D := P ⌈/⌉ m
  let N' := N / m
  have hN' : N' ≠ 0 := by
    unfold N'
    exact div_ne_zero hN (by exact_mod_cast hm.ne')
  have hraw := norm_reciprocalPhaseSum_zero_quadratic_le_sourceVinogradovAt
    C hVinogradov N' Z A D a b (by exact_mod_cast hD) hN' hlog hA hten
      (by simpa only [D, N'] using hcutoff)
      (by simpa only [D, N'] using hFhigh)
      (by simpa only [D, N'] using hsmall)
      (by exact_mod_cast haD) (by exact_mod_cast hbD)
  let R := C * (Real.log Z) ^ (4 * A) * (D : ℝ) * Real.exp
    (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log D) ^ 3 /
      (Real.log (reciprocalPhaseScale N' 0 2 D)) ^ 2)
  have hC : 0 ≤ C := hVinogradov.1.le
  have hR : 0 ≤ R := by unfold R; positivity
  have hfactor : 1 ≤ 2 * Real.log Z + 1 := by linarith
  have hdelete : 0 ≤ Real.log Z *
      (16 * (D : ℝ) * (Real.log Z) ^ (-3 * A) + Real.log Z + 1) := by
    positivity
  calc
    ‖reciprocalPhaseSum (N / m) 0 2 a b‖ ≤ R := by
      simpa only [D, N', R] using hraw
    _ ≤ (2 * Real.log Z + 1) * R + Real.log Z *
        (16 * (D : ℝ) * (Real.log Z) ^ (-3 * A) + Real.log Z + 1) := by
      have hmul := mul_le_mul_of_nonneg_right hfactor hR
      nlinarith
    _ = typeIQuadraticRescaledVinogradovMajorantAt C Z A N 0 P m := by
      unfold typeIQuadraticRescaledVinogradovMajorantAt R D N'
      simp only [zero_div]

/-- Branch-sensitive pure-linear Type I estimate on an arbitrary subinterval.
-/
theorem norm_reciprocalPhaseSum_subinterval_le_typeIQuadraticBranchAt_zero_quadratic
    (C : ℝ) (hVinogradov : VinogradovExponentialSumEstimateAt C)
    (Z A N : ℝ) {P m a b : ℕ}
    (haD : P ⌈/⌉ m ≤ a) (hbD : b ≤ 2 * (P ⌈/⌉ m))
    (hm : 0 < m) (hN : N ≠ 0)
    (hlog : 1 ≤ Real.log Z) (hA : 1 / 4 ≤ A)
    (hten : 10 ≤ (Real.log Z) ^ A)
    (hadm : TypeIQuadraticHybridAdmissible Z A N 0 P m)
    (hbudget :
      let D := P ⌈/⌉ m
      let N' := N / m
      reciprocalPhaseScale N' 0 2 D ≤ (D : ℝ) ^ 4 →
        240 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
            (reciprocalPhaseScale N' 0 2 D / (D : ℝ) ^ 5) +
          1 / 16 + 4 / reciprocalPhaseScale N' 0 2 D ≤ 1) :
    ‖reciprocalPhaseSum (N / m) 0 2 a b‖ ≤
      typeIQuadraticRescaledBranchMajorantAt C Z A N 0 P m := by
  let D := P ⌈/⌉ m
  let N' := N / m
  let F := reciprocalPhaseScale N' 0 2 D
  have hN' : N' ≠ 0 := by
    unfold N'
    exact div_ne_zero hN (by exact_mod_cast hm.ne')
  have hadm' : 10 ≤ D ∧
      ((F ≤ (D : ℝ) ^ 4 ∧
          240 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) * (F / (D : ℝ) ^ 5) +
            1 / 16 + 4 / F ≤ 1) ∨
        ((D : ℝ) ^ 4 ≤ F ∧
          ((((vinogradovDerivativeCutoff D F + 2 : ℕ) : ℝ)) ≤ Real.log Z) ∧
          Real.log ((Real.log Z) ^ (4 * A)) * (Real.log F) ^ 2 /
              (Real.log D) ^ 3 < (1 / 1000 : ℝ))) := by
    simpa only [TypeIQuadraticHybridAdmissible, D, N', F, zero_div,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using hadm
  by_cases hlow : F ≤ (D : ℝ) ^ 4
  · have hweyl :=
      norm_reciprocalPhaseSum_subinterval_le_typeIQuadraticWeylSource_zero_quadratic
        N' typeIQuadraticWeylOrders hadm'.1 haD hbD hN' hlow
          (by simpa only [D, N', F] using hbudget hlow)
          five_mem_typeIQuadraticWeylOrders six_mem_typeIQuadraticWeylOrders
    have hweyl' : ‖reciprocalPhaseSum (N / m) 0 2 a b‖ ≤
        typeIQuadraticRescaledWeylMajorant N 0 P m := by
      simpa only [typeIQuadraticRescaledWeylMajorant, D, N', zero_div,
        zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using hweyl
    simpa only [typeIQuadraticRescaledBranchMajorantAt, D, N', F, zero_div,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0), if_pos hlow] using hweyl'
  · have hhigh : (D : ℝ) ^ 4 ≤ F ∧
        ((((vinogradovDerivativeCutoff D F + 2 : ℕ) : ℝ)) ≤ Real.log Z) ∧
        Real.log ((Real.log Z) ^ (4 * A)) * (Real.log F) ^ 2 /
            (Real.log D) ^ 3 < (1 / 1000 : ℝ) := by
      rcases hadm'.2 with hbad | hgood
      · exact False.elim (hlow hbad.1)
      · exact hgood
    have hvin :=
      norm_reciprocalPhaseSum_subinterval_le_typeIQuadraticVinogradovAt_zero_quadratic
        C hVinogradov Z A N (P := P) (m := m) (a := a) (b := b)
          (by omega) haD hbD hm hN hlog hA hten
          (by simpa only [D, N', F] using hhigh.2.1)
          (by simpa only [D, N', F] using hhigh.1)
          (by simpa only [D, N', F] using hhigh.2.2)
    simpa only [typeIQuadraticRescaledBranchMajorantAt, D, N', F, zero_div,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0), if_neg hlow] using hvin

/-- Literal unweighted pure-linear Type I fiber estimate. -/
theorem norm_typeIProductRestrictedInnerSum_Ico_le_quadraticBranchAt_zero_quadratic
    (C : ℝ) (hVinogradov : VinogradovExponentialSumEstimateAt C)
    (Z A N : ℝ) {P a b B m : ℕ}
    (hPa : P ≤ a) (hbP : b ≤ 2 * P) (ha : 0 < a) (hbB : b ≤ B)
    (hm : 0 < m) (hN : N ≠ 0)
    (hlog : 1 ≤ Real.log Z) (hA : 1 / 4 ≤ A)
    (hten : 10 ≤ (Real.log Z) ^ A)
    (hadm : TypeIQuadraticHybridAdmissible Z A N 0 P m)
    (hbudget :
      let D := P ⌈/⌉ m
      let N' := N / m
      reciprocalPhaseScale N' 0 2 D ≤ (D : ℝ) ^ 4 →
        240 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
            (reciprocalPhaseScale N' 0 2 D / (D : ℝ) ^ 5) +
          1 / 16 + 4 / reciprocalPhaseScale N' 0 2 D ≤ 1) :
    ‖typeIProductRestrictedWeightedInnerSum
        (Finset.Ico a b) (Finset.Ioc 0 B) (fun _ => 1) N 0 2 m‖ ≤
      typeIQuadraticRescaledBranchMajorantAt C Z A N 0 P m := by
  rw [typeIProductRestrictedInnerSum_Ico_eq ha hbB hm]
  have hgeom := typeI_ceilDiv_dyadic_geometry hm hPa hbP
  simpa only [zero_div] using
    (norm_reciprocalPhaseSum_subinterval_le_typeIQuadraticBranchAt_zero_quadratic
      C hVinogradov Z A N hgeom.1 hgeom.2 hm hN hlog hA hten hadm hbudget)

/-- Literal logarithmically weighted pure-linear Type I fiber estimate. -/
theorem norm_typeIProductRestrictedLogInnerSum_Ico_le_quadraticBranchAt_zero_quadratic
    (C : ℝ) (hVinogradov : VinogradovExponentialSumEstimateAt C)
    (Z A N : ℝ) {P a b B m : ℕ}
    (hPa : P ≤ a) (hab : a ≤ b) (hbP : b ≤ 2 * P)
    (ha : 0 < a) (hbB : b ≤ B) (hm : 0 < m) (hN : N ≠ 0)
    (hC : 0 ≤ C) (hlog : 1 ≤ Real.log Z) (hA : 1 / 4 ≤ A)
    (hten : 10 ≤ (Real.log Z) ^ A)
    (hadm : TypeIQuadraticHybridAdmissible Z A N 0 P m)
    (hbudget :
      let D := P ⌈/⌉ m
      let N' := N / m
      reciprocalPhaseScale N' 0 2 D ≤ (D : ℝ) ^ 4 →
        240 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
            (reciprocalPhaseScale N' 0 2 D / (D : ℝ) ^ 5) +
          1 / 16 + 4 / reciprocalPhaseScale N' 0 2 D ≤ 1) :
    ‖typeIProductRestrictedWeightedInnerSum
        (Finset.Ico a b) (Finset.Ioc 0 B)
        (fun n => (Real.log n : ℂ)) N 0 2 m‖ ≤
      2 * Real.log ((b ⌈/⌉ m : ℕ) : ℝ) *
        typeIQuadraticRescaledBranchMajorantAt C Z A N 0 P m := by
  have hgeom := typeI_ceilDiv_dyadic_geometry hm hPa hbP
  have hDten : 10 ≤ P ⌈/⌉ m := by
    have h := hadm.1
    simpa only [TypeIQuadraticHybridAdmissible] using h
  have hR : 0 ≤ typeIQuadraticRescaledBranchMajorantAt C Z A N 0 P m :=
    typeIQuadraticRescaledBranchMajorantAt_nonneg hC (by linarith) (by omega)
  by_cases hceil : a ⌈/⌉ m < b ⌈/⌉ m
  · apply norm_typeIProductRestrictedLogInnerSum_Ico_le
      ha hbB hm N 0 2 hceil hR
    intro k hak hkb
    simpa only [zero_div] using
      (norm_reciprocalPhaseSum_subinterval_le_typeIQuadraticBranchAt_zero_quadratic
        C hVinogradov Z A N hgeom.1 (hkb.trans hgeom.2) hm hN hlog hA hten
          hadm hbudget)
  · have hle : b ⌈/⌉ m ≤ a ⌈/⌉ m := Nat.le_of_not_gt hceil
    have hIco : Finset.Ico (a ⌈/⌉ m) (b ⌈/⌉ m) = ∅ :=
      Finset.Ico_eq_empty (Nat.not_lt.mpr hle)
    rw [typeIProductRestrictedLogInnerSum_Ico_eq ha hbB hm]
    simp only [hIco, Finset.sum_empty, norm_zero]
    have hbpos : 0 < b := ha.trans_le hab
    have hceilPos : 0 < b ⌈/⌉ m := typeI_ceilDiv_pos hbpos hm
    have hlogb : 0 ≤ Real.log ((b ⌈/⌉ m : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hceilPos)
    positivity

/-- The complete prime-coefficient Vaughan Type I family in the pure-linear
chamber. -/
theorem eventually_norm_weightedConvolutionProductVaughanTypeIPrimeSum_le_source_zero_quadratic
    {C₀ C₁ ε A d T : ℝ}
    (hA : 1 / 4 ≤ A) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (hVinogradov : VinogradovExponentialSumEstimateAt C₁)
    (hε : 0 < ε) (haexp : 0 ≤ 3 / 2 - ε)
    (hAT : T + 2 ≤ 3 * A)
    (hd : 1024 * (T + 1) + 1 ≤ d) :
    ∀ᶠ B : ℕ in atTop, ∀ (P a b : ℕ) (N : ℝ),
      0 < P → P ≤ a → b ≤ 2 * P → 0 < a → b ≤ B →
      P ≤ B → B ≤ 2 * P → N ≠ 0 →
      64 ≤ reciprocalPhaseScale N 0 2 P →
      (Real.log B) ^ d ≤ reciprocalPhaseScale N 0 2 P →
      reciprocalPhaseScale N 0 2 P ≤
        C₀ * Real.exp ((Real.log B) ^ (3 / 2 - ε)) →
      ‖weightedConvolutionProductSum (Finset.Ico a b) B
          (fun n => standardAdditiveCharacter (reciprocalPhase N 0 2 n))
          (vaughanTypeIPrimeCoefficient
            (vaughanSourceTailCutoff B) (vaughanSourceTailCutoff B))
          (ζ : ArithmeticFunction ℝ)‖ ≤
        (Nat.log 2 B + 1 : ℕ) ^ 102 *
          (Real.log (2 * B) *
            ((P : ℝ) *
              (2 * typeIQuadraticBranchDecayConstant *
                (Real.log B) ^ (-T)) *
              ((harmonic
                (vaughanSourceTailCutoff B * vaughanSourceTailCutoff B) : ℚ) : ℝ))) := by
  let K : ℕ := ⌈2 * (240 * ((((5 + 2) ^ 5 : ℕ) : ℝ)))⌉₊
  have hadm := eventually_forall_activePrime_typeIQuadraticHybridAdmissible
    hA hC₀ hε haexp
  have hlarge := eventually_forall_activePrime_ceilDiv_ge K
  have hquarter := eventually_quarter_rpow_le_ceilDiv_of_activePrime
  have hmajor := eventually_typeIQuadraticRescaledBranchMajorantAt_le_invWeighted
    hC₀ hC₁ hε haexp hAT hd
  have hlog : ∀ᶠ B : ℕ in atTop, 1 ≤ Real.log (B : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 1)
  have hApos : 0 < A := by linarith
  have hten : ∀ᶠ B : ℕ in atTop, 10 ≤ (Real.log (B : ℝ)) ^ A :=
    ((tendsto_rpow_atTop hApos).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        (eventually_ge_atTop 10)
  filter_upwards [hadm, hlarge, hquarter, hmajor, hlog, hten,
    eventually_gt_atTop (0 : ℕ)] with
      B hadmB hlargeB hquarterB hmajorB hlogB htenB hB
  intro P a b N hP hPa hbP ha hbB hPB hBP hN hsource64 hsource hupper
  have hQ : 0 ≤
      2 * typeIQuadraticBranchDecayConstant * (Real.log B) ^ (-T) := by
    have hlogNonneg : 0 ≤ Real.log (B : ℝ) := by linarith
    exact mul_nonneg (mul_nonneg (by norm_num)
      typeIQuadraticBranchDecayConstant_pos.le)
        (Real.rpow_nonneg hlogNonneg _)
  apply norm_weightedConvolutionProductVaughanTypeIPrimeSum_le_invWeighted
    (Finset.Ico a b) B (vaughanSourceTailCutoff B)
      (vaughanSourceTailCutoff B) P hB N 0 2 hQ
  intro sk hsk m hmActive
  have hmpos : 0 < m := pos_of_mem_vaughanTypeIActiveProductBlockSupport hmActive
  have hD : K ≤ P ⌈/⌉ m := hlargeB P sk m hBP hmActive
  have htwoD : 2 ≤ P ⌈/⌉ m := by
    have hKtwo : 2 ≤ K := by norm_num [K]
    exact hKtwo.trans hD
  have hmP : m ≤ P := le_of_two_le_ceilDiv hmpos htwoD
  have hDreal : 2 * (240 * ((((5 + 2) ^ 5 : ℕ) : ℝ))) ≤
      ((P ⌈/⌉ m : ℕ) : ℝ) := by
    have hceil : 2 * (240 * ((((5 + 2) ^ 5 : ℕ) : ℝ))) ≤ (K : ℝ) := by
      norm_num [K]
    exact hceil.trans (by exact_mod_cast hD)
  have hadmFiber := hadmB P N 0 sk m hP hBP hsource64 hupper hmActive
  have hbudget :
      reciprocalPhaseScale (N / m) 0 2 ((P ⌈/⌉ m : ℕ) : ℝ) ≤
        ((P ⌈/⌉ m : ℕ) : ℝ) ^ 4 →
      240 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
          (reciprocalPhaseScale (N / m) 0 2 ((P ⌈/⌉ m : ℕ) : ℝ) /
            ((P ⌈/⌉ m : ℕ) : ℝ) ^ 5) +
        1 / 16 + 4 / reciprocalPhaseScale (N / m) 0 2
            ((P ⌈/⌉ m : ℕ) : ℝ) ≤ 1 := by
    intro hlow
    simpa only [zero_div] using
      (typeIQuadraticWeylBudget_of_sourceScale
        N 0 hP hmpos hmP hDreal hsource64 (by simpa only [zero_div] using hlow))
  have hlocalUpper := reciprocalPhaseScale_typeI_rescale_ceilDiv_le
    N 0 2 hP hmpos
  have hmajorFiber := hmajorB P m N 0 hP hmpos hmP hPB htwoD
    (hquarterB P sk m hBP hmActive) hsource (hlocalUpper.trans hupper)
  exact (norm_typeIProductRestrictedInnerSum_Ico_le_quadraticBranchAt_zero_quadratic
    C₁ hVinogradov B A N hPa hbP ha hbB hmpos hN
      hlogB hA htenB hadmFiber hbudget).trans hmajorFiber

/-- The complete logarithmically weighted Vaughan Type I family in the
pure-linear chamber. -/
theorem eventually_norm_weightedConvolutionProductVaughanTypeILogSum_le_source_zero_quadratic
    {C₀ C₁ ε A d T : ℝ}
    (hA : 1 / 4 ≤ A) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (hVinogradov : VinogradovExponentialSumEstimateAt C₁)
    (hε : 0 < ε) (haexp : 0 ≤ 3 / 2 - ε)
    (hAT : T + 2 ≤ 3 * A)
    (hd : 1024 * (T + 1) + 1 ≤ d) :
    ∀ᶠ B : ℕ in atTop, ∀ (P a b : ℕ) (N : ℝ),
      0 < P → P ≤ a → a ≤ b → b ≤ 2 * P → 0 < a → b ≤ B →
      P ≤ B → B ≤ 2 * P → N ≠ 0 →
      64 ≤ reciprocalPhaseScale N 0 2 P →
      (Real.log B) ^ d ≤ reciprocalPhaseScale N 0 2 P →
      reciprocalPhaseScale N 0 2 P ≤
        C₀ * Real.exp ((Real.log B) ^ (3 / 2 - ε)) →
      ‖weightedConvolutionProductSum (Finset.Ico a b) B
          (fun n => standardAdditiveCharacter (reciprocalPhase N 0 2 n))
          (vaughanTypeICoefficient (vaughanSourceTailCutoff B)) log‖ ≤
        (Nat.log 2 B + 1 : ℕ) ^ 102 *
          ((P : ℝ) *
            (4 * typeIQuadraticBranchDecayConstant *
              (Real.log B) ^ (-(T - 1))) *
            ((harmonic (vaughanSourceTailCutoff B) : ℚ) : ℝ)) := by
  let K : ℕ := ⌈2 * (240 * ((((5 + 2) ^ 5 : ℕ) : ℝ)))⌉₊
  have hadm := eventually_forall_activeLog_typeIQuadraticHybridAdmissible
    hA hC₀ hε haexp
  have hlarge := eventually_forall_activeLog_ceilDiv_ge K
  have hquarter := eventually_quarter_rpow_le_ceilDiv_of_activeLog
  have hmajor := eventually_typeIQuadraticRescaledBranchMajorantAt_le_invWeighted
    hC₀ hC₁ hε haexp hAT hd
  have hlog : ∀ᶠ B : ℕ in atTop, 1 ≤ Real.log (B : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 1)
  have hApos : 0 < A := by linarith
  have hten : ∀ᶠ B : ℕ in atTop, 10 ≤ (Real.log (B : ℝ)) ^ A :=
    ((tendsto_rpow_atTop hApos).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        (eventually_ge_atTop 10)
  filter_upwards [hadm, hlarge, hquarter, hmajor, hlog, hten,
    eventually_gt_atTop (0 : ℕ)] with
      B hadmB hlargeB hquarterB hmajorB hlogB htenB hB
  intro P a b N hP hPa hab hbP ha hbB hPB hBP hN hsource64 hsource hupper
  have hQ : 0 ≤ 4 * typeIQuadraticBranchDecayConstant *
        (Real.log B) ^ (-(T - 1)) := by
    have hlogNonneg : 0 ≤ Real.log (B : ℝ) := by linarith
    exact mul_nonneg (mul_nonneg (by norm_num)
      typeIQuadraticBranchDecayConstant_pos.le)
        (Real.rpow_nonneg hlogNonneg _)
  apply norm_weightedConvolutionProductVaughanTypeILogSum_le_invWeighted
    (Finset.Ico a b) B (vaughanSourceTailCutoff B) P N 0 2 hQ
  intro sk hsk m hmActive
  have hmpos : 0 < m := pos_of_mem_vaughanTypeIActiveProductBlockSupport hmActive
  have hD : K ≤ P ⌈/⌉ m := hlargeB P sk m hBP hmActive
  have htwoD : 2 ≤ P ⌈/⌉ m := by
    have hKtwo : 2 ≤ K := by norm_num [K]
    exact hKtwo.trans hD
  have hmP : m ≤ P := le_of_two_le_ceilDiv hmpos htwoD
  have hDreal : 2 * (240 * ((((5 + 2) ^ 5 : ℕ) : ℝ))) ≤
      ((P ⌈/⌉ m : ℕ) : ℝ) := by
    have hceil : 2 * (240 * ((((5 + 2) ^ 5 : ℕ) : ℝ))) ≤ (K : ℝ) := by
      norm_num [K]
    exact hceil.trans (by exact_mod_cast hD)
  have hadmFiber := hadmB P N 0 sk m hP hBP hsource64 hupper hmActive
  have hbudget :
      reciprocalPhaseScale (N / m) 0 2 ((P ⌈/⌉ m : ℕ) : ℝ) ≤
        ((P ⌈/⌉ m : ℕ) : ℝ) ^ 4 →
      240 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
          (reciprocalPhaseScale (N / m) 0 2 ((P ⌈/⌉ m : ℕ) : ℝ) /
            ((P ⌈/⌉ m : ℕ) : ℝ) ^ 5) +
        1 / 16 + 4 / reciprocalPhaseScale (N / m) 0 2
            ((P ⌈/⌉ m : ℕ) : ℝ) ≤ 1 := by
    intro hlow
    simpa only [zero_div] using
      (typeIQuadraticWeylBudget_of_sourceScale
        N 0 hP hmpos hmP hDreal hsource64 (by simpa only [zero_div] using hlow))
  have hlocalUpper := reciprocalPhaseScale_typeI_rescale_ceilDiv_le
    N 0 2 hP hmpos
  have hmajorFiber := hmajorB P m N 0 hP hmpos hmP hPB htwoD
    (hquarterB P sk m hBP hmActive) hsource (hlocalUpper.trans hupper)
  have hinner :=
    norm_typeIProductRestrictedLogInnerSum_Ico_le_quadraticBranchAt_zero_quadratic
      C₁ hVinogradov B A N hPa hab hbP ha hbB hmpos hN hC₁.le
        hlogB hA htenB hadmFiber hbudget
  have hceilPos : 0 < b ⌈/⌉ m := typeI_ceilDiv_pos (ha.trans_le hab) hmpos
  have hlogCeil : 0 ≤ Real.log ((b ⌈/⌉ m : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hceilPos)
  calc
    ‖typeIProductRestrictedWeightedInnerSum (Finset.Ico a b)
        (Finset.Ioc 0 B) (fun n => (Real.log n : ℂ)) N 0 2 m‖ ≤
      2 * Real.log ((b ⌈/⌉ m : ℕ) : ℝ) *
        typeIQuadraticRescaledBranchMajorantAt C₁ B A N 0 P m := hinner
    _ ≤ 2 * Real.log ((b ⌈/⌉ m : ℕ) : ℝ) *
        ((P : ℝ) / m *
          (2 * typeIQuadraticBranchDecayConstant *
            (Real.log B) ^ (-T))) := by
      exact mul_le_mul_of_nonneg_left hmajorFiber
        (mul_nonneg (by norm_num) hlogCeil)
    _ ≤ (P : ℝ) / m *
        (4 * typeIQuadraticBranchDecayConstant *
          (Real.log B) ^ (-(T - 1))) :=
      two_mul_log_ceilDiv_mul_branchDecay_le_invWeighted
        hmpos (ha.trans_le hab) hbB (by linarith)

/-- Final arbitrary-logarithmic-saving estimate for the pure-linear second
Vaughan Type I family. -/
theorem eventually_norm_weightedConvolutionProductVaughanTypeIPrimeSum_le_logSaving_zero_quadratic
    {C₀ C₁ ε A d S : ℝ}
    (hA : 1 / 4 ≤ A) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (hVinogradov : VinogradovExponentialSumEstimateAt C₁)
    (hε : 0 < ε) (haexp : 0 ≤ 3 / 2 - ε)
    (hAS : S + 106 ≤ 3 * A)
    (hd : 1024 * (S + 105) + 1 ≤ d) :
    ∀ᶠ B : ℕ in atTop, ∀ (P a b : ℕ) (N : ℝ),
      0 < P → P ≤ a → b ≤ 2 * P → 0 < a → b ≤ B →
      P ≤ B → B ≤ 2 * P → N ≠ 0 →
      64 ≤ reciprocalPhaseScale N 0 2 P →
      (Real.log B) ^ d ≤ reciprocalPhaseScale N 0 2 P →
      reciprocalPhaseScale N 0 2 P ≤
        C₀ * Real.exp ((Real.log B) ^ (3 / 2 - ε)) →
      ‖weightedConvolutionProductSum (Finset.Ico a b) B
          (fun n => standardAdditiveCharacter (reciprocalPhase N 0 2 n))
          (vaughanTypeIPrimeCoefficient
            (vaughanSourceTailCutoff B) (vaughanSourceTailCutoff B))
          (ζ : ArithmeticFunction ℝ)‖ ≤
        typeIQuadraticFamilyDecayConstant * (P : ℝ) *
          (Real.log B) ^ (-S) := by
  have hAT : (S + 104) + 2 ≤ 3 * A := by linarith
  have hd' : 1024 * ((S + 104) + 1) + 1 ≤ d := by linarith
  have hsource :=
    eventually_norm_weightedConvolutionProductVaughanTypeIPrimeSum_le_source_zero_quadratic
      hA hC₀ hC₁ hVinogradov hε haexp hAT hd'
  have hlog : ∀ᶠ B : ℕ in atTop, 2 ≤ Real.log (B : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 2)
  filter_upwards [hsource, hlog] with B hsourceB hlogB
  intro P a b N hP hPa hbP ha hbB hPB hBP hN hsource64 hlower hupper
  have hraw := hsourceB P a b N hP hPa hbP ha hbB hPB hBP hN
    hsource64 hlower hupper
  calc
    ‖weightedConvolutionProductSum (Finset.Ico a b) B
        (fun n => standardAdditiveCharacter (reciprocalPhase N 0 2 n))
        (vaughanTypeIPrimeCoefficient
          (vaughanSourceTailCutoff B) (vaughanSourceTailCutoff B))
        (ζ : ArithmeticFunction ℝ)‖ ≤
      (Nat.log 2 B + 1 : ℕ) ^ 102 *
        (Real.log (2 * B) *
          ((P : ℝ) *
            (2 * typeIQuadraticBranchDecayConstant *
              (Real.log B) ^ (-(S + 104))) *
            ((harmonic
              (vaughanSourceTailCutoff B * vaughanSourceTailCutoff B) : ℚ) : ℝ))) := hraw
    _ ≤ typeIQuadraticFamilyDecayConstant * (P : ℝ) *
        (Real.log B) ^ (-S) := by
      simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_one] using
        (typeIPrimeFamilyEnvelope_le_logSaving
          (hP.trans_le hPB) hlogB (T := S + 104) (S := S) rfl)

/-- Final arbitrary-logarithmic-saving estimate for the pure-linear first
Vaughan Type I family, including finite Abel summation. -/
theorem eventually_norm_weightedConvolutionProductVaughanTypeILogSum_le_logSaving_zero_quadratic
    {C₀ C₁ ε A d S : ℝ}
    (hA : 1 / 4 ≤ A) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (hVinogradov : VinogradovExponentialSumEstimateAt C₁)
    (hε : 0 < ε) (haexp : 0 ≤ 3 / 2 - ε)
    (hAS : S + 106 ≤ 3 * A)
    (hd : 1024 * (S + 105) + 1 ≤ d) :
    ∀ᶠ B : ℕ in atTop, ∀ (P a b : ℕ) (N : ℝ),
      0 < P → P ≤ a → a ≤ b → b ≤ 2 * P → 0 < a → b ≤ B →
      P ≤ B → B ≤ 2 * P → N ≠ 0 →
      64 ≤ reciprocalPhaseScale N 0 2 P →
      (Real.log B) ^ d ≤ reciprocalPhaseScale N 0 2 P →
      reciprocalPhaseScale N 0 2 P ≤
        C₀ * Real.exp ((Real.log B) ^ (3 / 2 - ε)) →
      ‖weightedConvolutionProductSum (Finset.Ico a b) B
          (fun n => standardAdditiveCharacter (reciprocalPhase N 0 2 n))
          (vaughanTypeICoefficient (vaughanSourceTailCutoff B)) log‖ ≤
        typeIQuadraticFamilyDecayConstant * (P : ℝ) *
          (Real.log B) ^ (-S) := by
  have hAT : (S + 104) + 2 ≤ 3 * A := by linarith
  have hd' : 1024 * ((S + 104) + 1) + 1 ≤ d := by linarith
  have hsource :=
    eventually_norm_weightedConvolutionProductVaughanTypeILogSum_le_source_zero_quadratic
      hA hC₀ hC₁ hVinogradov hε haexp hAT hd'
  have hlog : ∀ᶠ B : ℕ in atTop, 2 ≤ Real.log (B : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 2)
  filter_upwards [hsource, hlog] with B hsourceB hlogB
  intro P a b N hP hPa hab hbP ha hbB hPB hBP hN hsource64 hlower hupper
  have hraw := hsourceB P a b N hP hPa hab hbP ha hbB hPB hBP hN
    hsource64 hlower hupper
  calc
    ‖weightedConvolutionProductSum (Finset.Ico a b) B
        (fun n => standardAdditiveCharacter (reciprocalPhase N 0 2 n))
        (vaughanTypeICoefficient (vaughanSourceTailCutoff B)) log‖ ≤
      (Nat.log 2 B + 1 : ℕ) ^ 102 *
        ((P : ℝ) *
          (4 * typeIQuadraticBranchDecayConstant *
            (Real.log B) ^ (-((S + 104) - 1))) *
          ((harmonic (vaughanSourceTailCutoff B) : ℚ) : ℝ)) := hraw
    _ ≤ typeIQuadraticFamilyDecayConstant * (P : ℝ) *
        (Real.log B) ^ (-S) := by
      simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_one] using
        (typeILogFamilyEnvelope_le_logSaving
          (hP.trans_le hPB) hlogB (T := S + 104) (S := S) rfl)

end

end Tao2026
