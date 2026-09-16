import Tao2026.UnequalTypeIIVinogradov
import Tao2026.WeylDifferencing
import Tao2026.TypeIIConvolutionBridge

/-!
# Unequal-parameter Type II Weyl bridge

This module develops the low-scale counterpart of the unequal Type II
Vinogradov bridge.  On a dyadic inner band, both transformed reciprocal
coefficients retain the natural-distance fraction of their corresponding
source-scale terms.
-/

open Complex Finset Filter Topology
open scoped BigOperators

namespace Tao2026

noncomputable section

/-- On a positive band bounded above by `B`, whose two endpoints have sum at
least `B`, the transformed quadratic coefficient retains the source quadratic
scale multiplied by `dist/B`. -/
theorem typeIICorrelationScale_lower_of_quadratic
    (M K B : ℝ) {n n' : ℕ}
    (hK : 0 < K) (hB : 0 < B) (hn : 0 < n) (hn' : 0 < n')
    (hnB : (n : ℝ) ≤ B) (hn'B : (n' : ℝ) ≤ B)
    (hsum : B ≤ (n : ℝ) + n') :
    (Nat.dist n' n : ℝ) / B * (|M| / (K * B) ^ 2) ≤
      |typeIICorrelationHigherParameter M 2 n n'| / K ^ 2 := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn'R : 0 < (n' : ℝ) := by exact_mod_cast hn'
  have hnSq : (n : ℝ) ^ 2 ≤ B ^ 2 := by nlinarith
  have hn'Sq : (n' : ℝ) ^ 2 ≤ B ^ 2 := by nlinarith
  have hden : (n : ℝ) ^ 2 * (n' : ℝ) ^ 2 ≤ B ^ 4 := by
    calc
      (n : ℝ) ^ 2 * (n' : ℝ) ^ 2 ≤ B ^ 2 * B ^ 2 := by
        exact mul_le_mul hnSq hn'Sq (sq_nonneg _) (sq_nonneg _)
      _ = B ^ 4 := by ring
  have hdiff : |(n' : ℝ) ^ 2 - (n : ℝ) ^ 2| =
      (Nat.dist n' n : ℝ) * ((n' : ℝ) + n) := by
    calc
      |(n' : ℝ) ^ 2 - (n : ℝ) ^ 2| =
          |((n' : ℝ) - n) * ((n' : ℝ) + n)| := by
        exact congrArg abs (by ring)
      _ = |(n' : ℝ) - n| * |(n' : ℝ) + n| := abs_mul _ _
      _ = (Nat.dist n' n : ℝ) * ((n' : ℝ) + n) := by
        rw [abs_natCast_sub_eq_natDist_cast, abs_of_nonneg]
        positivity
  have hpower : B * (Nat.dist n' n : ℝ) ≤
      |(n' : ℝ) ^ 2 - (n : ℝ) ^ 2| := by
    rw [hdiff]
    nlinarith [Nat.cast_nonneg (α := ℝ) (Nat.dist n' n)]
  have hnum : |M| * (Nat.dist n' n : ℝ) * B ≤
      |M| * |(n' : ℝ) ^ 2 - (n : ℝ) ^ 2| := by
    nlinarith [abs_nonneg M]
  have hdenPos : 0 < (n : ℝ) ^ 2 * (n' : ℝ) ^ 2 := by positivity
  have hBfourPos : 0 < B ^ 4 := pow_pos hB 4
  have hcoeff : |M| * (Nat.dist n' n : ℝ) / B ^ 3 ≤
      |typeIICorrelationHigherParameter M 2 n n'| := by
    calc
      |M| * (Nat.dist n' n : ℝ) / B ^ 3 =
          (|M| * (Nat.dist n' n : ℝ) * B) / B ^ 4 := by field_simp
      _ ≤ (|M| * |(n' : ℝ) ^ 2 - (n : ℝ) ^ 2|) / B ^ 4 :=
        div_le_div_of_nonneg_right hnum hBfourPos.le
      _ ≤ (|M| * |(n' : ℝ) ^ 2 - (n : ℝ) ^ 2|) /
          ((n : ℝ) ^ 2 * (n' : ℝ) ^ 2) :=
        div_le_div_of_nonneg_left (by positivity) hdenPos hden
      _ = |typeIICorrelationHigherParameter M 2 n n'| := by
        rw [typeIICorrelationHigherParameter,
          abs_typeIICorrelationHigherParameter]
  have hdivide := div_le_div_of_nonneg_right hcoeff (sq_nonneg K)
  calc
    (Nat.dist n' n : ℝ) / B * (|M| / (K * B) ^ 2) =
        (|M| * (Nat.dist n' n : ℝ) / B ^ 3) / K ^ 2 := by
      field_simp
    _ ≤ |typeIICorrelationHigherParameter M 2 n n'| / K ^ 2 := hdivide

/-- On a quadratic dyadic band, natural distance controls the complete source
scale even when the two reciprocal coefficients are independent.  The factor
two records the elementary split according to which source term is larger. -/
theorem typeIICorrelationScale_lower_of_unequal_quadratic
    (N M K B : ℝ) {n n' : ℕ}
    (hK : 0 < K) (hB : 0 < B)
    (hn : 0 < n) (hn' : 0 < n')
    (hnB : (n : ℝ) ≤ B) (hn'B : (n' : ℝ) ≤ B)
    (hsum : B ≤ (n : ℝ) + n') :
    (Nat.dist n' n : ℝ) / B *
        (reciprocalPhaseScale N M 2 (K * B) / 2) ≤
      reciprocalPhaseScale
        (typeIICorrelationLinearParameter N n n')
        (typeIICorrelationHigherParameter M 2 n n') 2 K := by
  let d : ℝ := (Nat.dist n' n : ℝ) / B
  let linear : ℝ := |N| / (K * B)
  let higher : ℝ := |M| / (K * B) ^ 2
  let transformed := reciprocalPhaseScale
    (typeIICorrelationLinearParameter N n n')
    (typeIICorrelationHigherParameter M 2 n n') 2 K
  have hd : 0 ≤ d := by unfold d; positivity
  have hlinear : d * linear ≤ transformed := by
    simpa only [d, linear, transformed] using
      (typeIICorrelationScale_lower_of_linear
        N M K B 2 n n' hK hB hn hn' hnB hn'B)
  have hhigherComponent :
      d * higher ≤ |typeIICorrelationHigherParameter M 2 n n'| / K ^ 2 := by
    simpa only [d, higher] using
      (typeIICorrelationScale_lower_of_quadratic
        M K B hK hB hn hn' hnB hn'B hsum)
  have hhigher : d * higher ≤ transformed :=
    hhigherComponent.trans <| by
      unfold transformed reciprocalPhaseScale
      exact le_add_of_nonneg_left (by positivity)
  have hsource : reciprocalPhaseScale N M 2 (K * B) = linear + higher := by
    rfl
  by_cases hterms : higher ≤ linear
  · have hhalf : reciprocalPhaseScale N M 2 (K * B) / 2 ≤ linear := by
      rw [hsource]
      linarith
    exact (mul_le_mul_of_nonneg_left hhalf hd).trans hlinear
  · have hhalf : reciprocalPhaseScale N M 2 (K * B) / 2 ≤ higher := by
      rw [hsource]
      have : linear ≤ higher := le_of_not_ge hterms
      linarith
    exact (mul_le_mul_of_nonneg_left hhalf hd).trans hhigher

/-- Reciprocal transformed-scale control for unequal quadratic coefficients
on one dyadic band. -/
theorem one_div_typeIICorrelationScale_le_two_mul_B_div_sourceScale_unequal
    (N M K B : ℝ) {n n' : ℕ}
    (hK : 0 < K) (hB : 0 < B)
    (hn : 0 < n) (hn' : 0 < n') (hne : n ≠ n')
    (hnB : (n : ℝ) ≤ B) (hn'B : (n' : ℝ) ≤ B)
    (hsum : B ≤ (n : ℝ) + n')
    (hF : 0 < reciprocalPhaseScale N M 2 (K * B)) :
    1 / reciprocalPhaseScale
          (typeIICorrelationLinearParameter N n n')
          (typeIICorrelationHigherParameter M 2 n n') 2 K ≤
      2 * B / reciprocalPhaseScale N M 2 (K * B) := by
  let F := reciprocalPhaseScale N M 2 (K * B)
  let F' := reciprocalPhaseScale
    (typeIICorrelationLinearParameter N n n')
    (typeIICorrelationHigherParameter M 2 n n') 2 K
  have hdistNat : 1 ≤ Nat.dist n' n :=
    Nat.one_le_iff_ne_zero.mpr (fun h => hne (Nat.eq_of_dist_eq_zero h).symm)
  have hdist : (1 : ℝ) ≤ (Nat.dist n' n : ℝ) := by exact_mod_cast hdistNat
  have hdiv : 1 / B ≤ (Nat.dist n' n : ℝ) / B :=
    div_le_div_of_nonneg_right hdist hB.le
  have hhalf0 : 0 ≤ F / 2 := by unfold F; positivity
  have hbaseRaw := mul_le_mul_of_nonneg_right hdiv hhalf0
  have hbase : F / (2 * B) ≤
      (Nat.dist n' n : ℝ) / B * (F / 2) := by
    calc
      F / (2 * B) = (1 / B) * (F / 2) := by field_simp
      _ ≤ (Nat.dist n' n : ℝ) / B * (F / 2) := hbaseRaw
  have hlower : (Nat.dist n' n : ℝ) / B * (F / 2) ≤ F' := by
    simpa only [F, F'] using
      (typeIICorrelationScale_lower_of_unequal_quadratic
        N M K B hK hB hn hn' hnB hn'B hsum)
  have hbasePos : 0 < F / (2 * B) := by unfold F; positivity
  have hinv : 1 / F' ≤ 1 / (F / (2 * B)) :=
    one_div_le_one_div_of_le hbasePos (hbase.trans hlower)
  calc
    1 / reciprocalPhaseScale
          (typeIICorrelationLinearParameter N n n')
          (typeIICorrelationHigherParameter M 2 n n') 2 K = 1 / F' := by rfl
    _ ≤ 1 / (F / (2 * B)) := hinv
    _ = 2 * B / reciprocalPhaseScale N M 2 (K * B) := by
      unfold F
      field_simp

/-- The far-pair inverse-scale bound also survives with unequal quadratic
coefficients once both points lie in one dyadic band. -/
theorem one_div_typeIICorrelationScale_le_two_thirds_of_three_le_scaledDistance_unequal
    (N M K B : ℝ) {n n' : ℕ}
    (hK : 0 < K) (hB : 0 < B)
    (hn : 0 < n) (hn' : 0 < n')
    (hnB : (n : ℝ) ≤ B) (hn'B : (n' : ℝ) ≤ B)
    (hsum : B ≤ (n : ℝ) + n')
    (hfar : 3 ≤ (Nat.dist n' n : ℝ) *
      reciprocalPhaseScale N M 2 (K * B) / B) :
    1 / reciprocalPhaseScale
          (typeIICorrelationLinearParameter N n n')
          (typeIICorrelationHigherParameter M 2 n n') 2 K ≤ 2 / 3 := by
  let F := reciprocalPhaseScale N M 2 (K * B)
  let F' := reciprocalPhaseScale
    (typeIICorrelationLinearParameter N n n')
    (typeIICorrelationHigherParameter M 2 n n') 2 K
  have hlower : (Nat.dist n' n : ℝ) / B * (F / 2) ≤ F' := by
    simpa only [F, F'] using
      (typeIICorrelationScale_lower_of_unequal_quadratic
        N M K B hK hB hn hn' hnB hn'B hsum)
  have hthreeHalves : (3 / 2 : ℝ) ≤
      (Nat.dist n' n : ℝ) / B * (F / 2) := by
    calc
      (3 / 2 : ℝ) ≤ ((Nat.dist n' n : ℝ) * F / B) / 2 := by
        apply div_le_div_of_nonneg_right
        · simpa only [F] using hfar
        · norm_num
      _ = (Nat.dist n' n : ℝ) / B * (F / 2) := by field_simp
  have hinv : 1 / F' ≤ 1 / (3 / 2 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) (hthreeHalves.trans hlower)
  calc
    1 / reciprocalPhaseScale
          (typeIICorrelationLinearParameter N n n')
          (typeIICorrelationHigherParameter M 2 n n') 2 K = 1 / F' := by rfl
    _ ≤ 1 / (3 / 2 : ℝ) := hinv
    _ = 2 / 3 := by norm_num

/-- Distance-kernel domination for the unequal quadratic correlation.  The
large-distance branch uses the complete unequal scale lower bound above; the
small-distance branch uses the universal fact that the Weyl width is at most
one. -/
theorem reciprocalPhaseFourStepTwoTermWidth_typeIICorrelation_unequal_quadratic_le
    (N M K B E : ℝ) {n n' : ℕ}
    (hM : M ≠ 0) (hK : 0 < K) (hB : 0 < B)
    (hn : 0 < n) (hn' : 0 < n') (hne : n ≠ n')
    (hnB : (n : ℝ) ≤ B) (hn'B : (n' : ℝ) ≤ B)
    (hsum : B ≤ (n : ℝ) + n')
    (hwidthOne :
      reciprocalPhaseFourStepTwoTermWidth
        (typeIICorrelationLinearParameter N n n')
        (typeIICorrelationHigherParameter M 2 n n') 2 K ≤ 1)
    (hupper :
      reciprocalPhaseScale
          (typeIICorrelationLinearParameter N n n')
          (typeIICorrelationHigherParameter M 2 n n') 2 K / K ^ 5 ≤ E) :
    reciprocalPhaseFourStepTwoTermWidth
        (typeIICorrelationLinearParameter N n n')
        (typeIICorrelationHigherParameter M 2 n n') 2 K ≤
      E ^ (1 / 1024 : ℝ) +
        4 * typeIIDecayKernel B (reciprocalPhaseScale N M 2 (K * B))
          (1 / 1024 : ℝ) (Nat.dist n' n) := by
  let N' := typeIICorrelationLinearParameter N n n'
  let M' := typeIICorrelationHigherParameter M 2 n n'
  let F := reciprocalPhaseScale N M 2 (K * B)
  let d := Nat.dist n' n
  let x := (d : ℝ) * F / B
  let δ : ℝ := 1 / 1024
  have hδ0 : 0 ≤ δ := by unfold δ; norm_num
  have hδ1 : δ ≤ 1 := by unfold δ; norm_num
  have hM' : M' ≠ 0 := by
    unfold M' typeIICorrelationHigherParameter
    exact typeIICorrelationHigherParameter_ne_zero hM (by norm_num)
      (Nat.ne_of_gt hn) (Nat.ne_of_gt hn') hne
  have hscale : 0 < reciprocalPhaseScale N' M' 2 K := by
    unfold reciprocalPhaseScale
    have hMabs : 0 < |M'| := abs_pos.mpr hM'
    have hKpow : 0 < K ^ 2 := pow_pos hK 2
    have hterm : 0 < |M'| / K ^ 2 := div_pos hMabs hKpow
    positivity
  have hF : 0 < F := by
    unfold F reciprocalPhaseScale
    have hMabs : 0 < |M| := abs_pos.mpr hM
    have hKBpos : 0 < K * B := mul_pos hK hB
    have hterm : 0 < |M| / (K * B) ^ 2 :=
      div_pos hMabs (pow_pos hKBpos 2)
    positivity
  have hx0 : 0 ≤ x := by unfold x; positivity
  have hlower : x / 2 ≤ reciprocalPhaseScale N' M' 2 K := by
    have hraw := typeIICorrelationScale_lower_of_unequal_quadratic
      N M K B hK hB hn hn' hnB hn'B hsum
    calc
      x / 2 = (d : ℝ) / B * (F / 2) := by
        unfold x
        ring
      _ ≤ reciprocalPhaseScale N' M' 2 K := by
        simpa only [N', M', F, d] using hraw
  by_cases hx : 1 ≤ x
  · have hbaseLower : (1 + (d : ℝ) * F / B) / 4 ≤
        reciprocalPhaseScale N' M' 2 K := by
      have hxeq : (d : ℝ) * F / B = x := by rfl
      rw [hxeq]
      calc
        (1 + x) / 4 ≤ x / 2 := by linarith
        _ ≤ reciprocalPhaseScale N' M' 2 K := hlower
    have hgeneric :=
      reciprocalPhaseFourStepTwoTermWidth_le_typeIIDecayKernel_add_error
        N' M' hK hscale hB hF.le (by norm_num : (0 : ℝ) < 4)
          (by simpa only [N', M'] using hupper) hbaseLower
    have hfour : (4 : ℝ) ^ δ ≤ 4 :=
      Real.rpow_le_self_of_one_le (by norm_num) hδ1
    have hkernelNonneg : 0 ≤ typeIIDecayKernel B F δ d :=
      typeIIDecayKernel_nonneg δ d hB hF.le
    calc
      reciprocalPhaseFourStepTwoTermWidth N' M' 2 K ≤
          E ^ δ + 4 ^ δ * typeIIDecayKernel B F δ d := by
        simpa only [δ] using hgeneric
      _ ≤ E ^ δ + 4 * typeIIDecayKernel B F δ d := by gcongr
      _ = E ^ (1 / 1024 : ℝ) +
          4 * typeIIDecayKernel B F (1 / 1024 : ℝ) d := by rfl
  · have hxlt : x < 1 := lt_of_not_ge hx
    have hbasePos : 0 < 1 + (d : ℝ) * F / B := by positivity
    have hbaseTwo : 1 + (d : ℝ) * F / B ≤ 2 := by
      have hxeq : (d : ℝ) * F / B = x := by rfl
      rw [hxeq]
      linarith
    have htwoKernel : (2 : ℝ) ^ (-δ) ≤
        typeIIDecayKernel B F δ d := by
      unfold typeIIDecayKernel
      exact Real.rpow_le_rpow_of_nonpos hbasePos hbaseTwo
        (neg_nonpos.mpr hδ0)
    have hhalfPow : (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (-δ) := by
      calc
        (1 / 2 : ℝ) = (2 : ℝ) ^ (-1 : ℝ) := by norm_num
        _ ≤ (2 : ℝ) ^ (-δ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have hkernelHalf : (1 / 2 : ℝ) ≤
        typeIIDecayKernel B F δ d := hhalfPow.trans htwoKernel
    have hwidthOne' : reciprocalPhaseFourStepTwoTermWidth N' M' 2 K ≤ 1 := by
      simpa only [N', M'] using hwidthOne
    have hEnonneg : 0 ≤ E := by
      have hu : 0 ≤ reciprocalPhaseScale N' M' 2 K / K ^ 5 := by positivity
      exact hu.trans (by simpa only [N', M'] using hupper)
    calc
      reciprocalPhaseFourStepTwoTermWidth N' M' 2 K ≤ 1 := hwidthOne'
      _ ≤ E ^ δ + 4 * typeIIDecayKernel B F δ d := by
        have hEpow : 0 ≤ E ^ δ := Real.rpow_nonneg hEnonneg δ
        nlinarith
      _ = E ^ (1 / 1024 : ℝ) +
          4 * typeIIDecayKernel B F (1 / 1024 : ℝ) d := by rfl

/-- A far unequal quadratic pair has complete four-step effective error at
most one under the same quarter-budget used by the diagonal proof. -/
theorem reciprocalPhaseFourStepEffectiveErrorScale_typeIICorrelation_le_one_of_far_unequal
    (N M K B E : ℝ) {L n n' : ℕ}
    (hK : 0 < K) (hB : 0 < B)
    (hn : 0 < n) (hn' : 0 < n')
    (hnB : (n : ℝ) ≤ B) (hn'B : (n' : ℝ) ≤ B)
    (hsum : B ≤ (n : ℝ) + n')
    (hupper : reciprocalPhaseScale
        (typeIICorrelationLinearParameter N n n')
        (typeIICorrelationHigherParameter M 2 n n') 2 K / K ^ 5 ≤ E)
    (hscaleBudget : 240 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) * E ≤ 1 / 4)
    (hLength : 1 ≤ L)
    (hfar : 3 ≤ (Nat.dist n' n : ℝ) *
      reciprocalPhaseScale N M 2 (K * B) / B) :
    reciprocalPhaseFourStepEffectiveErrorScale
        (typeIICorrelationLinearParameter N n n')
        (typeIICorrelationHigherParameter M 2 n n') 2 K L ≤ 1 := by
  have hinv :=
    one_div_typeIICorrelationScale_le_two_thirds_of_three_le_scaledDistance_unequal
      N M K B hK hB hn hn' hnB hn'B hsum hfar
  have hraw := reciprocalPhaseFourStepEffectiveErrorScale_le_of_scale_bounds
    (typeIICorrelationLinearParameter N n n')
    (typeIICorrelationHigherParameter M 2 n n') K E (2 / 3) 2 L
    hupper hinv hLength
  calc
    reciprocalPhaseFourStepEffectiveErrorScale
        (typeIICorrelationLinearParameter N n n')
        (typeIICorrelationHigherParameter M 2 n n') 2 K L ≤
      240 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) * E + 1 / 16 + 2 / 3 := hraw
    _ ≤ 1 := by linarith

/-- Source-shaped pointwise four-step Weyl estimate for an unequal quadratic
Type II correlation. -/
theorem norm_typeIIProductRestrictedCorrelationSum_le_fourStepWeyl_decayKernel_unequal_quadratic
    (a b K₀ K₁ q k : ℕ) (N M : ℝ) (orders : Finset ℕ)
    {n n' : ℕ} {K B Y E : ℝ}
    (hq : 0 < q) (hn : 0 < n) (hn' : 0 < n') (hne : n ≠ n')
    (hM : M ≠ 0) (hK : 0 < K) (hB : 0 < B)
    (hnB : (n : ℝ) ≤ B) (hn'B : (n' : ℝ) ≤ B)
    (hsum : B ≤ (n : ℝ) + n')
    (hrFive : 5 ∈ orders) (hrSix : 6 ∈ orders)
    (hupper :
      reciprocalPhaseScale
          (typeIICorrelationLinearParameter N n n')
          (typeIICorrelationHigherParameter M 2 n n') 2 K / K ^ 5 ≤ E)
    (hanalytic :
      let N' := typeIICorrelationLinearParameter N n n'
      let M' := typeIICorrelationHigherParameter M 2 n n'
      let lo := typeIIProductRestrictedBlockLower a K₀ q k n n'
      let hi := typeIIProductRestrictedBlockUpper b K₀ K₁ q k n n'
      1 ≤ hi - lo →
        reciprocalPhaseScale N' M' 2 K ≤ K ^ 4 ∧
        reciprocalPhaseFourStepEffectiveErrorScale N' M' 2 K (hi - lo) ≤ 1 ∧
        (lo : ℝ) ∈ Set.Icc K Y ∧
        (lo : ℝ) + (hi - lo : ℕ) +
            (4 * reciprocalPhaseFourStepOptimizedRange N' M' 2 K (hi - lo) : ℕ) ≤ Y ∧
        (lo : ℝ) + (hi - lo : ℕ) +
            (4 * reciprocalPhaseFourStepOptimizedRange N' M' 2 K (hi - lo) : ℕ) ≤
          2 * K ∧
        ∀ t ∈ Set.Icc K Y, t ^ (2 - 1) ≤ 2 * K ^ (2 - 1)) :
    let lo := typeIIProductRestrictedBlockLower a K₀ q k n n'
    let hi := typeIIProductRestrictedBlockUpper b K₀ K₁ q k n n'
    let F := reciprocalPhaseScale N M 2 (K * B)
    ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
        (shortIntervalBlock K₀ K₁ q k) N M 2 n n'‖ ≤
      ((370 * orders.card + 173 : ℕ) : ℝ) *
        (480 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
          (((((5 + 2) ^ 5 : ℕ) : ℝ)) + 1) *
          (1 + Real.log ((hi - lo : ℕ) : ℝ)) * K *
            (E ^ (1 / 1024 : ℝ) +
              4 * typeIIDecayKernel B F (1 / 1024 : ℝ) (Nat.dist n' n))) := by
  dsimp only
  let N' := typeIICorrelationLinearParameter N n n'
  let M' := typeIICorrelationHigherParameter M 2 n n'
  let lo := typeIIProductRestrictedBlockLower a K₀ q k n n'
  let hi := typeIIProductRestrictedBlockUpper b K₀ K₁ q k n n'
  let F := reciprocalPhaseScale N M 2 (K * B)
  let p := reciprocalPhaseFourStepTwoTermWidth N' M' 2 K
  let δ : ℝ := 1 / 1024
  let J : ℝ := ((((5 + 2) ^ 5 : ℕ) : ℝ))
  let C : ℝ := ((370 * orders.card + 173 : ℕ) : ℝ)
  have hM' : M' ≠ 0 := by
    unfold M' typeIICorrelationHigherParameter
    exact typeIICorrelationHigherParameter_ne_zero hM (by norm_num)
      (Nat.ne_of_gt hn) (Nat.ne_of_gt hn') hne
  have hscale : 0 < reciprocalPhaseScale N' M' 2 K := by
    unfold reciprocalPhaseScale
    have hMabs : 0 < |M'| := abs_pos.mpr hM'
    have hKpow : 0 < K ^ 2 := pow_pos hK 2
    have hterm : 0 < |M'| / K ^ 2 := div_pos hMabs hKpow
    positivity
  have hEnonneg : 0 ≤ E := by
    have hu : 0 ≤ reciprocalPhaseScale N' M' 2 K / K ^ 5 := by positivity
    exact hu.trans (by simpa only [N', M'] using hupper)
  by_cases hLength : 1 ≤ hi - lo
  · rcases hanalytic hLength with
      ⟨hFlow, herrorSmall, haIcc, hevalY, hevalTop, hpow⟩
    have hpoint :=
      norm_typeIIProductRestrictedCorrelationSum_le_fourStepWeyl_twoTerm
        a b K₀ K₁ q k N M orders hq hn hn' hne hK hM (by norm_num)
          hrFive hrSix hanalytic
    have hwidthOne : p ≤ 1 := by
      exact reciprocalPhaseFourStepTwoTermWidth_le_one N' M' hK hscale
        (by simpa only [N', M', p] using herrorSmall)
    have hwidth : p ≤ E ^ δ +
        4 * typeIIDecayKernel B F δ (Nat.dist n' n) := by
      simpa only [N', M', F, p, δ] using
        (reciprocalPhaseFourStepTwoTermWidth_typeIICorrelation_unequal_quadratic_le
          N M K B E hM hK hB hn hn' hne hnB hn'B hsum hwidthOne hupper)
    let Q : ℝ := C * (480 * J * ((J + 1) *
      (1 + Real.log ((hi - lo : ℕ) : ℝ)) * K))
    have hlog : 0 ≤ Real.log ((hi - lo : ℕ) : ℝ) := by
      apply Real.log_nonneg
      exact_mod_cast hLength
    have hQ : 0 ≤ Q := by unfold Q C J; positivity
    have hpoint' :
        ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
            (shortIntervalBlock K₀ K₁ q k) N M 2 n n'‖ ≤ Q * p := by
      refine hpoint.trans_eq ?_
      unfold Q C J p N' M' lo hi
      ring
    have hfinal :
        ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
            (shortIntervalBlock K₀ K₁ q k) N M 2 n n'‖ ≤
          Q * (E ^ δ + 4 * typeIIDecayKernel B F δ (Nat.dist n' n)) :=
      hpoint'.trans (mul_le_mul_of_nonneg_left hwidth hQ)
    convert hfinal using 1
    all_goals
      unfold Q C J F δ lo hi
      ring
  · have hhi : hi ≤ lo := by omega
    have hzero : hi - lo = 0 := Nat.sub_eq_zero_of_le hhi
    have hIco : Finset.Ico lo hi = ∅ := Finset.Ico_eq_empty_of_le hhi
    rw [typeIIProductRestrictedCorrelationSum_shortIntervalBlock_eq
      a b K₀ K₁ q k N M 2 hq hn hn', reciprocalPhaseSum, hIco, hzero]
    simp only [Finset.sum_empty, norm_zero, Nat.cast_zero, Real.log_zero,
      add_zero]
    have hFnonneg : 0 ≤ F := by unfold F reciprocalPhaseScale; positivity
    have hkernel : 0 ≤ typeIIDecayKernel B F δ (Nat.dist n' n) :=
      typeIIDecayKernel_nonneg δ (Nat.dist n' n) hB hFnonneg
    have hEpow : 0 ≤ E ^ δ := Real.rpow_nonneg hEnonneg δ
    have hsumNonneg :
        0 ≤ E ^ δ + 4 * typeIIDecayKernel B F δ (Nat.dist n' n) := by
      positivity
    have hsumRaw : 0 ≤ E ^ (1 / 1024 : ℝ) +
        4 * typeIIDecayKernel B (reciprocalPhaseScale N M 2 (K * B))
          (1 / 1024 : ℝ) (Nat.dist n' n) := by
      simpa only [F, δ] using hsumNonneg
    positivity

/-- Pointwise low-transformed-scale Weyl estimate for an unequal quadratic
Type II correlation. -/
theorem norm_typeIIProductRestrictedCorrelationSum_le_fourStepWeyl_decayKernel_unequal_quadratic_lowScale
    (a b K₀ K₁ q k : ℕ) (N M : ℝ) (orders : Finset ℕ)
    {n n' : ℕ} {K B E : ℝ}
    (hK₀ : 0 < K₀) (hq : 0 < q) (hn : 0 < n) (hn' : 0 < n') (hne : n ≠ n')
    (hM : M ≠ 0) (hKouter : K = ((K₀ + k * q : ℕ) : ℝ))
    (hB : 0 < B)
    (hnB : (n : ℝ) ≤ B) (hn'B : (n' : ℝ) ≤ B)
    (hsum : B ≤ (n : ℝ) + n')
    (hrFive : 5 ∈ orders) (hrSix : 6 ∈ orders)
    (hupper :
      reciprocalPhaseScale
          (typeIICorrelationLinearParameter N n n')
          (typeIICorrelationHigherParameter M 2 n n') 2 K / K ^ 5 ≤ E)
    (hscale :
      reciprocalPhaseScale
          (typeIICorrelationLinearParameter N n n')
          (typeIICorrelationHigherParameter M 2 n n') 2 K ≤ K ^ 4)
    (hfar : 3 ≤ (Nat.dist n' n : ℝ) *
      reciprocalPhaseScale N M 2 (K * B) / B)
    (hKbudget : 4 * (240 * ((((5 + 2) ^ 5 : ℕ) : ℝ))) ≤ K)
    (hqK : 5 * (q : ℝ) ≤ K) :
    let lo := typeIIProductRestrictedBlockLower a K₀ q k n n'
    let hi := typeIIProductRestrictedBlockUpper b K₀ K₁ q k n n'
    let F := reciprocalPhaseScale N M 2 (K * B)
    ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
        (shortIntervalBlock K₀ K₁ q k) N M 2 n n'‖ ≤
      ((370 * orders.card + 173 : ℕ) : ℝ) *
        (480 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
          (((((5 + 2) ^ 5 : ℕ) : ℝ)) + 1) *
          (1 + Real.log ((hi - lo : ℕ) : ℝ)) * K *
            (E ^ (1 / 1024 : ℝ) +
              4 * typeIIDecayKernel B F (1 / 1024 : ℝ) (Nat.dist n' n))) := by
  dsimp only
  have hKnat : 0 < K₀ + k * q := by omega
  have hK : 0 < K := by rw [hKouter]; exact_mod_cast hKnat
  have hpairError :
      reciprocalPhaseScale
          (typeIICorrelationLinearParameter N n n')
          (typeIICorrelationHigherParameter M 2 n n') 2 K / K ^ 5 ≤ 1 / K :=
    div_pow_five_le_one_div_of_le_pow_four hK hscale
  have hanalytic :
      let N' := typeIICorrelationLinearParameter N n n'
      let M' := typeIICorrelationHigherParameter M 2 n n'
      let lo := typeIIProductRestrictedBlockLower a K₀ q k n n'
      let hi := typeIIProductRestrictedBlockUpper b K₀ K₁ q k n n'
      1 ≤ hi - lo →
        reciprocalPhaseScale N' M' 2 K ≤ K ^ 4 ∧
        reciprocalPhaseFourStepEffectiveErrorScale N' M' 2 K (hi - lo) ≤ 1 ∧
        (lo : ℝ) ∈ Set.Icc K (2 * K) ∧
        (lo : ℝ) + (hi - lo : ℕ) +
            (4 * reciprocalPhaseFourStepOptimizedRange N' M' 2 K (hi - lo) : ℕ) ≤
          2 * K ∧
        (lo : ℝ) + (hi - lo : ℕ) +
            (4 * reciprocalPhaseFourStepOptimizedRange N' M' 2 K (hi - lo) : ℕ) ≤
          2 * K ∧
        ∀ t ∈ Set.Icc K (2 * K), t ^ (2 - 1) ≤ 2 * K ^ (2 - 1) := by
    dsimp only
    intro hLength
    have herror : reciprocalPhaseFourStepEffectiveErrorScale
        (typeIICorrelationLinearParameter N n n')
        (typeIICorrelationHigherParameter M 2 n n') 2 K
        (typeIIProductRestrictedBlockUpper b K₀ K₁ q k n n' -
          typeIIProductRestrictedBlockLower a K₀ q k n n') ≤ 1 := by
      apply reciprocalPhaseFourStepEffectiveErrorScale_typeIICorrelation_le_one_of_far_unequal
        N M K B
        (reciprocalPhaseScale
            (typeIICorrelationLinearParameter N n n')
            (typeIICorrelationHigherParameter M 2 n n') 2 K / K ^ 5)
        hK hB hn hn' hnB hn'B hsum
      · exact le_rfl
      · apply mul_error_le_one_div_four_of_error_le_one_div
        · positivity
        · exact hK
        · exact hpairError
        · exact hKbudget
      · exact hLength
      · exact hfar
    have hM' : typeIICorrelationHigherParameter M 2 n n' ≠ 0 :=
      typeIICorrelationHigherParameter_ne_zero hM (by norm_num)
        (Nat.ne_of_gt hn) (Nat.ne_of_gt hn') hne
    have hF' : 0 < reciprocalPhaseScale
        (typeIICorrelationLinearParameter N n n')
        (typeIICorrelationHigherParameter M 2 n n') 2 K := by
      unfold reciprocalPhaseScale
      have hterm : 0 < |typeIICorrelationHigherParameter M 2 n n'| / K ^ 2 :=
        div_pos (abs_pos.mpr hM') (pow_pos hK 2)
      positivity
    have hlenNat :
        typeIIProductRestrictedBlockUpper b K₀ K₁ q k n n' -
          typeIIProductRestrictedBlockLower a K₀ q k n n' ≤ q :=
      typeIIProductRestrictedBlock_length_le a b K₀ K₁ q k n n'
    have hlen :
        ((typeIIProductRestrictedBlockUpper b K₀ K₁ q k n n' -
          typeIIProductRestrictedBlockLower a K₀ q k n n' : ℕ) : ℝ) ≤ (q : ℝ) := by
      exact_mod_cast hlenNat
    have hrangeRaw := reciprocalPhaseFourStepOptimizedRange_cast_le_of_error_bound
      (typeIICorrelationLinearParameter N n n')
      (typeIICorrelationHigherParameter M 2 n n') hK hF' herror
    have hrange :
        (reciprocalPhaseFourStepOptimizedRange
          (typeIICorrelationLinearParameter N n n')
          (typeIICorrelationHigherParameter M 2 n n') 2 K
          (typeIIProductRestrictedBlockUpper b K₀ K₁ q k n n' -
            typeIIProductRestrictedBlockLower a K₀ q k n n') : ℝ) ≤ (q : ℝ) := by
      calc
        (reciprocalPhaseFourStepOptimizedRange
            (typeIICorrelationLinearParameter N n n')
            (typeIICorrelationHigherParameter M 2 n n') 2 K
            (typeIIProductRestrictedBlockUpper b K₀ K₁ q k n n' -
              typeIIProductRestrictedBlockLower a K₀ q k n n') : ℝ) ≤
          ((typeIIProductRestrictedBlockUpper b K₀ K₁ q k n n' -
            typeIIProductRestrictedBlockLower a K₀ q k n n' : ℕ) : ℝ) *
              (1 : ℝ) ^ (1 / 128 : ℝ) := hrangeRaw
        _ = ((typeIIProductRestrictedBlockUpper b K₀ K₁ q k n n' -
            typeIIProductRestrictedBlockLower a K₀ q k n n' : ℕ) : ℝ) := by
              norm_num
        _ ≤ (q : ℝ) := hlen
    have hmargin : (q : ℝ) +
        (4 * reciprocalPhaseFourStepOptimizedRange
          (typeIICorrelationLinearParameter N n n')
          (typeIICorrelationHigherParameter M 2 n n') 2 K
          (typeIIProductRestrictedBlockUpper b K₀ K₁ q k n n' -
            typeIIProductRestrictedBlockLower a K₀ q k n n') : ℕ) ≤ K := by
      norm_num only [Nat.cast_mul, Nat.cast_ofNat]
      have hfour := mul_le_mul_of_nonneg_left hrange (by norm_num : (0 : ℝ) ≤ 4)
      calc
        (q : ℝ) + 4 *
            (reciprocalPhaseFourStepOptimizedRange
              (typeIICorrelationLinearParameter N n n')
              (typeIICorrelationHigherParameter M 2 n n') 2 K
              (typeIIProductRestrictedBlockUpper b K₀ K₁ q k n n' -
                typeIIProductRestrictedBlockLower a K₀ q k n n') : ℝ) ≤
          (q : ℝ) + 4 * (q : ℝ) := add_le_add le_rfl hfour
        _ = 5 * (q : ℝ) := by ring
        _ ≤ K := hqK
    have hgeom := typeIIProductRestrictedBlock_quadratic_fourStep_geometryAt
      a b K₀ K₁ q k n n'
      (typeIICorrelationLinearParameter N n n')
      (typeIICorrelationHigherParameter M 2 n n') K hKouter hLength hmargin
    exact ⟨hscale, herror, hgeom.1,
      hgeom.2.1, hgeom.2.1, hgeom.2.2⟩
  exact norm_typeIIProductRestrictedCorrelationSum_le_fourStepWeyl_decayKernel_unequal_quadratic
    a b K₀ K₁ q k N M orders hq hn hn' hne hM hK hB hnB hn'B hsum
      hrFive hrSix hupper hanalytic

/-- Replace the correlation-dependent logarithm in the unequal-parameter
pointwise Weyl bound by the fixed outer-block length. -/
theorem norm_typeIIProductRestrictedCorrelationSum_le_fourStepWeyl_decayKernel_blockLength_unequal
    (a b K₀ K₁ q k : ℕ) (N M : ℝ) {j : ℕ} (orders : Finset ℕ)
    {n n' : ℕ} {K B E : ℝ}
    (hq : 0 < q) (hK : 0 ≤ K) (hB : 0 < B) (hE : 0 ≤ E)
    (hpoint :
      let lo := typeIIProductRestrictedBlockLower a K₀ q k n n'
      let hi := typeIIProductRestrictedBlockUpper b K₀ K₁ q k n n'
      let F := reciprocalPhaseScale N M j (K * B)
      ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
          (shortIntervalBlock K₀ K₁ q k) N M j n n'‖ ≤
        ((370 * orders.card + 173 : ℕ) : ℝ) *
          (480 * ((((5 + j) ^ 5 : ℕ) : ℝ)) *
            (((((5 + j) ^ 5 : ℕ) : ℝ)) + 1) *
            (1 + Real.log ((hi - lo : ℕ) : ℝ)) * K *
              (E ^ (1 / 1024 : ℝ) +
                4 * typeIIDecayKernel B F (1 / 1024 : ℝ) (Nat.dist n' n)))) :
    let F := reciprocalPhaseScale N M j (K * B)
    let Q := ((370 * orders.card + 173 : ℕ) : ℝ) *
      (480 * ((((5 + j) ^ 5 : ℕ) : ℝ)) *
        (((((5 + j) ^ 5 : ℕ) : ℝ)) + 1) *
          (1 + Real.log (q : ℝ)) * K)
    ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
        (shortIntervalBlock K₀ K₁ q k) N M j n n'‖ ≤
      Q * (4 * typeIIDecayKernel B F (1 / 1024 : ℝ) (Nat.dist n' n) +
        E ^ (1 / 1024 : ℝ)) := by
  dsimp only at hpoint ⊢
  let lo := typeIIProductRestrictedBlockLower a K₀ q k n n'
  let hi := typeIIProductRestrictedBlockUpper b K₀ K₁ q k n n'
  let F := reciprocalPhaseScale N M j (K * B)
  let J : ℝ := ((((5 + j) ^ 5 : ℕ) : ℝ))
  let C : ℝ := ((370 * orders.card + 173 : ℕ) : ℝ)
  let W := E ^ (1 / 1024 : ℝ) +
    4 * typeIIDecayKernel B F (1 / 1024 : ℝ) (Nat.dist n' n)
  have hlen : hi - lo ≤ q :=
    typeIIProductRestrictedBlock_length_le a b K₀ K₁ q k n n'
  have hqReal : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hlogq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hqReal
  have hloglen : 0 ≤ Real.log ((hi - lo : ℕ) : ℝ) := by
    by_cases hz : hi - lo = 0
    · simp [hz]
    · exact Real.log_nonneg (by exact_mod_cast Nat.pos_of_ne_zero hz)
  have hlogLe : Real.log ((hi - lo : ℕ) : ℝ) ≤ Real.log (q : ℝ) := by
    by_cases hz : hi - lo = 0
    · simpa [hz] using hlogq
    · apply Real.log_le_log
      · exact_mod_cast Nat.pos_of_ne_zero hz
      · exact_mod_cast hlen
  have hFnonneg : 0 ≤ F := by unfold F reciprocalPhaseScale; positivity
  have hkernel :
      0 ≤ typeIIDecayKernel B F (1 / 1024 : ℝ) (Nat.dist n' n) :=
    typeIIDecayKernel_nonneg _ _ hB hFnonneg
  have hEnonneg : 0 ≤ E ^ (1 / 1024 : ℝ) := Real.rpow_nonneg hE _
  have hW : 0 ≤ W := by unfold W; positivity
  have hfactor :
      C * (480 * J * ((J + 1) *
          (1 + Real.log ((hi - lo : ℕ) : ℝ)) * K)) ≤
        C * (480 * J * ((J + 1) * (1 + Real.log (q : ℝ)) * K)) := by
    gcongr
  have hpoint' :
      ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
          (shortIntervalBlock K₀ K₁ q k) N M j n n'‖ ≤
        (C * (480 * J * ((J + 1) *
          (1 + Real.log ((hi - lo : ℕ) : ℝ)) * K))) * W := by
    refine hpoint.trans_eq ?_
    unfold C J W F lo hi
    ring
  calc
    ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
        (shortIntervalBlock K₀ K₁ q k) N M j n n'‖ ≤
      (C * (480 * J * ((J + 1) *
        (1 + Real.log ((hi - lo : ℕ) : ℝ)) * K))) * W := hpoint'
    _ ≤ (C * (480 * J * ((J + 1) * (1 + Real.log (q : ℝ)) * K))) * W :=
      mul_le_mul_of_nonneg_right hfactor hW
    _ = ((370 * orders.card + 173 : ℕ) : ℝ) *
        (480 * ((((5 + j) ^ 5 : ℕ) : ℝ)) *
          (((((5 + j) ^ 5 : ℕ) : ℝ)) + 1) *
            (1 + Real.log (q : ℝ)) * K) *
        (4 * typeIIDecayKernel B (reciprocalPhaseScale N M j (K * B))
            (1 / 1024 : ℝ) (Nat.dist n' n) + E ^ (1 / 1024 : ℝ)) := by
      unfold C J W F
      ring

/-- The trivial nearby-pair estimate for independent linear and higher phase
parameters, absorbed by the source decay kernel. -/
theorem norm_typeIIProductRestrictedCorrelationSum_near_le_decayKernel_blockLength_unequal
    (a b K₀ K₁ q k : ℕ) (N M : ℝ) {j : ℕ} (orders : Finset ℕ)
    {n n' : ℕ} {K B E : ℝ}
    (hq : 0 < q) (hn : 0 < n) (hn' : 0 < n')
    (hK : 0 < K) (hB : 0 < B) (hE : 0 ≤ E)
    (hqK : (q : ℝ) ≤ K)
    (hnear : (Nat.dist n' n : ℝ) *
      reciprocalPhaseScale N M j (K * B) / B ≤ 3) :
    let F := reciprocalPhaseScale N M j (K * B)
    let Q := ((370 * orders.card + 173 : ℕ) : ℝ) *
      (480 * ((((5 + j) ^ 5 : ℕ) : ℝ)) *
        (((((5 + j) ^ 5 : ℕ) : ℝ)) + 1) *
          (1 + Real.log (q : ℝ)) * K)
    ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
        (shortIntervalBlock K₀ K₁ q k) N M j n n'‖ ≤
      Q * (4 * typeIIDecayKernel B F (1 / 1024 : ℝ) (Nat.dist n' n) +
        E ^ (1 / 1024 : ℝ)) := by
  dsimp only
  let F := reciprocalPhaseScale N M j (K * B)
  let J : ℝ := ((((5 + j) ^ 5 : ℕ) : ℝ))
  let C : ℝ := ((370 * orders.card + 173 : ℕ) : ℝ)
  let Q : ℝ := C * (480 * J * ((J + 1) *
    (1 + Real.log (q : ℝ)) * K))
  let W : ℝ := 4 * typeIIDecayKernel B F (1 / 1024 : ℝ) (Nat.dist n' n) +
    E ^ (1 / 1024 : ℝ)
  have htrivial := norm_typeIIProductRestrictedCorrelationSum_le_blockLength
    a b K₀ K₁ q k N M j hq hn hn'
  have hqOne : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hlog : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hqOne
  have hF0 : 0 ≤ F := by unfold F reciprocalPhaseScale; positivity
  have hkernel : 1 / 4 ≤
      typeIIDecayKernel B F (1 / 1024 : ℝ) (Nat.dist n' n) := by
    apply one_div_four_le_typeIIDecayKernel_of_scaledDistance_le_three
      (Nat.dist n' n) hB hF0
    simpa only [F] using hnear
  have hEpow : 0 ≤ E ^ (1 / 1024 : ℝ) := Real.rpow_nonneg hE _
  have hWOne : 1 ≤ W := by unfold W; nlinarith
  have hC : 1 ≤ C := by
    unfold C
    exact_mod_cast (by omega : 1 ≤ 370 * orders.card + 173)
  have hJ : 1 ≤ J := by
    unfold J
    exact_mod_cast (one_le_pow₀ (by omega : 0 < 5 + j) : 1 ≤ (5 + j) ^ 5)
  have h480J : 1 ≤ 480 * J :=
    one_le_mul_of_one_le_of_one_le (by norm_num) hJ
  have hJplus : 1 ≤ J + 1 := by linarith
  have hlogFactor : 1 ≤ 1 + Real.log (q : ℝ) := by linarith
  have htail : 1 ≤ (J + 1) * (1 + Real.log (q : ℝ)) :=
    one_le_mul_of_one_le_of_one_le hJplus hlogFactor
  have hmiddle : 1 ≤ 480 * J * ((J + 1) * (1 + Real.log (q : ℝ))) :=
    one_le_mul_of_one_le_of_one_le h480J htail
  have hcoefficient : 1 ≤ C *
      (480 * J * ((J + 1) * (1 + Real.log (q : ℝ)))) :=
    one_le_mul_of_one_le_of_one_le hC hmiddle
  have hQ0 : 0 ≤ Q := by unfold Q; positivity
  have hKQ : K ≤ Q := by
    have hmul := mul_le_mul_of_nonneg_right hcoefficient hK.le
    calc
      K = 1 * K := by ring
      _ ≤ (C * (480 * J * ((J + 1) *
          (1 + Real.log (q : ℝ))))) * K := hmul
      _ = Q := by unfold Q; ring
  have hQW : Q ≤ Q * W := by
    have hprod := mul_nonneg hQ0 (sub_nonneg.mpr hWOne)
    nlinarith
  calc
    ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
        (shortIntervalBlock K₀ K₁ q k) N M j n n'‖ ≤ (q : ℝ) := htrivial
    _ ≤ K := hqK
    _ ≤ Q := hKQ
    _ ≤ Q * W := hQW
    _ = ((370 * orders.card + 173 : ℕ) : ℝ) *
        (480 * ((((5 + j) ^ 5 : ℕ) : ℝ)) *
          (((((5 + j) ^ 5 : ℕ) : ℝ)) + 1) *
            (1 + Real.log (q : ℝ)) * K) *
        (4 * typeIIDecayKernel B (reciprocalPhaseScale N M j (K * B))
            (1 / 1024 : ℝ) (Nat.dist n' n) + E ^ (1 / 1024 : ℝ)) := by
      unfold Q W C J F
      ring

/-- Unequal-parameter Type II aggregation after an arbitrary far-pair estimate.
Nearby pairs are absorbed by the same source decay kernel. -/
theorem sum_typeIIProductRestrictedInnerSum_shortIntervalDoubleBlock_norm_sq_le_nearFar_of_farBound_additiveError_unequal
    (a b : ℕ) (γ : ℕ → ℂ) (N M : ℝ) {j : ℕ} (orders : Finset ℕ)
    (K₀ K₁ S₀ S₁ qouter qinner kouter kinner : ℕ)
    {L K B Z : ℝ}
    (hK₀ : 0 < K₀) (hS₀ : 0 < S₀)
    (hqouter : 0 < qouter) (hqinner : 0 < qinner)
    (hL : 0 ≤ L) (hγ : ∀ n, ‖γ n‖ ≤ L)
    (hK : 0 < K) (hB : 0 < B) (hqinnerB : (qinner : ℝ) ≤ B)
    (hF : 1 ≤ reciprocalPhaseScale N M j (K * B)) (hZ : 0 ≤ Z)
    (hqouterK : (qouter : ℝ) ≤ K)
    (hfarBound : ∀ n ∈ shortIntervalBlock S₀ S₁ qinner kinner,
      ∀ n' ∈ shortIntervalBlock S₀ S₁ qinner kinner, n ≠ n' →
        3 ≤ (Nat.dist n' n : ℝ) *
          reciprocalPhaseScale N M j (K * B) / B →
        let F := reciprocalPhaseScale N M j (K * B)
        let Q := ((370 * orders.card + 173 : ℕ) : ℝ) *
          (480 * ((((5 + j) ^ 5 : ℕ) : ℝ)) *
            (((((5 + j) ^ 5 : ℕ) : ℝ)) + 1) *
              (1 + Real.log (qouter : ℝ)) * K)
        ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
            (shortIntervalBlock K₀ K₁ qouter kouter)
            N M j n n'‖ ≤
          Q * (4 * typeIIDecayKernel B F (1 / 1024 : ℝ) (Nat.dist n' n) + Z)) :
    let F := reciprocalPhaseScale N M j (K * B)
    let Q := ((370 * orders.card + 173 : ℕ) : ℝ) *
      (480 * ((((5 + j) ^ 5 : ℕ) : ℝ)) *
        (((((5 + j) ^ 5 : ℕ) : ℝ)) + 1) *
          (1 + Real.log (qouter : ℝ)) * K)
    ∑ m ∈ shortIntervalBlock K₀ K₁ qouter kouter,
        ‖typeIIProductRestrictedInnerSum (Finset.Ico a b)
          (shortIntervalBlock S₀ S₁ qinner kinner)
          γ N M j m‖ ^ 2 ≤
      (qouter : ℝ) * (qinner : ℝ) * L ^ 2 +
        L ^ 2 * ((qinner : ℝ) *
          (Q * (4 *
              (2 * ((2 ^ (1 - (1 / 1024 : ℝ)) /
                (1 - (1 / 1024 : ℝ))) * B * F ^ (-(1 / 1024 : ℝ)))) +
            (qinner : ℝ) * Z))) := by
  dsimp only
  let F := reciprocalPhaseScale N M j (K * B)
  let δ : ℝ := 1 / 1024
  let Q : ℝ := ((370 * orders.card + 173 : ℕ) : ℝ) *
    (480 * ((((5 + j) ^ 5 : ℕ) : ℝ)) *
      (((((5 + j) ^ 5 : ℕ) : ℝ)) + 1) *
        (1 + Real.log (qouter : ℝ)) * K)
  have hQ : 0 ≤ Q := by
    have hlog : 0 ≤ Real.log (qouter : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hqouter)
    unfold Q
    positivity
  have hpoint : ∀ n ∈ shortIntervalBlock S₀ S₁ qinner kinner,
      ∀ n' ∈ shortIntervalBlock S₀ S₁ qinner kinner, n ≠ n' →
      ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
          (shortIntervalBlock K₀ K₁ qouter kouter)
          N M j n n'‖ ≤
        Q * (4 * typeIIDecayKernel B F δ (Nat.dist n' n) + Z) := by
    intro n hnmem n' hn'mem hne
    have hnData := mem_shortIntervalBlock.mp hnmem
    have hn'Data := mem_shortIntervalBlock.mp hn'mem
    have hnpos : 0 < n := by omega
    have hn'pos : 0 < n' := by omega
    by_cases hnear : (Nat.dist n' n : ℝ) *
        reciprocalPhaseScale N M j (K * B) / B ≤ 3
    · have hnearZero :=
        norm_typeIIProductRestrictedCorrelationSum_near_le_decayKernel_blockLength_unequal
          a b K₀ K₁ qouter kouter N M orders (E := (0 : ℝ))
            hqouter hnpos hn'pos hK hB (by norm_num) hqouterK hnear
      have hbase :
          ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
              (shortIntervalBlock K₀ K₁ qouter kouter) N M j n n'‖ ≤
            Q * (4 * typeIIDecayKernel B F δ (Nat.dist n' n)) := by
        simpa only [F, Q, δ, Real.zero_rpow (by norm_num : (1 / 1024 : ℝ) ≠ 0),
          add_zero] using hnearZero
      exact hbase.trans (mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_right hZ) hQ)
    · have hfar : 3 ≤ (Nat.dist n' n : ℝ) *
          reciprocalPhaseScale N M j (K * B) / B :=
        (lt_of_not_ge hnear).le
      simpa only [F, Q, δ] using hfarBound n hnmem n' hn'mem hne hfar
  have hresult :=
    sum_typeIIProductRestrictedInnerSum_shortIntervalDoubleBlock_norm_sq_le_sourceScale_blockLengths
      (Finset.Ico a b) γ N M j K₀ K₁ S₀ S₁ qouter qinner kouter kinner
      hK₀ hS₀ hqouter hqinner hL hγ hQ (by norm_num : (0 : ℝ) ≤ 4)
      hZ hB hF (by norm_num : (0 : ℝ) ≤ 1 / 1024)
      (by norm_num : (1 / 1024 : ℝ) < 1) hqinnerB hpoint
  simpa only [F, Q, δ] using hresult

/-- Unequal quadratic Type II Weyl--Vinogradov hybrid with the intrinsic
low-scale error `(1/K)^(1/1024)`.  The extra lower-band hypothesis is exactly
what lets the transformed quadratic coefficient control the original source
scale when the two phase parameters are independent. -/
theorem sum_typeIIProductRestrictedInnerSum_shortIntervalDoubleBlock_norm_sq_le_weylVinogradov_quadratic_intrinsicError_unequal
    (a b : ℕ) (γ : ℕ → ℂ) (N M : ℝ) (orders : Finset ℕ)
    (K₀ K₁ S₀ S₁ qouter qinner kouter kinner : ℕ)
    {L K B V : ℝ}
    (hK₀ : 0 < K₀) (hS₀ : 0 < S₀)
    (hqouter : 0 < qouter) (hqinner : 0 < qinner)
    (hL : 0 ≤ L) (hγ : ∀ n, ‖γ n‖ ≤ L)
    (hM : M ≠ 0) (hKouter : K = ((K₀ + kouter * qouter : ℕ) : ℝ))
    (hB : 0 < B) (hBsum : B ≤ 2 * (S₀ : ℝ))
    (hS₁ : (S₁ : ℝ) ≤ B) (hqinnerB : (qinner : ℝ) ≤ B)
    (hF : 1 ≤ reciprocalPhaseScale N M 2 (K * B))
    (hrFive : 5 ∈ orders) (hrSix : 6 ∈ orders)
    (hKbudget : 4 * (240 * ((((5 + 2) ^ 5 : ℕ) : ℝ))) ≤ K)
    (hqouterK : 5 * (qouter : ℝ) ≤ K) (hV : 0 ≤ V)
    (hhigh : ∀ n ∈ shortIntervalBlock S₀ S₁ qinner kinner,
      ∀ n' ∈ shortIntervalBlock S₀ S₁ qinner kinner, n ≠ n' →
        3 ≤ (Nat.dist n' n : ℝ) *
          reciprocalPhaseScale N M 2 (K * B) / B →
        K ^ 4 < reciprocalPhaseScale
          (typeIICorrelationLinearParameter N n n')
          (typeIICorrelationHigherParameter M 2 n n') 2 K →
        let F := reciprocalPhaseScale N M 2 (K * B)
        let Q := ((370 * orders.card + 173 : ℕ) : ℝ) *
          (480 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
            (((((5 + 2) ^ 5 : ℕ) : ℝ)) + 1) *
              (1 + Real.log (qouter : ℝ)) * K)
        ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
            (shortIntervalBlock K₀ K₁ qouter kouter)
            N M 2 n n'‖ ≤
          Q * (4 * typeIIDecayKernel B F (1 / 1024 : ℝ) (Nat.dist n' n) + V)) :
    let F := reciprocalPhaseScale N M 2 (K * B)
    let Q := ((370 * orders.card + 173 : ℕ) : ℝ) *
      (480 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
        (((((5 + 2) ^ 5 : ℕ) : ℝ)) + 1) *
          (1 + Real.log (qouter : ℝ)) * K)
    ∑ m ∈ shortIntervalBlock K₀ K₁ qouter kouter,
        ‖typeIIProductRestrictedInnerSum (Finset.Ico a b)
          (shortIntervalBlock S₀ S₁ qinner kinner)
          γ N M 2 m‖ ^ 2 ≤
      (qouter : ℝ) * (qinner : ℝ) * L ^ 2 +
        L ^ 2 * ((qinner : ℝ) *
          (Q * (4 *
              (2 * ((2 ^ (1 - (1 / 1024 : ℝ)) /
                (1 - (1 / 1024 : ℝ))) * B * F ^ (-(1 / 1024 : ℝ)))) +
            (qinner : ℝ) * ((1 / K) ^ (1 / 1024 : ℝ) + V)))) := by
  dsimp only
  let F := reciprocalPhaseScale N M 2 (K * B)
  let δ : ℝ := 1 / 1024
  let Q : ℝ := ((370 * orders.card + 173 : ℕ) : ℝ) *
    (480 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
      (((((5 + 2) ^ 5 : ℕ) : ℝ)) + 1) *
        (1 + Real.log (qouter : ℝ)) * K)
  have hKnat : 0 < K₀ + kouter * qouter := by omega
  have hK : 0 < K := by rw [hKouter]; exact_mod_cast hKnat
  have hInvK : 0 ≤ 1 / K := by positivity
  have hInvKpow : 0 ≤ (1 / K) ^ δ := Real.rpow_nonneg hInvK _
  have hZ : 0 ≤ (1 / K) ^ δ + V := add_nonneg hInvKpow hV
  have hQ : 0 ≤ Q := by
    have hlog : 0 ≤ Real.log (qouter : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hqouter)
    unfold Q
    positivity
  have hfarBound : ∀ n ∈ shortIntervalBlock S₀ S₁ qinner kinner,
      ∀ n' ∈ shortIntervalBlock S₀ S₁ qinner kinner, n ≠ n' →
        3 ≤ (Nat.dist n' n : ℝ) *
          reciprocalPhaseScale N M 2 (K * B) / B →
        ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
            (shortIntervalBlock K₀ K₁ qouter kouter) N M 2 n n'‖ ≤
          Q * (4 * typeIIDecayKernel B F δ (Nat.dist n' n) +
            ((1 / K) ^ δ + V)) := by
    intro n hnmem n' hn'mem hne hfar
    have hnData := mem_shortIntervalBlock.mp hnmem
    have hn'Data := mem_shortIntervalBlock.mp hn'mem
    have hnpos : 0 < n := by omega
    have hn'pos : 0 < n' := by omega
    have hnLower : S₀ ≤ n := by omega
    have hn'Lower : S₀ ≤ n' := by omega
    have hnUpper : n ≤ S₁ := by omega
    have hn'Upper : n' ≤ S₁ := by omega
    have hnB : (n : ℝ) ≤ B :=
      (by exact_mod_cast hnUpper : (n : ℝ) ≤ (S₁ : ℝ)).trans hS₁
    have hn'B : (n' : ℝ) ≤ B :=
      (by exact_mod_cast hn'Upper : (n' : ℝ) ≤ (S₁ : ℝ)).trans hS₁
    have hsum : B ≤ (n : ℝ) + n' := by
      have hnLowerReal : (S₀ : ℝ) ≤ n := by exact_mod_cast hnLower
      have hn'LowerReal : (S₀ : ℝ) ≤ n' := by exact_mod_cast hn'Lower
      nlinarith
    by_cases hscale : reciprocalPhaseScale
        (typeIICorrelationLinearParameter N n n')
        (typeIICorrelationHigherParameter M 2 n n') 2 K ≤ K ^ 4
    · have hpairError : reciprocalPhaseScale
          (typeIICorrelationLinearParameter N n n')
          (typeIICorrelationHigherParameter M 2 n n') 2 K / K ^ 5 ≤ 1 / K :=
        div_pow_five_le_one_div_of_le_pow_four hK hscale
      have hraw :=
        norm_typeIIProductRestrictedCorrelationSum_le_fourStepWeyl_decayKernel_unequal_quadratic_lowScale
          a b K₀ K₁ qouter kouter N M orders hK₀ hqouter hnpos hn'pos hne
            hM hKouter hB hnB hn'B hsum hrFive hrSix hpairError hscale hfar
            hKbudget hqouterK
      have hlow :=
        norm_typeIIProductRestrictedCorrelationSum_le_fourStepWeyl_decayKernel_blockLength_unequal
          a b K₀ K₁ qouter kouter N M orders hqouter hK.le hB hInvK hraw
      have hadd : 4 * typeIIDecayKernel B F δ (Nat.dist n' n) +
          (1 / K) ^ δ ≤
          4 * typeIIDecayKernel B F δ (Nat.dist n' n) +
            ((1 / K) ^ δ + V) := by linarith
      have hlow' : ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
            (shortIntervalBlock K₀ K₁ qouter kouter) N M 2 n n'‖ ≤
          Q * (4 * typeIIDecayKernel B F δ (Nat.dist n' n) +
            (1 / K) ^ δ) := by
        simpa only [F, Q, δ] using hlow
      exact hlow'.trans (mul_le_mul_of_nonneg_left hadd hQ)
    · have hscaleHigh : K ^ 4 < reciprocalPhaseScale
          (typeIICorrelationLinearParameter N n n')
          (typeIICorrelationHigherParameter M 2 n n') 2 K := lt_of_not_ge hscale
      have hhighPair := hhigh n hnmem n' hn'mem hne hfar hscaleHigh
      have hadd : 4 * typeIIDecayKernel B F δ (Nat.dist n' n) + V ≤
          4 * typeIIDecayKernel B F δ (Nat.dist n' n) +
            ((1 / K) ^ δ + V) := by linarith
      have hhighPair' : ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
            (shortIntervalBlock K₀ K₁ qouter kouter) N M 2 n n'‖ ≤
          Q * (4 * typeIIDecayKernel B F δ (Nat.dist n' n) + V) := by
        simpa only [F, Q, δ] using hhighPair
      exact hhighPair'.trans (mul_le_mul_of_nonneg_left hadd hQ)
  have hqouterK' : (qouter : ℝ) ≤ K := by nlinarith [hqouterK]
  have hresult :=
    sum_typeIIProductRestrictedInnerSum_shortIntervalDoubleBlock_norm_sq_le_nearFar_of_farBound_additiveError_unequal
      a b γ N M orders K₀ K₁ S₀ S₁ qouter qinner kouter kinner
      hK₀ hS₀ hqouter hqinner hL hγ hK hB hqinnerB hF hZ hqouterK' hfarBound
  simpa only [F, Q, δ] using hresult

/-- Canonical Vaughan dyadic-block specialization of the unequal quadratic
Weyl--Vinogradov hybrid. -/
theorem sum_typeIIProductRestrictedInnerSum_vaughanDoubleBlock_norm_sq_le_weylVinogradov_quadratic_intrinsicError_unequal
    (a b Bcap : ℕ) (γ : ℕ → ℂ) (N M : ℝ) (orders : Finset ℕ)
    (sk tl : ℕ × ℕ) {L d V : ℝ}
    (hBcap : 0 < Bcap) (hlog : 2 ≤ Real.log Bcap)
    (hDouter : (vaughanShortIntervalBudget Bcap : ℝ) ≤ (2 ^ sk.1 : ℕ))
    (hL : 0 ≤ L) (hγ : ∀ n, ‖γ n‖ ≤ L) (hM : M ≠ 0)
    (hrFive : 5 ∈ orders) (hrSix : 6 ∈ orders) (hd : 0 ≤ d)
    (hFhigh : (Real.log Bcap) ^ d ≤ reciprocalPhaseScale N M 2
      (((dyadicShortIntervalLeftEndpoint (vaughanShortIntervalBudget Bcap) sk : ℕ) : ℝ) *
        ((2 * 2 ^ tl.1 : ℕ) : ℝ)))
    (hV : 0 ≤ V)
    (hhigh :
      let qouter := dyadicShortIntervalLength (2 ^ sk.1)
        (vaughanShortIntervalBudget Bcap)
      let K : ℝ := (dyadicShortIntervalLeftEndpoint
        (vaughanShortIntervalBudget Bcap) sk : ℕ)
      let B : ℝ := (2 * 2 ^ tl.1 : ℕ)
      ∀ n ∈ dyadicShortIntervalIndexedBlock
          (vaughanShortIntervalBudget Bcap) tl,
        ∀ n' ∈ dyadicShortIntervalIndexedBlock
            (vaughanShortIntervalBudget Bcap) tl, n ≠ n' →
          3 ≤ (Nat.dist n' n : ℝ) *
            reciprocalPhaseScale N M 2 (K * B) / B →
          K ^ 4 < reciprocalPhaseScale
            (typeIICorrelationLinearParameter N n n')
            (typeIICorrelationHigherParameter M 2 n n') 2 K →
          let F := reciprocalPhaseScale N M 2 (K * B)
          let Q := ((370 * orders.card + 173 : ℕ) : ℝ) *
            (480 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
              (((((5 + 2) ^ 5 : ℕ) : ℝ)) + 1) *
                (1 + Real.log (qouter : ℝ)) * K)
          ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
              (dyadicShortIntervalIndexedBlock
                (vaughanShortIntervalBudget Bcap) sk)
              N M 2 n n'‖ ≤
            Q * (4 * typeIIDecayKernel B F (1 / 1024 : ℝ) (Nat.dist n' n) + V)) :
    let qouter := dyadicShortIntervalLength (2 ^ sk.1)
      (vaughanShortIntervalBudget Bcap)
    let qinner := dyadicShortIntervalLength (2 ^ tl.1)
      (vaughanShortIntervalBudget Bcap)
    let K : ℝ := (dyadicShortIntervalLeftEndpoint
      (vaughanShortIntervalBudget Bcap) sk : ℕ)
    let B : ℝ := (2 * 2 ^ tl.1 : ℕ)
    let F := reciprocalPhaseScale N M 2 (K * B)
    let Q := ((370 * orders.card + 173 : ℕ) : ℝ) *
      (480 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
        (((((5 + 2) ^ 5 : ℕ) : ℝ)) + 1) *
          (1 + Real.log (qouter : ℝ)) * K)
    ∑ m ∈ dyadicShortIntervalIndexedBlock
          (vaughanShortIntervalBudget Bcap) sk,
        ‖typeIIProductRestrictedInnerSum (Finset.Ico a b)
          (dyadicShortIntervalIndexedBlock (vaughanShortIntervalBudget Bcap) tl)
          γ N M 2 m‖ ^ 2 ≤
      (qouter : ℝ) * (qinner : ℝ) * L ^ 2 +
        L ^ 2 * ((qinner : ℝ) *
          (Q * (4 *
              (2 * ((2 ^ (1 - (1 / 1024 : ℝ)) /
                (1 - (1 / 1024 : ℝ))) * B * F ^ (-(1 / 1024 : ℝ)))) +
            (qinner : ℝ) * ((1 / K) ^ (1 / 1024 : ℝ) + V)))) := by
  dsimp only
  let qouter := dyadicShortIntervalLength (2 ^ sk.1)
    (vaughanShortIntervalBudget Bcap)
  let qinner := dyadicShortIntervalLength (2 ^ tl.1)
    (vaughanShortIntervalBudget Bcap)
  let K : ℝ := (dyadicShortIntervalLeftEndpoint
    (vaughanShortIntervalBudget Bcap) sk : ℕ)
  let B : ℝ := (2 * 2 ^ tl.1 : ℕ)
  have hbudget : 0 < vaughanShortIntervalBudget Bcap :=
    vaughanShortIntervalBudget_pos Bcap
  have hbudgetLarge : 4 * (240 * ((((5 + 2) ^ 5 : ℕ) : ℝ))) ≤
      (vaughanShortIntervalBudget Bcap : ℝ) :=
    four_mul_quadraticWeylCoefficient_le_vaughanShortIntervalBudget hBcap hlog
  have hDouterPos : 0 < 2 ^ sk.1 := pow_pos (by omega) sk.1
  have hDinnerPos : 0 < 2 ^ tl.1 := pow_pos (by omega) tl.1
  have hqouter : 0 < qouter := by
    unfold qouter
    exact dyadicShortIntervalLength_pos hDouterPos hbudget
  have hqinner : 0 < qinner := by
    unfold qinner
    exact dyadicShortIntervalLength_pos hDinnerPos hbudget
  have hKouter : K = (((2 ^ sk.1) + sk.2 * qouter : ℕ) : ℝ) := by rfl
  have hlogOne : (1 : ℝ) ≤ Real.log Bcap := by linarith
  have hF : 1 ≤ reciprocalPhaseScale N M 2 (K * B) := by
    have hpowOne : (1 : ℝ) ≤ (Real.log Bcap) ^ d :=
      Real.one_le_rpow hlogOne hd
    exact hpowOne.trans (by simpa only [K, B] using hFhigh)
  have hB : 0 < B := by unfold B; positivity
  have hBsum : B ≤ 2 * ((2 ^ tl.1 : ℕ) : ℝ) := by
    unfold B
    norm_num
  have hS₁ : (((2 * 2 ^ tl.1 : ℕ) : ℝ)) ≤ B := by rfl
  have hqinnerNat : qinner ≤ 2 * 2 ^ tl.1 := by
    have hraw := dyadicShortIntervalLength_le_div_add_one
      (2 ^ tl.1) hbudget
    unfold qinner
    have hdiv : 2 ^ tl.1 / vaughanShortIntervalBudget Bcap ≤ 2 ^ tl.1 :=
      Nat.div_le_self _ _
    omega
  have hqinnerB : (qinner : ℝ) ≤ B := by
    unfold B
    exact_mod_cast hqinnerNat
  have hDouterK : ((2 ^ sk.1 : ℕ) : ℝ) ≤ K := by
    rw [hKouter]
    exact_mod_cast Nat.le_add_right (2 ^ sk.1) (sk.2 * qouter)
  have hKbudget : 4 * (240 * ((((5 + 2) ^ 5 : ℕ) : ℝ))) ≤ K :=
    hbudgetLarge.trans (hDouter.trans hDouterK)
  have hfive := five_mul_vaughanShortIntervalLength_cast_le
    hBcap hlog hDouter
  have hqouterK : 5 * (qouter : ℝ) ≤ K := by
    have hfiveQ : 5 * (qouter : ℝ) ≤ ((2 ^ sk.1 : ℕ) : ℝ) := by
      simpa only [qouter] using hfive
    exact hfiveQ.trans hDouterK
  have hhigh' : ∀ n ∈ shortIntervalBlock
        (2 ^ tl.1) (2 * 2 ^ tl.1) qinner tl.2,
      ∀ n' ∈ shortIntervalBlock
          (2 ^ tl.1) (2 * 2 ^ tl.1) qinner tl.2, n ≠ n' →
        3 ≤ (Nat.dist n' n : ℝ) *
          reciprocalPhaseScale N M 2 (K * B) / B →
        K ^ 4 < reciprocalPhaseScale
          (typeIICorrelationLinearParameter N n n')
          (typeIICorrelationHigherParameter M 2 n n') 2 K →
        let F := reciprocalPhaseScale N M 2 (K * B)
        let Q := ((370 * orders.card + 173 : ℕ) : ℝ) *
          (480 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
            (((((5 + 2) ^ 5 : ℕ) : ℝ)) + 1) *
              (1 + Real.log (qouter : ℝ)) * K)
        ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
            (shortIntervalBlock (2 ^ sk.1) (2 * 2 ^ sk.1) qouter sk.2)
            N M 2 n n'‖ ≤
          Q * (4 * typeIIDecayKernel B F (1 / 1024 : ℝ) (Nat.dist n' n) + V) := by
    simpa only [dyadicShortIntervalIndexedBlock, qouter, qinner, K, B] using hhigh
  have hresult :=
    sum_typeIIProductRestrictedInnerSum_shortIntervalDoubleBlock_norm_sq_le_weylVinogradov_quadratic_intrinsicError_unequal
      a b γ N M orders (2 ^ sk.1) (2 * 2 ^ sk.1) (2 ^ tl.1) (2 * 2 ^ tl.1)
      qouter qinner sk.2 tl.2 hDouterPos hDinnerPos hqouter hqinner hL hγ hM
      hKouter hB hBsum hS₁ hqinnerB (by simpa only [K, B] using hF)
      hrFive hrSix hKbudget hqouterK hV hhigh'
  simpa only [dyadicShortIntervalIndexedBlock, qouter, qinner, K, B] using hresult

/-- The complete unequal-parameter conditional estimate for one canonical
Vaughan Type II inner double block. -/
theorem eventually_sum_typeIIProductRestrictedInnerSum_vaughanDoubleBlock_norm_sq_le_sourceVinogradov_unequal
    (hVinogradov : VinogradovExponentialSumEstimate)
    {A A₀ c ε T : ℝ} (hA : 1 / 4 ≤ A) (hA₀ : 0 < A₀) (hc : 0 < c)
    (hε : 0 < ε) (ha : 0 ≤ 3 / 2 - ε) (hAT : T + 2 ≤ 3 * A) :
    ∀ᶠ P : ℝ in Filter.atTop,
      ∀ (a b Bcap : ℕ) (γ : ℕ → ℂ) (N M : ℝ) (orders : Finset ℕ)
        (sk tl : ℕ × ℕ) (L d : ℝ),
        0 < Bcap → 2 ≤ Real.log Bcap →
        (vaughanShortIntervalBudget Bcap : ℝ) ≤ (2 ^ sk.1 : ℕ) →
        0 ≤ L → (∀ n, ‖γ n‖ ≤ L) → M ≠ 0 →
        5 ∈ orders → 6 ∈ orders → 0 ≤ d →
        (Real.log Bcap) ^ d ≤ reciprocalPhaseScale N M 2
          (((dyadicShortIntervalLeftEndpoint
              (vaughanShortIntervalBudget Bcap) sk : ℕ) : ℝ) *
            ((2 * 2 ^ tl.1 : ℕ) : ℝ)) →
        |N| ≤ A₀ * Real.exp ((Real.log P) ^ (3 / 2 - ε)) →
        |M| ≤ A₀ * Real.exp ((Real.log P) ^ (3 / 2 - ε)) →
        c * Real.log P ≤ Real.log
          ((dyadicShortIntervalLeftEndpoint
            (vaughanShortIntervalBudget Bcap) sk : ℕ) : ℝ) →
        let qouter := dyadicShortIntervalLength (2 ^ sk.1)
          (vaughanShortIntervalBudget Bcap)
        let qinner := dyadicShortIntervalLength (2 ^ tl.1)
          (vaughanShortIntervalBudget Bcap)
        let K : ℝ := (dyadicShortIntervalLeftEndpoint
          (vaughanShortIntervalBudget Bcap) sk : ℕ)
        let B : ℝ := (2 * 2 ^ tl.1 : ℕ)
        let F := reciprocalPhaseScale N M 2 (K * B)
        let Q := ((370 * orders.card + 173 : ℕ) : ℝ) *
          (480 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
            (((((5 + 2) ^ 5 : ℕ) : ℝ)) + 1) *
              (1 + Real.log (qouter : ℝ)) * K)
        ∑ m ∈ dyadicShortIntervalIndexedBlock
              (vaughanShortIntervalBudget Bcap) sk,
            ‖typeIIProductRestrictedInnerSum (Finset.Ico a b)
              (dyadicShortIntervalIndexedBlock
                (vaughanShortIntervalBudget Bcap) tl)
              γ N M 2 m‖ ^ 2 ≤
          (qouter : ℝ) * (qinner : ℝ) * L ^ 2 +
            L ^ 2 * ((qinner : ℝ) *
              (Q * (4 *
                  (2 * ((2 ^ (1 - (1 / 1024 : ℝ)) /
                    (1 - (1 / 1024 : ℝ))) * B *
                      F ^ (-(1 / 1024 : ℝ)))) +
                (qinner : ℝ) * ((1 / K) ^ (1 / 1024 : ℝ) +
                  3 * (Real.log P) ^ (-T))))) := by
  have hcallback :=
    eventually_norm_typeIIProductRestrictedCorrelationSum_le_sourceVinogradov_vaughanInnerBlockCallback_unequal
      hVinogradov hA hA₀ hc hε ha hAT
  filter_upwards [hcallback,
    Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop (1 : ℝ))]
      with P hcallbackP hlogP
  intro a b Bcap γ N M orders sk tl L d hBcap hlog hDouter hL hγ hM
    hrFive hrSix hd hFhigh hNupper hMupper hKlower
  let qouter := dyadicShortIntervalLength (2 ^ sk.1)
    (vaughanShortIntervalBudget Bcap)
  let qinner := dyadicShortIntervalLength (2 ^ tl.1)
    (vaughanShortIntervalBudget Bcap)
  let K : ℝ := (dyadicShortIntervalLeftEndpoint
    (vaughanShortIntervalBudget Bcap) sk : ℕ)
  let B : ℝ := (2 * 2 ^ tl.1 : ℕ)
  let F := reciprocalPhaseScale N M 2 (K * B)
  have hbudget : 0 < vaughanShortIntervalBudget Bcap :=
    vaughanShortIntervalBudget_pos Bcap
  have hbudgetLarge : 4 * (240 * ((((5 + 2) ^ 5 : ℕ) : ℝ))) ≤
      (vaughanShortIntervalBudget Bcap : ℝ) :=
    four_mul_quadraticWeylCoefficient_le_vaughanShortIntervalBudget hBcap hlog
  have hDouterPos : 0 < 2 ^ sk.1 := pow_pos (by omega) sk.1
  have hDinnerPos : 0 < 2 ^ tl.1 := pow_pos (by omega) tl.1
  have hqouter : 0 < qouter := by
    unfold qouter
    exact dyadicShortIntervalLength_pos hDouterPos hbudget
  have hqinner : 0 < qinner := by
    unfold qinner
    exact dyadicShortIntervalLength_pos hDinnerPos hbudget
  have hKouter : K = (((2 ^ sk.1) + sk.2 * qouter : ℕ) : ℝ) := by rfl
  have hDouterK : ((2 ^ sk.1 : ℕ) : ℝ) ≤ K := by
    rw [hKouter]
    exact_mod_cast Nat.le_add_right (2 ^ sk.1) (sk.2 * qouter)
  have hKbudget : 4 * (240 * ((((5 + 2) ^ 5 : ℕ) : ℝ))) ≤ K :=
    hbudgetLarge.trans (hDouter.trans hDouterK)
  have hK : (2 : ℝ) ≤ K :=
    (by norm_num : (2 : ℝ) ≤ 4 * (240 * ((((5 + 2) ^ 5 : ℕ) : ℝ)))).trans
      hKbudget
  have hfive := five_mul_vaughanShortIntervalLength_cast_le
    hBcap hlog hDouter
  have hqouterK : (qouter : ℝ) ≤ K := by
    have hfiveQ : 5 * (qouter : ℝ) ≤ ((2 ^ sk.1 : ℕ) : ℝ) := by
      simpa only [qouter] using hfive
    linarith
  have hB : 0 < B := by unfold B; positivity
  have hlogOne : (1 : ℝ) ≤ Real.log Bcap := by linarith
  have hFone : 1 ≤ F := by
    have hpowOne : (1 : ℝ) ≤ (Real.log Bcap) ^ d :=
      Real.one_le_rpow hlogOne hd
    exact hpowOne.trans (by simpa only [F, K, B] using hFhigh)
  have hV : 0 ≤ 3 * (Real.log P) ^ (-T) := by positivity
  have hhigh :
      let qouter := dyadicShortIntervalLength (2 ^ sk.1)
        (vaughanShortIntervalBudget Bcap)
      let K : ℝ := (dyadicShortIntervalLeftEndpoint
        (vaughanShortIntervalBudget Bcap) sk : ℕ)
      let B : ℝ := (2 * 2 ^ tl.1 : ℕ)
      ∀ n ∈ dyadicShortIntervalIndexedBlock
          (vaughanShortIntervalBudget Bcap) tl,
        ∀ n' ∈ dyadicShortIntervalIndexedBlock
            (vaughanShortIntervalBudget Bcap) tl, n ≠ n' →
          3 ≤ (Nat.dist n' n : ℝ) *
            reciprocalPhaseScale N M 2 (K * B) / B →
          K ^ 4 < reciprocalPhaseScale
            (typeIICorrelationLinearParameter N n n')
            (typeIICorrelationHigherParameter M 2 n n') 2 K →
          let F := reciprocalPhaseScale N M 2 (K * B)
          let Q := ((370 * orders.card + 173 : ℕ) : ℝ) *
            (480 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
              (((((5 + 2) ^ 5 : ℕ) : ℝ)) + 1) *
                (1 + Real.log (qouter : ℝ)) * K)
          ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
              (dyadicShortIntervalIndexedBlock
                (vaughanShortIntervalBudget Bcap) sk)
              N M 2 n n'‖ ≤
            Q * (4 * typeIIDecayKernel B F (1 / 1024 : ℝ) (Nat.dist n' n) +
              3 * (Real.log P) ^ (-T)) := by
    dsimp only
    intro n hnBlock n' hn'Block hne _ hpairHigh
    have hnShort : n ∈ shortIntervalBlock
        (2 ^ tl.1) (2 * 2 ^ tl.1) qinner tl.2 := by
      simpa only [dyadicShortIntervalIndexedBlock, qinner] using hnBlock
    have hn'Short : n' ∈ shortIntervalBlock
        (2 ^ tl.1) (2 * 2 ^ tl.1) qinner tl.2 := by
      simpa only [dyadicShortIntervalIndexedBlock, qinner] using hn'Block
    have hnData := mem_shortIntervalBlock.mp hnShort
    have hn'Data := mem_shortIntervalBlock.mp hn'Short
    have hnpos : 0 < n := by omega
    have hn'pos : 0 < n' := by omega
    have hraw := hcallbackP a b Bcap (2 ^ sk.1) (2 * 2 ^ sk.1) qouter
      sk.2 N M K n n' orders B F tl hKouter hK hqouter hqouterK hnBlock
        hn'Block hnpos hn'pos hne hM hB (zero_le_one.trans hFone) hNupper
        hMupper (by simpa only [K] using hKlower) hpairHigh.le
    simpa only [dyadicShortIntervalIndexedBlock, qouter, K, B, F] using hraw
  have hresult :=
    sum_typeIIProductRestrictedInnerSum_vaughanDoubleBlock_norm_sq_le_weylVinogradov_quadratic_intrinsicError_unequal
      a b Bcap γ N M orders sk tl hBcap hlog hDouter hL hγ hM hrFive hrSix hd
        hFhigh hV hhigh
  simpa only [qouter, qinner, K, B, F] using hresult

/-- Complete conditional estimate for one actual source Vaughan Type II double
block with independent linear and quadratic phase parameters. -/
theorem eventually_norm_weightedConvolutionProductVaughanTypeIIDoubleBlockSum_sq_le_sourceVinogradov_unequal
    (hVinogradov : VinogradovExponentialSumEstimate)
    {A A₀ c ε T : ℝ} (hA : 1 / 4 ≤ A) (hA₀ : 0 < A₀) (hc : 0 < c)
    (hε : 0 < ε) (ha : 0 ≤ 3 / 2 - ε) (hAT : T + 2 ≤ 3 * A) :
    ∀ᶠ P : ℝ in Filter.atTop,
      ∀ (a b U V : ℕ) (N M : ℝ) (orders : Finset ℕ) (sk tl : ℕ × ℕ) (d : ℝ),
        0 < b → 2 ≤ Real.log b →
        sk ∈ vaughanShortIntervalIndexBox b →
        tl ∈ vaughanShortIntervalIndexBox b →
        (vaughanShortIntervalBudget b : ℝ) ≤ (2 ^ sk.1 : ℕ) →
        M ≠ 0 → 5 ∈ orders → 6 ∈ orders → 0 ≤ d →
        (Real.log b) ^ d ≤ reciprocalPhaseScale N M 2
          (((dyadicShortIntervalLeftEndpoint
              (vaughanShortIntervalBudget b) sk : ℕ) : ℝ) *
            ((2 * 2 ^ tl.1 : ℕ) : ℝ)) →
        |N| ≤ A₀ * Real.exp ((Real.log P) ^ (3 / 2 - ε)) →
        |M| ≤ A₀ * Real.exp ((Real.log P) ^ (3 / 2 - ε)) →
        c * Real.log P ≤ Real.log
          ((dyadicShortIntervalLeftEndpoint
            (vaughanShortIntervalBudget b) sk : ℕ) : ℝ) →
        let qouter := dyadicShortIntervalLength (2 ^ sk.1)
          (vaughanShortIntervalBudget b)
        let qinner := dyadicShortIntervalLength (2 ^ tl.1)
          (vaughanShortIntervalBudget b)
        let K : ℝ := (dyadicShortIntervalLeftEndpoint
          (vaughanShortIntervalBudget b) sk : ℕ)
        let B : ℝ := (2 * 2 ^ tl.1 : ℕ)
        let F := reciprocalPhaseScale N M 2 (K * B)
        let Q := ((370 * orders.card + 173 : ℕ) : ℝ) *
          (480 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
            (((((5 + 2) ^ 5 : ℕ) : ℝ)) + 1) *
              (1 + Real.log (qouter : ℝ)) * K)
        ‖weightedConvolutionProductVaughanDoubleBlockSum
            (Finset.Ico a b) b sk tl
            (fun n => standardAdditiveCharacter (reciprocalPhase N M 2 n))
            (vaughanTypeIIBetaCoefficient U)
            (vaughanTypeIIGammaCoefficient V)‖ ^ 2 ≤
          ((dyadicShortIntervalIndexedBlock
              (vaughanShortIntervalBudget b) sk).card : ℝ) *
            ((qouter : ℝ) * (qinner : ℝ) * (Real.log (2 * b)) ^ 2 +
              (Real.log (2 * b)) ^ 2 * ((qinner : ℝ) *
                (Q * (4 *
                    (2 * ((2 ^ (1 - (1 / 1024 : ℝ)) /
                      (1 - (1 / 1024 : ℝ))) * B *
                        F ^ (-(1 / 1024 : ℝ)))) +
                  (qinner : ℝ) * ((1 / K) ^ (1 / 1024 : ℝ) +
                    3 * (Real.log P) ^ (-T)))))) := by
  have hinner :=
    eventually_sum_typeIIProductRestrictedInnerSum_vaughanDoubleBlock_norm_sq_le_sourceVinogradov_unequal
      hVinogradov hA hA₀ hc hε ha hAT
  filter_upwards [hinner] with P hinnerP
  intro a b U V N M orders sk tl d hb hlog hsk htl hDouter hM
    hrFive hrSix hd hFhigh hNupper hMupper hKlower
  let γ : ℕ → ℂ := vaughanShortIntervalCoefficient
    (fun n => (vaughanTypeIIGammaCoefficient V n : ℂ)) b tl
  let L : ℝ := Real.log (2 * b)
  have hL : 0 ≤ L := by
    unfold L
    apply Real.log_nonneg
    exact_mod_cast (by omega : 1 ≤ 2 * b)
  have hγ : ∀ n, ‖γ n‖ ≤ L := by
    intro n
    exact norm_vaughanShortIntervalTypeIIGammaCoefficient_le_log_two_mul
      V b hb htl n
  have hinnerBound := hinnerP a b b γ N M orders sk tl L d hb hlog hDouter
    hL hγ hM hrFive hrSix hd hFhigh hNupper hMupper hKlower
  have hI : ∀ x ∈ Finset.Ico a b, x ≤ b := by
    intro x hx
    rw [Finset.mem_Ico] at hx
    omega
  have hbridge :=
    norm_weightedConvolutionProductVaughanTypeIIDoubleBlockSum_sq_le
      (Finset.Ico a b) b U V sk tl N M 2 hI
  exact hbridge.trans (mul_le_mul_of_nonneg_left
    (by simpa only [γ, L] using hinnerBound) (Nat.cast_nonneg _))

end

end Tao2026
