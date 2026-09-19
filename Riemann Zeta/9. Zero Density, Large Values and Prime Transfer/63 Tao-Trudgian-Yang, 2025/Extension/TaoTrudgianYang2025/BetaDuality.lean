import TaoTrudgianYang2025.ExponentPair

/-!
# Exponent-pair to beta duality

This module begins the two-way duality proof at the actual ANTEDB
`exponentSumGrowthExponent`. The theorem here proves the analytic forward
direction on `0 ≤ α < 1`. The remaining endpoint and converse are kept as
separate obligations.
-/

open Filter Topology
open scoped Expdb NNReal

noncomputable section

namespace TaoTrudgianYang2025

open Expdb

/-- The affine line associated to an exponent-pair candidate. -/
def exponentPairLine (k l α : ℝ) : ℝ :=
  k + (l - k) * α

/-- An analytic exponent pair bounds ANTEDB's exponential-sum growth exponent
by its associated affine line throughout the half-open beta range. -/
theorem exponentSumGrowthExponent_le_exponentPairLine
    {k l : ℝ} (hkl : ExponentPair k l) (α : ℝ≥0)
    (hα : (α : ℝ) < 1) :
    exponentSumGrowthExponent α ≤ exponentPairLine k l α := by
  rw [exponentSumGrowthExponent_le_iff]
  intro N T F a b hN hT hTunbounded hNT hF hab
  have htriangle := hkl.inTriangle
  have hdiffNonneg : 0 ≤ l - k := by
    dsimp [InExponentPairTriangle] at htriangle
    linarith
  have hdiffLeOne : l - k ≤ 1 := by
    dsimp [InExponentPairTriangle] at htriangle
    linarith
  let margin : ℝ := (1 - (α : ℝ)) / 2
  have hmargin : 0 < margin := by
    dsimp [margin]
    linarith
  have hNleT : ∀ᶠ i in atTop, N i ≤ T i := by
    have hbetween :=
      hNT.eventually_between (Filter.Eventually.of_forall hT) hmargin
    filter_upwards [hbetween] with i hi
    calc
      N i ≤ T i ^ ((α : ℝ) + margin) := hi.2
      _ ≤ T i ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (hT i) (by
          dsimp [margin]
          linarith)
      _ = T i := Real.rpow_one _
  apply (isPowerBounded_iff_forall_pos
    (exponentialSum F T N a b) T (exponentPairLine k l α)
    hT hTunbounded).2
  intro ε hε
  let η : ℝ := ε / 3
  have hη : 0 < η := by
    dsimp [η]
    linarith
  have hbetween :=
    hNT.eventually_between (Filter.Eventually.of_forall hT) hη
  have hpair :=
    hkl.estimate N T F a b hN hNleT hTunbounded hF hab η hη
  refine hpair.trans (Asymptotics.IsBigO.of_bound 1 ?_)
  filter_upwards [hbetween] with i hiN
  have hTpos : 0 < T i := zero_lt_one.trans_le (hT i)
  have hTnonneg : 0 ≤ T i := hTpos.le
  have hNpos : 0 < N i := zero_lt_one.trans_le (hN i)
  have hNnonneg : 0 ≤ N i := hNpos.le
  have hratioNonneg : 0 ≤ T i / N i := div_nonneg hTnonneg hNnonneg
  have hrearrange :
      (T i / N i) ^ (k + η) * N i ^ (l + η) =
        T i ^ (k + η) * N i ^ (l - k) := by
    rw [Real.div_rpow hTnonneg hNnonneg, div_mul_eq_mul_div, mul_div_assoc,
      ← Real.rpow_sub hNpos]
    congr 2
    ring
  have hNpower :
      N i ^ (l - k) ≤ T i ^ (((α : ℝ) + η) * (l - k)) := by
    calc
      N i ^ (l - k) ≤ (T i ^ ((α : ℝ) + η)) ^ (l - k) :=
        Real.rpow_le_rpow hNnonneg hiN.2 hdiffNonneg
      _ = T i ^ (((α : ℝ) + η) * (l - k)) :=
        (Real.rpow_mul hTnonneg ((α : ℝ) + η) (l - k)).symm
  have hεdiff : 0 ≤ ε * (1 - (l - k)) :=
    mul_nonneg hε.le (sub_nonneg.mpr hdiffLeOne)
  rw [one_mul, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hratioNonneg _)
      (Real.rpow_nonneg hNnonneg _)),
    Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hTnonneg _), hrearrange]
  calc
    T i ^ (k + η) * N i ^ (l - k) ≤
        T i ^ (k + η) * T i ^ (((α : ℝ) + η) * (l - k)) :=
      mul_le_mul_of_nonneg_left hNpower (Real.rpow_nonneg hTnonneg _)
    _ = T i ^ ((k + η) + ((α : ℝ) + η) * (l - k)) :=
      (Real.rpow_add hTpos (k + η) (((α : ℝ) + η) * (l - k))).symm
    _ ≤ T i ^ (exponentPairLine k l α + ε) :=
      Real.rpow_le_rpow_of_exponent_le (hT i) (by
        dsimp [η, exponentPairLine]
        nlinarith)

end TaoTrudgianYang2025
