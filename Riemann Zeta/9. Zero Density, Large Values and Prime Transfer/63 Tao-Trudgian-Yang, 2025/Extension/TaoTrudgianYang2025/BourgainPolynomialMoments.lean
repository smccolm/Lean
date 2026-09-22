import TaoTrudgianYang2025.BourgainWeightedMoments

/-!
# Actual polynomial powers with retained zeta-square moments

The finite convolution and dyadic decomposition are the existing exact
source-polynomial identities. Uniform factorization bounds and the
retained native weighted moment are consumed at their actual scales.
-/

open Complex Finset
open RiemannZeta.GuthMaynard

noncomputable section

namespace TaoTrudgianYang2025

/-- For every positive power, the literal powered source polynomial has
a retained-zeta bound. The factor U is the required unweighted-to-critical
conversion; it is not dropped or absorbed into a scale-dependent constant. -/
theorem bourgain_source_power_moment_retained (k : ℕ) (hk : 0 < k)
    {q : ℕ} (hq : 0 < q) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ) (T H : ℝ) (W : Finset ℝ) (a : ℕ → ℂ),
        0 < N → 0 ≤ T → 0 ≤ H → IsSeparated 1 W → InBaseInterval T W →
        (∀ n ∈ dyadicInterval N, ‖a n‖ ≤ 1) →
        (∑ t ∈ W, ∑ v ∈ W, ‖sourceDirichletPoly N a (t-v)‖^(2*k)) ≤
          C*(2^k*N^k : ℕ)*(((2^k*N^k : ℕ) : ℝ)^η)^2 *
            bourgainMomentBudget q (2^k*N^k : ℕ) T H W := by
  obtain ⟨D,hD,hcoeff⟩ := finitePowCoeff_bound_uniform k η hη
  obtain ⟨A,hA,hmoment⟩ := bourgain_heathBrownWeightedMoment_retained hq
  let C : ℝ := (k : ℝ)^2*2*D^2*A
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro N T H W a hN hT hH hsep hbase ha
  let U : ℕ := 2^k*N^k
  let B : ℝ := bourgainMomentBudget q U T H W
  have hB : 0 ≤ B := bourgainMomentBudget_nonneg q W (Nat.cast_nonneg U) hH
  have hblock (r : ℕ) (hr : r ∈ Finset.range k) :
      (∑ t ∈ W, ∑ v ∈ W,
        ‖sourceDirichletPoly (2^r*N^k) (finitePoweredLineCoeffs N k a 0) (t-v)‖^2) ≤
        (D*(U : ℝ)^η)^2*(2*(U : ℝ))*(A*B) := by
    have hrk := Finset.mem_range.mp hr
    have hQ : 0 < 2^r*N^k := by positivity
    have hQU : 2^r*N^k ≤ U :=
      Nat.mul_le_mul_right _ (pow_le_pow_right₀ (by omega) hrk.le)
    have hQUr : ((2^r*N^k : ℕ) : ℝ) ≤ U := by exact_mod_cast hQU
    have hcoef : ∀ m ∈ dyadicInterval (2^r*N^k),
        ‖finitePoweredLineCoeffs N k a 0 m‖ ≤ D*(U : ℝ)^η := by
      intro m hm
      have hsupport := heathBrown_poweredBlock_subset N k r m hrk hm
      have hmpos : 0 < m := lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hm).1
      exact (norm_finitePoweredLineCoeffs_le N k m a 0 hN le_rfl hsupport).trans
        ((hcoeff N a ha m hmpos).trans (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Nat.cast_nonneg m)
            (by exact_mod_cast (Finset.mem_Ioc.mp hsupport).2) hη.le) hD.le))
    have hc := jutila_coefficient_moment_le (2^r*N^k) W
      (finitePoweredLineCoeffs N k a 0) (by positivity) hcoef
    have hm := hmoment (2^r*N^k) T H W hQ hT hH hsep hbase
    have hm' : heathBrownWeightedMoment (2^r*N^k) W ≤ A*B :=
      hm.trans (mul_le_mul_of_nonneg_left
        (bourgainMomentBudget_mono_scale q hQUr T H W) hA.le)
    calc
      _ ≤ (D*(U : ℝ)^η)^2*(2*((2^r*N^k : ℕ) : ℝ))*
          heathBrownWeightedMoment (2^r*N^k) W := hc
      _ ≤ (D*(U : ℝ)^η)^2*(2*((2^r*N^k : ℕ) : ℝ))*(A*B) :=
        mul_le_mul_of_nonneg_left hm' (by positivity)
      _ ≤ _ := by gcongr
  have hwide := jutila_source_power_moment_le_blocks N k W a hN hk
  have hsum := Finset.sum_le_sum hblock
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hsum
  have hfinal := hwide.trans (mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg k))
  convert hfinal using 1
  dsimp [C,B,U]
  ring

end TaoTrudgianYang2025
