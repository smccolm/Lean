import TaoTrudgianYang2025.BourgainPairDensity
import TaoTrudgianYang2025.ClassicalSecondDerivativePair

/-! The closed low-k boundary of Bourgain's pair-to-density theorem.
The perturbations are genuine analytic exponent pairs, not triangle certificates. -/

noncomputable section
open Filter Topology
namespace TaoTrudgianYang2025

theorem exponentPair_one_fourteenth_eleven_fourteenths :
    ExponentPair (1/14) (11/14) := by
  convert exponentPair_half_half.aProcess.aProcess using 1 <;> norm_num

/-- Convex perturbation and a genuine limit extend the strict Bourgain
theorem to the two closed low-k faces needed by the optimized table. -/
theorem ExponentPair.bourgain_zero_density_closed_low_k {k l σ : ℝ}
    (hpair : ExponentPair k l)
    (hk : k ≤ 11/85) (hl : 3/5 ≤ l) (hrange : 13 ≤ 15*l+20*k)
    (hline : (l+1)/(2*(k+1)) < σ) (hσ1 : σ ≤ 1) :
    zeroDensityExponent σ ≤ ((4*k/(2*(1+k)*σ-1-l):ℝ):EReal) := by
  have hk0 : 0 ≤ k := hpair.inTriangle.1
  have hden0 : 0 < 2*(k+1) := by linarith
  have hd : 0 < 2*(1+k)*σ-1-l := by
    have h := (div_lt_iff₀ hden0).mp hline
    nlinarith
  let θ : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  let K : ℕ → ℝ := fun n => (1-θ n)*k+θ n*(1/14)
  let L : ℕ → ℝ := fun n => (1-θ n)*l+θ n*(11/14)
  have hθ : ∀ n, 0 < θ n ∧ θ n ≤ 1 := by
    intro n
    dsimp [θ]
    constructor
    · positivity
    · apply (div_le_iff₀ (by positivity : 0 < (n:ℝ)+1)).mpr
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hθlim : Tendsto θ atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hOne : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hKlim : Tendsto K atTop (𝓝 k) := by
    simpa only [sub_zero,one_mul,zero_mul,add_zero] using
      ((hOne.sub hθlim).mul_const k).add (hθlim.mul_const (1/14))
  have hLlim : Tendsto L atTop (𝓝 l) := by
    simpa only [sub_zero,one_mul,zero_mul,add_zero] using
      ((hOne.sub hθlim).mul_const l).add (hθlim.mul_const (11/14))
  have hDlim : Tendsto (fun n => 2*(1+K n)*σ-1-L n)
      atTop (𝓝 (2*(1+k)*σ-1-l)) :=
    (((tendsto_const_nhds.add hKlim).const_mul 2).mul_const σ).sub_const 1 |>.sub hLlim
  have hDpos : ∀ᶠ n in atTop, 0 < 2*(1+K n)*σ-1-L n :=
    hDlim.eventually (lt_mem_nhds hd)
  have hRlim : Tendsto (fun n => ((4*K n/(2*(1+K n)*σ-1-L n):ℝ):EReal))
      atTop (𝓝 ((4*k/(2*(1+k)*σ-1-l):ℝ):EReal)) :=
    EReal.tendsto_coe.mpr ((hKlim.const_mul 4).div hDlim hd.ne')
  apply ge_of_tendsto hRlim
  filter_upwards [hDpos] with n hn
  have ht0 := (hθ n).1
  have ht1 := (hθ n).2
  have hp := hpair.convexCombination exponentPair_one_fourteenth_eleven_fourteenths
    ht0.le ht1
  change ExponentPair (K n) (L n) at hp
  have hK : K n < 11/85 := by
    dsimp [K]
    nlinarith [mul_nonneg (show 0 ≤ 1-θ n by linarith)
      (show 0 ≤ 11/85-k by linarith)]
  have hL : 3/5 < L n := by
    dsimp [L]
    nlinarith only [ht0, mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr hl)]
  have hr : 13 < 15*L n+20*K n := by
    dsimp [K,L]
    nlinarith [mul_nonneg (show 0 ≤ 1-θ n by linarith)
      (show 0 ≤ 15*l+20*k-13 by linarith)]
  have hlineN : (L n+1)/(2*(K n+1)) < σ := by
    have hK0 := hp.inTriangle.1
    apply (div_lt_iff₀ (by linarith : 0 < 2*(K n+1))).mpr
    nlinarith
  exact hp.bourgain_zero_density (by linarith) hL hr hlineN hσ1 (Or.inl hK)

/-- The first optimized rational formula, with its necessary analytic
pair input still explicit. No triangle certificate discharges that input. -/
theorem ExponentPair.bourgain_density_first_piece {σ : ℝ}
    (hpair : ExponentPair (11/85) (59/85))
    (hσ : 3/4 < σ) (hσ1 : σ ≤ 1) :
    zeroDensityExponent σ ≤ ((11/(12*(4*σ-3)):ℝ):EReal) := by
  have h := hpair.bourgain_zero_density_closed_low_k (by norm_num)
    (by norm_num) (by norm_num) (by norm_num; linarith) hσ1
  have he : 4*(11/85)/(2*(1+11/85)*σ-1-59/85) = 11/(12*(4*σ-3)) := by
    apply (div_eq_div_iff (by linarith) (by linarith)).mpr
    ring
  simpa only [he] using h

end TaoTrudgianYang2025
