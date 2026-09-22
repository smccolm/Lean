import TaoTrudgianYang2025.BetaCoherentWindow
import TaoTrudgianYang2025.PointMeanLemmaThreeEdges

/-!
# Physical power witnesses for the beta lower bound

An integer source length N and T=N^(1/alpha) give an exact power scale.
For alpha<1, rounding the linear frequency changes the model phase by
less than any prescribed tolerance at sufficiently large T.
-/

noncomputable section

open Expdb Filter
open scoped Topology

namespace TaoTrudgianYang2025

theorem exists_twistedLog_power_witness {α δ : ℝ}
    (hα : 0 < α) (hαone : α < 1) (hδ : 0 < δ) (B : ℝ) :
    ∃ (T : ℝ) (N : ℕ), 1 ≤ T ∧ B ≤ T ∧ 1 ≤ N ∧
      T^α = (N : ℝ) ∧
      ((N+betaCoherentLength T N : ℕ) : ℝ) ≤ 2*(N : ℝ) ∧
      (∀ P : ℕ, IsApproximateModelPhaseFunction
        (twistedLogPhase (betaResonantCorrection T N)) 1 P δ) ∧
      T^(α-1/2)/8 ≤
        ‖exponentialSumAt (twistedLogPhase (betaResonantCorrection T N)) T N
          N (N+betaCoherentLength T N)‖ := by
  obtain ⟨M,hM⟩ := eventually_atTop.1
    (eventually_const_mul_rpow_le_rpow (D := δ⁻¹) (a := α) (b := 1) hαone)
  have htop : Tendsto (fun n : ℕ => (n : ℝ)^(α⁻¹)) atTop atTop :=
    (tendsto_rpow_atTop (inv_pos.mpr hα)).comp tendsto_natCast_atTop_atTop
  have hlarge : ∀ᶠ n : ℕ in atTop, max 1 (max B M) ≤ (n : ℝ)^(α⁻¹) :=
    htop.eventually (eventually_ge_atTop _)
  obtain ⟨n,hnlarge,hn⟩ := (hlarge.and (eventually_ge_atTop (1 : ℕ))).exists
  let T := (n : ℝ)^(α⁻¹)
  have hT : 1 ≤ T := (le_max_left _ _).trans hnlarge
  have hTB : B ≤ T := ((le_max_left _ _).trans (le_max_right _ _)).trans hnlarge
  have hTM : M ≤ T := ((le_max_right _ _).trans (le_max_right _ _)).trans hnlarge
  have hTp : 0 < T := zero_lt_one.trans_le hT
  have hNp : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hscale : T^α = (n : ℝ) := by
    dsimp [T]
    rw [← Real.rpow_mul hNp.le,inv_mul_cancel₀ hα.ne',Real.rpow_one]
  have hsmallraw := hM T hTM
  rw [Real.rpow_one,hscale] at hsmallraw
  have hsmall : (n : ℝ)/T ≤ δ := by
    have hh := mul_le_mul_of_nonneg_left hsmallraw hδ.le
    rw [← mul_assoc,mul_inv_cancel₀ hδ.ne',one_mul] at hh
    exact (div_le_iff₀ hTp).mpr (by nlinarith)
  have hfactor : (n : ℝ)/(8*Real.sqrt T) = T^(α-1/2)/8 := by
    rw [← hscale,Real.sqrt_eq_rpow]
    rw [show T^α/(8*T^((1 : ℝ)/2)) = (T^α/T^((1 : ℝ)/2))/8 by ring,
      ← Real.rpow_sub hTp]
  refine ⟨T,n,hT,hTB,hn,hscale,betaCoherentLength_source_end hT n,
    fun P => betaResonantCorrection_model hTp hNp hsmall P,?_⟩
  rw [← hfactor]
  exact norm_twistedLog_coherent_sum_lower hT hn

end TaoTrudgianYang2025
