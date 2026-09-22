import TaoTrudgianYang2025.BetaDuality
import Mathlib.Topology.Compactness.Compact
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Compact uniformity in beta/exponent-pair duality

Pointwise beta bounds on the full closed scale interval yield one uniform
exponent-pair estimate. The finite subcover is applied to the physical
scale log_T N, so neither the scale nor the analytic estimate is assumed
to have already been made uniform.
-/

noncomputable section

open Set
open Expdb
open scoped NNReal

namespace TaoTrudgianYang2025

theorem approximateModelPhase_mono {F : ℝ → ℝ} {σ δ₀ δ₁ : ℝ} {P₀ P₁ : ℕ}
    (h : IsApproximateModelPhaseFunction F σ P₁ δ₀)
    (hP : P₀ ≤ P₁) (hδ : δ₀ ≤ δ₁) :
    IsApproximateModelPhaseFunction F σ P₀ δ₁ := by
  refine ⟨h.1, ?_⟩
  intro p hp u
  exact (h.2 p (hp.trans hP) u).trans hδ

theorem exponentPair_rhs_eq_logb_power {T N : ℝ}
    (hT : 1 < T) (hN : 0 < N) (k l ε : ℝ) :
    (T/N)^(k+ε)*N^(l+ε) =
      T^(exponentPairLine k l (Real.logb T N)+ε) := by
  have hTpos : 0 < T := zero_lt_one.trans hT
  rw [Real.div_rpow hTpos.le hN.le, div_mul_eq_mul_div, mul_div_assoc,
    ← Real.rpow_sub hN]
  have hdiff : l+ε-(k+ε) = l-k := by ring
  rw [hdiff]
  calc
    T^(k+ε)*N^(l-k) =
        T^(k+ε)*(T^(Real.logb T N))^(l-k) := by
      rw [Real.rpow_logb hTpos hT.ne' hN]
    _ = T^((k+ε)+Real.logb T N*(l-k)) := by
      rw [← Real.rpow_mul hTpos.le, ← Real.rpow_add hTpos]
    _ = _ := by congr 1; unfold exponentPairLine; ring

/-- One uniform fixed-parameter estimate follows from beta bounds at every
scale in [0,1]. The phase exponent and epsilon precede every constant. -/
theorem isExponentPairEstimateNonAsymptotic_of_beta_bound
    {k l : ℝ} (htri : InExponentPairTriangle k l)
    (hβ : ∀ α : ℝ≥0, (α : ℝ) ≤ 1 →
      exponentSumGrowthExponent α ≤ exponentPairLine k l α) :
    IsExponentPairEstimateNonAsymptotic k l := by
  classical
  intro ε hε σ hσ
  have hlocal (α : Icc (0 : ℝ) 1) :
      ∃ δ : ℝ, 0 < δ ∧ ∃ P : ℕ, 1 ≤ P ∧ ∃ C : ℝ, 1 ≤ C ∧
        ∀ (T N : ℝ) (F : ℝ → ℝ) (a b : ℕ),
          IsModelPhaseSumSetupAt α σ δ P C T N F a b →
          ‖exponentialSumAt F T N a b‖ ≤ C*T^(exponentPairLine k l α+ε/2) :=
    (exponentSumGrowthExponent_le_iff_nonAsymptotic.mp
      (hβ ⟨α,α.property.1⟩ α.property.2)) (ε/2) (by linarith) σ hσ
  choose δ hδ P hP C hC hbound using hlocal
  let radius (α : Icc (0 : ℝ) 1) : ℝ := min (δ α) (ε/4)
  have hrad (α : Icc (0 : ℝ) 1) : 0 < radius α :=
    lt_min (hδ α) (by positivity)
  let U (α : Icc (0 : ℝ) 1) : Set ℝ := Ioo (α-radius α) (α+radius α)
  have hcover : Icc (0 : ℝ) 1 ⊆ ⋃ α, U α := by
    intro x hx
    refine mem_iUnion.mpr ⟨⟨x,hx⟩, ?_⟩
    have := hrad ⟨x,hx⟩
    change x-radius ⟨x,hx⟩ < x ∧ x < x+radius ⟨x,hx⟩
    constructor <;> linarith
  obtain ⟨s,hs⟩ := isCompact_Icc.elim_finite_subcover U (fun _ => isOpen_Ioo) hcover
  have hsne : s.Nonempty := by
    have hz := hs (show (0 : ℝ) ∈ Icc 0 1 by norm_num)
    obtain ⟨α,hα,_⟩ := mem_iUnion₂.mp hz
    exact ⟨α,hα⟩
  let δall : ℝ := s.inf' hsne δ
  let Pall : ℕ := max 1 (s.sup P)
  let Call : ℝ := max 2 (s.sup' hsne C)
  have hδall : 0 < δall := by
    exact (Finset.lt_inf'_iff hsne).2 (fun α _ => hδ α)
  have hPall : 1 ≤ Pall := le_max_left _ _
  have hCall : 1 ≤ Call := le_trans (by norm_num) (le_max_left _ _)
  refine ⟨δall,hδall,Pall,hPall,Call,hCall,?_⟩
  intro T N F a b hsetup
  have hT : 1 < T := lt_of_lt_of_le
    (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (le_max_left _ _))
    hsetup.threshold_le_param
  have hN : 0 < N := zero_lt_one.trans_le hsetup.one_le_scale
  have hz : Real.logb T N ∈ Icc (0 : ℝ) 1 := by
    refine ⟨Real.logb_nonneg hT hsetup.one_le_scale, ?_⟩
    apply (Real.logb_le_iff_le_rpow hT hN).2
    simpa only [Real.rpow_one] using hsetup.scale_le_param
  obtain ⟨α,hα,hu⟩ := mem_iUnion₂.mp (hs hz)
  change (α : ℝ)-radius α < Real.logb T N ∧
    Real.logb T N < (α : ℝ)+radius α at hu
  have hδle : δall ≤ δ α := Finset.inf'_le δ hα
  have hPle : P α ≤ Pall := (Finset.le_sup hα).trans (le_max_right _ _)
  have hCle : C α ≤ Call := (Finset.le_sup' C hα).trans (le_max_right _ _)
  have hrδ : radius α ≤ δ α := min_le_left _ _
  have hrε : radius α ≤ ε/4 := min_le_right _ _
  have hpoint := hbound α T N F a b
    ⟨hCle.trans hsetup.threshold_le_param,
      (Real.le_logb_iff_rpow_le hT hN).1 (by linarith),
      (Real.logb_le_iff_le_rpow hT hN).1 (by linarith),
      approximateModelPhase_mono hsetup.isApproximateModelPhase hPle hδle,
      hsetup.scale_le_start,hsetup.end_le_two_mul_scale⟩
  have hd : 0 ≤ l-k := by
    rcases htri with ⟨hk₀,hk₁,hl₀,hl₁,hkl⟩
    linarith
  have hdhi : l-k ≤ 1 := by
    rcases htri with ⟨hk₀,hk₁,hl₀,hl₁,hkl⟩
    linarith
  have hexp : exponentPairLine k l α+ε/2 ≤
      exponentPairLine k l (Real.logb T N)+ε := by
    unfold exponentPairLine
    nlinarith [mul_nonneg hd
      (by linarith : 0 ≤ Real.logb T N+ε/4-(α : ℝ))]
  calc
    ‖exponentialSumAt F T N a b‖ ≤ C α*T^(exponentPairLine k l α+ε/2) := hpoint
    _ ≤ Call*T^(exponentPairLine k l (Real.logb T N)+ε) :=
      mul_le_mul hCle (Real.rpow_le_rpow_of_exponent_le hT.le hexp)
        (Real.rpow_nonneg (zero_lt_one.trans hT).le _) (zero_le_one.trans hCall)
    _ = Call*(T/N)^(k+ε)*N^(l+ε) := by
      rw [← exponentPair_rhs_eq_logb_power hT hN]
      ring

/-- The full converse in the source beta-duality lemma, including both
scale endpoints and the uniform constants in the exponent-pair definition. -/
theorem exponentPair_of_beta_bound {k l : ℝ} (htri : InExponentPairTriangle k l)
    (hβ : ∀ α : ℝ≥0, (α : ℝ) ≤ 1 →
      exponentSumGrowthExponent α ≤ exponentPairLine k l α) :
    ExponentPair k l :=
  ⟨htri,isExponentPairEstimate_iff_nonAsymptotic.mpr
    (isExponentPairEstimateNonAsymptotic_of_beta_bound htri hβ)⟩

end TaoTrudgianYang2025
