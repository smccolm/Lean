import Dubon2026.SourceOriginalPathIntegral

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi -> actual periods.
Integration of an original regular differential is additive under path
concatenation and negates under reversal. The original path-primitive
existence and uniqueness theorems discharge all primitive hypotheses.
These laws identify differences between chosen paths with actual loop
periods in the required period-lattice quotient.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_AlgebraicCurve_exists_ball_abelJacobiVec_sub_sub_mem_pathPeriodLattice.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Filter Set KaehlerDifferential
open scoped Topology
variable (N : ℕ) [NeZero N]
attribute [local instance] placeTopology

theorem isPrimitiveAlong_symm {η : Ω[modularFunctionFieldOver N ℂ⁄ℂ]} {P Q : Place ℂ (modularFunctionFieldOver N ℂ)} {γ : Path P Q}
    {g : unitInterval → ℂ} (hg : IsPrimitiveAlong N η γ g) :
    IsPrimitiveAlong N η γ.symm (g ∘ unitInterval.symm) := by
  intro t₀
  obtain ⟨Φ, hΦ, hg'⟩ := hg (unitInterval.symm t₀)
  refine ⟨Φ, ?_, ?_⟩
  · simp only [Path.symm_apply] at hΦ ⊢
    exact hΦ
  · have hc : ContinuousAt unitInterval.symm t₀ := unitInterval.continuous_symm.continuousAt
    filter_upwards [hc.eventually hg'] with t ht
    simpa only [Path.symm_apply, Function.comp_apply] using ht

private def halfL (s : unitInterval) : unitInterval :=
  ⟨(s : ℝ) / 2, unitInterval.div_mem s.2.1 zero_le_two (s.2.2.trans one_le_two)⟩

private def halfR (s : unitInterval) : unitInterval :=
  ⟨((s : ℝ) + 1) / 2, unitInterval.div_mem (by linarith [s.2.1]) zero_le_two
    (by linarith [s.2.2])⟩

private theorem continuous_halfL : Continuous (halfL) :=
  Continuous.subtype_mk (by fun_prop) _

private theorem continuous_halfR : Continuous (halfR) :=
  Continuous.subtype_mk (by fun_prop) _

@[local simp] private theorem coe_halfL (s : unitInterval) : ((halfL s : unitInterval) : ℝ) = s / 2 := rfl
@[local simp] private theorem coe_halfR (s : unitInterval) : ((halfR s : unitInterval) : ℝ) = (s + 1) / 2 :=
  rfl

private theorem trans_halfL {P Q R : Place ℂ (modularFunctionFieldOver N ℂ)} (γ₁ : Path P Q) (γ₂ : Path Q R) (s : unitInterval) :
    (γ₁.trans γ₂) (halfL s) = γ₁ s := by
  rw [Path.trans_apply]
  have h : ((halfL s : unitInterval) : ℝ) ≤ 1 / 2 := by
    rw [coe_halfL]; linarith [s.2.2]
  rw [dif_pos h]
  congr 1
  ext
  simp only [coe_halfL]
  ring

private theorem trans_halfR {P Q R : Place ℂ (modularFunctionFieldOver N ℂ)} (γ₁ : Path P Q) (γ₂ : Path Q R) (s : unitInterval) :
    (γ₁.trans γ₂) (halfR s) = γ₂ s := by
  rw [Path.trans_apply]
  split_ifs with h
  · have hs : (s : ℝ) = 0 := by
      rw [coe_halfR] at h
      linarith [s.2.1]
    have hs' : s = 0 := Subtype.ext hs
    subst hs'
    rw [γ₂.source]
    convert γ₁.target
    simp only [coe_halfR, Set.Icc.coe_zero, Set.Icc.coe_one]
    norm_num
  · congr 1
    ext
    simp only [coe_halfR]
    ring

theorem isPrimitiveAlong_trans_left {η : Ω[modularFunctionFieldOver N ℂ⁄ℂ]} {P Q R : Place ℂ (modularFunctionFieldOver N ℂ)} {γ₁ : Path P Q}
    {γ₂ : Path Q R} {g : unitInterval → ℂ} (hg : IsPrimitiveAlong N η (γ₁.trans γ₂) g) :
    IsPrimitiveAlong N η γ₁ (g ∘ halfL) := by
  intro t₀
  obtain ⟨Φ, hΦ, hg'⟩ := hg (halfL t₀)
  rw [trans_halfL] at hΦ hg'
  refine ⟨Φ, hΦ, ?_⟩
  filter_upwards [continuous_halfL.continuousAt.eventually hg'] with t ht
  simpa only [Function.comp_apply, trans_halfL] using ht

theorem isPrimitiveAlong_trans_right {η : Ω[modularFunctionFieldOver N ℂ⁄ℂ]} {P Q R : Place ℂ (modularFunctionFieldOver N ℂ)} {γ₁ : Path P Q}
    {γ₂ : Path Q R} {g : unitInterval → ℂ} (hg : IsPrimitiveAlong N η (γ₁.trans γ₂) g) :
    IsPrimitiveAlong N η γ₂ (g ∘ halfR) := by
  intro t₀
  obtain ⟨Φ, hΦ, hg'⟩ := hg (halfR t₀)
  rw [trans_halfR] at hΦ hg'
  refine ⟨Φ, hΦ, ?_⟩
  filter_upwards [continuous_halfR.continuousAt.eventually hg'] with t ht
  simpa only [Function.comp_apply, trans_halfR] using ht

theorem pathIntegral_trans {η : Ω[modularFunctionFieldOver N ℂ⁄ℂ]} (hη : η ∈ regularDifferentials ℂ (modularFunctionFieldOver N ℂ)) {P Q R : Place ℂ (modularFunctionFieldOver N ℂ)} (γ₁ : Path P Q)
    (γ₂ : Path Q R) :
    pathIntegral N η (γ₁.trans γ₂) = pathIntegral N η γ₁ + pathIntegral N η γ₂ := by
  obtain ⟨g, hg⟩ := exists_isPrimitiveAlong N η hη (γ₁.trans γ₂)
  rw [pathIntegral_eq_of_isPrimitiveAlong N hg, pathIntegral_eq_of_isPrimitiveAlong N (isPrimitiveAlong_trans_left N hg),
    pathIntegral_eq_of_isPrimitiveAlong N (isPrimitiveAlong_trans_right N hg)]
  have h1 : halfL 1 = halfR 0 := Subtype.ext (by simp)
  have h0 : halfL 0 = (0 : unitInterval) := Subtype.ext (by simp)
  have h2 : halfR 1 = (1 : unitInterval) := Subtype.ext (by simp)
  simp only [Function.comp_apply, h1, h0, h2]
  ring

theorem pathIntegral_symm {η : Ω[modularFunctionFieldOver N ℂ⁄ℂ]} (hη : η ∈ regularDifferentials ℂ (modularFunctionFieldOver N ℂ)) {P Q : Place ℂ (modularFunctionFieldOver N ℂ)} (γ : Path P Q) :
    pathIntegral N η γ.symm = -pathIntegral N η γ := by
  obtain ⟨g, hg⟩ := exists_isPrimitiveAlong N η hη γ
  rw [pathIntegral_eq_of_isPrimitiveAlong N hg, pathIntegral_eq_of_isPrimitiveAlong N (isPrimitiveAlong_symm N hg)]
  simp only [Function.comp_apply, unitInterval.symm_one, unitInterval.symm_zero]
  ring


end
end Dubon2026.SourceFunctionField.OriginalChart
