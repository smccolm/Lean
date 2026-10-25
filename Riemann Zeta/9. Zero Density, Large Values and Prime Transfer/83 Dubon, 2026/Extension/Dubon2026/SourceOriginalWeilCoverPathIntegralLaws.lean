import Dubon2026.SourceOriginalWeilCoverPathIntegral

/-! DUB-17/18 -> auxiliary point division -> cover Abel comparison.
The native original-curve path and local Abel arguments are adapted to the
literal Kummer splitting field and its constructed complex manifold.
All path and primitive inputs are proved; Abel inversion and its principal
kernel remain required. Adapted from anthropics/fermats-last-theorem,
Apache-2.0, commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
Def_AlgebraicCurve_ComplexLineIntegral and
S_AlgebraicCurve_exists_ball_abelJacobiVec_sub_sub_mem_pathPeriodLattice.
-/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Filter Set KaehlerDifferential
open scoped Topology
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

variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
variable (r : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C r : Polynomial FF)
variable (A : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hr : r ≠ 0)
variable (hrA : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord r = (n : ℤ) * A v)
include A hr hrA
local notation "CoverPath" => @Path (Place ℂ EE) (placeTopology N n r A hr hrA)

theorem isPrimitiveAlong_symm {η : Ω[EE⁄ℂ]} {P Q : Place ℂ (EE)} {γ : CoverPath P Q}
    {g : unitInterval → ℂ} (hg : IsPrimitiveAlong N n r A hr hrA η γ g) :
    IsPrimitiveAlong N n r A hr hrA η (@Path.symm (Place ℂ EE) (placeTopology N n r A hr hrA) _ _ γ) (g ∘ unitInterval.symm) := by
  letI := placeTopology N n r A hr hrA
  intro t₀
  obtain ⟨Φ, hΦ, hg'⟩ := hg (unitInterval.symm t₀)
  refine ⟨Φ, ?_, ?_⟩
  · simp only [Path.symm_apply] at hΦ ⊢
    exact hΦ
  · have hc : ContinuousAt unitInterval.symm t₀ := unitInterval.continuous_symm.continuousAt
    filter_upwards [hc.eventually hg'] with t ht
    simpa only [Path.symm_apply, Function.comp_apply] using ht

private theorem trans_halfL {P Q R : Place ℂ (EE)} (γ₁ : CoverPath P Q) (γ₂ : CoverPath Q R) (s : unitInterval) :
    (@Path.trans (Place ℂ EE) (placeTopology N n r A hr hrA) _ _ _ γ₁ γ₂) (halfL s) = γ₁ s := by
  letI := placeTopology N n r A hr hrA
  rw [Path.trans_apply]
  have h : ((halfL s : unitInterval) : ℝ) ≤ 1 / 2 := by
    rw [coe_halfL]; linarith [s.2.2]
  rw [dif_pos h]
  congr 1
  ext
  simp only [coe_halfL]
  ring

private theorem trans_halfR {P Q R : Place ℂ (EE)} (γ₁ : CoverPath P Q) (γ₂ : CoverPath Q R) (s : unitInterval) :
    (@Path.trans (Place ℂ EE) (placeTopology N n r A hr hrA) _ _ _ γ₁ γ₂) (halfR s) = γ₂ s := by
  letI := placeTopology N n r A hr hrA
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

theorem isPrimitiveAlong_trans_left {η : Ω[EE⁄ℂ]} {P Q R : Place ℂ (EE)} {γ₁ : CoverPath P Q}
    {γ₂ : CoverPath Q R} {g : unitInterval → ℂ} (hg : IsPrimitiveAlong N n r A hr hrA η (@Path.trans (Place ℂ EE) (placeTopology N n r A hr hrA) _ _ _ γ₁ γ₂) g) :
    IsPrimitiveAlong N n r A hr hrA η γ₁ (g ∘ halfL) := by
  letI := placeTopology N n r A hr hrA
  intro t₀
  obtain ⟨Φ, hΦ, hg'⟩ := hg (halfL t₀)
  rw [trans_halfL] at hΦ hg'
  refine ⟨Φ, hΦ, ?_⟩
  filter_upwards [continuous_halfL.continuousAt.eventually hg'] with t ht
  simpa only [Function.comp_apply, trans_halfL] using ht

theorem isPrimitiveAlong_trans_right {η : Ω[EE⁄ℂ]} {P Q R : Place ℂ (EE)} {γ₁ : CoverPath P Q}
    {γ₂ : CoverPath Q R} {g : unitInterval → ℂ} (hg : IsPrimitiveAlong N n r A hr hrA η (@Path.trans (Place ℂ EE) (placeTopology N n r A hr hrA) _ _ _ γ₁ γ₂) g) :
    IsPrimitiveAlong N n r A hr hrA η γ₂ (g ∘ halfR) := by
  letI := placeTopology N n r A hr hrA
  intro t₀
  obtain ⟨Φ, hΦ, hg'⟩ := hg (halfR t₀)
  rw [trans_halfR] at hΦ hg'
  refine ⟨Φ, hΦ, ?_⟩
  filter_upwards [continuous_halfR.continuousAt.eventually hg'] with t ht
  simpa only [Function.comp_apply, trans_halfR] using ht

theorem pathIntegral_trans {η : Ω[EE⁄ℂ]} (hη : η ∈ regularDifferentials ℂ (EE)) {P Q R : Place ℂ (EE)} (γ₁ : CoverPath P Q)
    (γ₂ : CoverPath Q R) :
    pathIntegral N n r A hr hrA η (@Path.trans (Place ℂ EE) (placeTopology N n r A hr hrA) _ _ _ γ₁ γ₂) = pathIntegral N n r A hr hrA η γ₁ + pathIntegral N n r A hr hrA η γ₂ := by
  letI := placeTopology N n r A hr hrA
  obtain ⟨g, hg⟩ := exists_isPrimitiveAlong N n r A hr hrA η hη (@Path.trans (Place ℂ EE) (placeTopology N n r A hr hrA) _ _ _ γ₁ γ₂)
  rw [pathIntegral_eq_of_isPrimitiveAlong N n r A hr hrA hg, pathIntegral_eq_of_isPrimitiveAlong N n r A hr hrA (isPrimitiveAlong_trans_left N n r A hr hrA hg),
    pathIntegral_eq_of_isPrimitiveAlong N n r A hr hrA (isPrimitiveAlong_trans_right N n r A hr hrA hg)]
  have h1 : halfL 1 = halfR 0 := Subtype.ext (by simp)
  have h0 : halfL 0 = (0 : unitInterval) := Subtype.ext (by simp)
  have h2 : halfR 1 = (1 : unitInterval) := Subtype.ext (by simp)
  simp only [Function.comp_apply, h1, h0, h2]
  ring

theorem pathIntegral_symm {η : Ω[EE⁄ℂ]} (hη : η ∈ regularDifferentials ℂ (EE)) {P Q : Place ℂ (EE)} (γ : CoverPath P Q) :
    pathIntegral N n r A hr hrA η (@Path.symm (Place ℂ EE) (placeTopology N n r A hr hrA) _ _ γ) = -pathIntegral N n r A hr hrA η γ := by
  letI := placeTopology N n r A hr hrA
  obtain ⟨g, hg⟩ := exists_isPrimitiveAlong N n r A hr hrA η hη γ
  rw [pathIntegral_eq_of_isPrimitiveAlong N n r A hr hrA hg, pathIntegral_eq_of_isPrimitiveAlong N n r A hr hrA (isPrimitiveAlong_symm N n r A hr hrA hg)]
  simp only [Function.comp_apply, unitInterval.symm_one, unitInterval.symm_zero]
  ring


end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
