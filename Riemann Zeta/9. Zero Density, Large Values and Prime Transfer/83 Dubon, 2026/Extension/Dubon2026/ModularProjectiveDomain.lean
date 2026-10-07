/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck

Selected projective integer action and fundamental-domain proof from PSL2Action.lean,
LeanModularForms 7c41b9b1747d47298f76bdb51f07031087702198.
The measure is Mathlib's existing invariant upper-half-plane volume.
-/
import Dubon2026.ModularPeterssonLevel
import Dubon2026.FundamentalDomainTransport
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
import Mathlib.Data.Countable.Basic

/-! # The actual projective modular group and its hyperbolic fundamental domain -/

namespace Dubon2026

noncomputable section

open scoped MatrixGroups ModularForm Pointwise
open ModularGroup UpperHalfPlane Matrix.SpecialLinearGroup MeasureTheory

local notation "μ_hyp" => (volume : Measure ℍ)

/-- Integer special linear matrices form a countable group. -/
instance modularSLCountable : Countable SL(2, ℤ) := by
  haveI : Countable (Matrix (Fin 2) (Fin 2) ℤ) :=
    inferInstanceAs (Countable (Fin 2 → Fin 2 → ℤ))
  exact inferInstanceAs (Countable { A : Matrix (Fin 2) (Fin 2) ℤ // A.det = 1 })

/-- The projective integer modular group is countable. -/
instance modularPSLCountable : Countable PSL(2, ℤ) :=
  Quotient.countable


/-- The center of `SL(2, ℤ)` consists of `{I, -I}`. Every center element
acts trivially on `ℍ` because it is a scalar matrix `ζI` with `ζ = ±1`,
and `(ζτ + 0)/(0τ + ζ) = τ`. -/
theorem center_SL2Z_smul_eq (c : SL(2, ℤ)) (hc : c ∈ Subgroup.center SL(2, ℤ)) (τ : ℍ) :
    c • τ = τ := by
  rw [mem_center_iff] at hc
  obtain ⟨ζ, hζ, hζ_eq⟩ := hc
  simp only [Fintype.card_fin] at hζ
  have hζ_cases : ζ = 1 ∨ ζ = -1 := by
    rcases mul_eq_zero.mp (by nlinarith [hζ] : (ζ - 1) * (ζ + 1) = 0) with h | h <;> omega
  rcases hζ_cases with rfl | rfl
  · have : c = 1 := by
      ext i j
      simpa [Matrix.scalar] using (congr_fun (congr_fun hζ_eq i) j).symm
    rw [this, one_smul]
  · have : c = -1 := by
      ext i j
      simpa [Matrix.scalar, coe_neg] using (congr_fun (congr_fun hζ_eq i) j).symm
    rw [this]
    simp

private def pslSmul : PSL(2, ℤ) → ℍ → ℍ :=
  Quotient.lift (fun (a : SL(2, ℤ)) (τ : ℍ) ↦ a • τ) (by
    intro a b hab
    funext τ
    change a • τ = b • τ
    rw [show b = a * (a⁻¹ * b) by group, mul_smul,
      center_SL2Z_smul_eq _ (QuotientGroup.leftRel_apply.mp hab)])

@[simp] private theorem pslSmul_coe (a : SL(2, ℤ)) (τ : ℍ) :
    pslSmul (↑a) τ = a • τ := rfl

/-- The action of `PSL(2, ℤ) = SL(2, ℤ)/{±I}` on `ℍ`, descending from the
`SL(2, ℤ)` action since the center acts trivially. -/
instance modularPSLMulAction : MulAction PSL(2, ℤ) ℍ where
  smul g τ := pslSmul g τ
  one_smul τ := by
    change pslSmul (↑(1 : SL(2, ℤ))) τ = τ
    rw [pslSmul_coe, one_smul]
  mul_smul g₁ g₂ τ := by
    induction g₁ using Quotient.inductionOn with | h a => ?_
    induction g₂ using Quotient.inductionOn with | h b => ?_
    change pslSmul ((↑a : PSL(2, ℤ)) * ↑b) τ = pslSmul ↑a (pslSmul ↑b τ)
    rw [← QuotientGroup.mk_mul, pslSmul_coe, pslSmul_coe, pslSmul_coe, mul_smul]

/-- The `PSL(2, ℤ)` action is compatible with the `SL(2, ℤ)` action:
`(↑g) • τ = g • τ` for `g : SL(2, ℤ)`. -/
@[simp]
theorem PSL_smul_coe (g : SL(2, ℤ)) (τ : ℍ) :
    (↑g : PSL(2, ℤ)) • τ = g • τ := rfl


/-- The projective integer action is measurable, through its genuine matrix representative. -/
instance modularPSLMeasurableConstSMul : MeasurableConstSMul PSL(2, ℤ) ℍ where
  measurable_const_smul g := by
    induction g using Quotient.inductionOn with | h a => ?_
    exact (continuous_const_smul (mapGL ℝ a)).measurable

/-- Mathlib's hyperbolic volume is invariant under the integer special linear action. -/
instance modularSLInvariantMeasure : SMulInvariantMeasure SL(2, ℤ) ℍ μ_hyp where
  measure_preimage_smul g s _hs := by
    change μ_hyp ((mapGL ℝ g • ·) ⁻¹' s) = μ_hyp s
    exact MeasureTheory.measure_preimage_smul μ_hyp (mapGL ℝ g) s

/-- The same hyperbolic volume descends to the projective integer action. -/
instance modularPSLInvariantMeasure : SMulInvariantMeasure PSL(2, ℤ) ℍ μ_hyp where
  measure_preimage_smul g s _hs := by
    induction g using Quotient.inductionOn with | h a => ?_
    exact MeasureTheory.measure_preimage_smul μ_hyp a s

private theorem fdo_PSL_pairwise_disjoint :
    Pairwise fun (g₁ g₂ : PSL(2, ℤ)) ↦ Disjoint (g₁ • (fdo : Set ℍ)) (g₂ • fdo) := by
  intro g₁ g₂ hne
  rw [Set.disjoint_left]
  intro τ h1 h2
  obtain ⟨σ₁, hσ₁, rfl⟩ := h1
  obtain ⟨σ₂, hσ₂, h_eq⟩ := h2
  induction g₁ using Quotient.inductionOn with | h a => ?_
  induction g₂ using Quotient.inductionOn with | h b => ?_
  simp only [PSL_smul_coe] at h_eq
  have hba : (b⁻¹ * a) • σ₁ = σ₂ := by rw [mul_smul, ← h_eq, inv_smul_smul]
  exfalso
  apply hne
  rw [Quotient.eq, QuotientGroup.leftRel_apply, show a⁻¹ * b = (b⁻¹ * a)⁻¹ by group]
  apply (Subgroup.center _).inv_mem
  rcases eq_one_or_neg_one_of_mem_fdo_mem_fdo hσ₁ (hba ▸ hσ₂) with he | he
  · rw [he]
    exact one_mem _
  · rw [he]
    refine Subgroup.mem_center_iff.mpr fun x ↦ ?_
    ext i j
    simp [coe_neg, neg_mul, mul_neg]

private lemma measurableSet_fd_diff_fdo : MeasurableSet (fd \ fdo : Set ℍ) :=
  MeasurableSet.diff
    ((isClosed_le continuous_const (Complex.continuous_normSq.comp continuous_coe)).inter
      (isClosed_le (continuous_abs.comp continuous_re) continuous_const)).measurableSet
    Dubon2026.isOpen_fdo.measurableSet

/-- The open fundamental domain `𝒟ᵒ` is a fundamental domain for `PSL(2, ℤ)`
acting on `ℍ` with respect to the hyperbolic measure `μ_hyp`. -/
theorem isFundamentalDomain_fdo_PSL :
    IsFundamentalDomain PSL(2, ℤ) (fdo : Set ℍ) μ_hyp where
  nullMeasurableSet := Dubon2026.isOpen_fdo.measurableSet.nullMeasurableSet
  ae_covers := by
    rw [ae_iff]
    apply measure_mono_null (show {x | ¬∃ g : PSL(2, ℤ), g • x ∈ fdo} ⊆
        ⋃ g : SL(2, ℤ), (g • ·) ⁻¹' (fd \ fdo) by
      intro τ hτ
      push Not at hτ
      obtain ⟨g, hg⟩ := exists_smul_mem_fd τ
      exact Set.mem_iUnion.mpr ⟨g, Set.mem_preimage.mpr ⟨hg, hτ ↑g⟩⟩)
    exact measure_iUnion_null fun g ↦
      (measurePreserving_smul g μ_hyp).measure_preimage
        (measurableSet_fd_diff_fdo.nullMeasurableSet) ▸ hyperbolicMeasure_fd_boundary
  aedisjoint := fun _ _ hne ↦
    (fdo_PSL_pairwise_disjoint hne).aedisjoint

end
end Dubon2026
