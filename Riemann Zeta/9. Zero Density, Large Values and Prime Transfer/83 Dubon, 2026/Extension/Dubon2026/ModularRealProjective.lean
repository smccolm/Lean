/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck

The final domain-image transport adapts the selected PeterssonLevelN argument
at LeanModularForms 7c41b9b1747d47298f76bdb51f07031087702198.
The real ambient group here is Mathlib's actual PGL, with its existing action.
-/
import Dubon2026.ModularGamma0Domain
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic

/-! # Faithful real projective realization of the actual modular group -/

namespace Dubon2026

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane MeasureTheory
open scoped MatrixGroups Pointwise

noncomputable section

/-- Real matrix extension detects precisely the integer special linear center. -/
theorem mapGL_mem_center_iff (γ : SL(2, ℤ)) :
    mapGL ℝ γ ∈ Subgroup.center (GL (Fin 2) ℝ) ↔ γ ∈ Subgroup.center SL(2, ℤ) := by
  constructor
  · intro h
    apply Subgroup.mem_center_iff.mpr
    intro δ
    apply mapGL_injective (S := ℝ)
    simpa only [map_mul] using (Subgroup.mem_center_iff.mp h) (mapGL ℝ δ)
  · intro h
    obtain ⟨r, _, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp h
    apply GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr
    refine ⟨(r : ℝ), ?_⟩
    change Matrix.scalar (Fin 2) (r : ℝ) = (γ : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ)
    rw [← hr]
    ext i j
    simp only [Matrix.scalar_apply, Matrix.map_apply, Matrix.diagonal_apply]
    split_ifs <;> simp

/-- The actual integer matrix map into the real projective general linear group. -/
def slToRealProjective : SL(2, ℤ) →* PGL(2, ℝ) :=
  ProjGenLinGroup.mk.comp (mapGL ℝ)

/-- Only the actual integer center disappears under real projectivization. -/
theorem slToRealProjective_ker : slToRealProjective.ker = Subgroup.center SL(2, ℤ) := by
  ext γ
  simp [slToRealProjective, MonoidHom.mem_ker, mapGL_mem_center_iff]

/-- The actual modular projective group embeds in the real projective group. -/
def modularProjectiveEmbedding : PSL(2, ℤ) →* PGL(2, ℝ) :=
  QuotientGroup.lift (Subgroup.center SL(2, ℤ)) slToRealProjective
    (by rw [slToRealProjective_ker])

/-- The embedding has trivial kernel. -/
theorem modularProjectiveEmbedding_injective : Function.Injective modularProjectiveEmbedding := by
  rw [← MonoidHom.ker_eq_bot_iff]
  unfold modularProjectiveEmbedding
  rw [QuotientGroup.ker_lift, slToRealProjective_ker, QuotientGroup.map_mk'_self]

/-- The faithful real embedding preserves the actual upper-half-plane action. -/
theorem modularProjectiveEmbedding_smul (γ : PSL(2, ℤ)) (τ : ℍ) :
    modularProjectiveEmbedding γ • τ = γ • τ := by
  induction γ using Quotient.inductionOn with | h δ => ?_
  rfl

/-- The real projective action is continuous through each genuine matrix representative. -/
instance realProjectiveContinuousConstSMul : ContinuousConstSMul PGL(2, ℝ) ℍ where
  continuous_const_smul γ := by
    induction γ using ProjGenLinGroup.induction_on with | mk A => ?_
    exact continuous_const_smul A

/-- Mathlib's actual hyperbolic volume is invariant under real projective transformations. -/
instance realProjectiveInvariantMeasure : SMulInvariantMeasure PGL(2, ℝ) ℍ (volume : Measure ℍ) where
  measure_preimage_smul γ S _hS := by
    induction γ using ProjGenLinGroup.induction_on with | mk A => ?_
    exact MeasureTheory.measure_preimage_smul (volume : Measure ℍ) A S

/-- The actual real projective image of Gamma0. -/
def realProjectiveGamma0 (Q : ℕ) : Subgroup PGL(2, ℝ) :=
  (projectiveGamma0 Q).map modularProjectiveEmbedding

/-- The integer tiling remains a genuine domain for its faithful real projective image. -/
theorem isFundamentalDomain_realGamma0 (Q : ℕ) [NeZero Q] :
    IsFundamentalDomain (realProjectiveGamma0 Q) (gamma0FundamentalDomain Q)
      (volume : Measure ℍ) := by
  have he : (Equiv.refl ℍ) '' gamma0FundamentalDomain Q = gamma0FundamentalDomain Q := by simp
  rw [← he]
  refine (isFundamentalDomain_gamma0 Q).image_of_equiv (Equiv.refl ℍ)
    (Measure.QuasiMeasurePreserving.id _) ((Subgroup.equivMapOfInjective (projectiveGamma0 Q)
      modularProjectiveEmbedding modularProjectiveEmbedding_injective).toEquiv.symm) ?_
  intro g τ
  let e := Subgroup.equivMapOfInjective (projectiveGamma0 Q)
    modularProjectiveEmbedding modularProjectiveEmbedding_injective
  have hv : (g : PGL(2, ℝ)) = modularProjectiveEmbedding (e.symm g : PSL(2, ℤ)) := by
    rw [← Subgroup.coe_equivMapOfInjective_apply (projectiveGamma0 Q)
      modularProjectiveEmbedding modularProjectiveEmbedding_injective (e.symm g)]
    exact congrArg Subtype.val (e.apply_symm_apply g).symm
  change (e.symm g : PSL(2, ℤ)) • τ = (g : PGL(2, ℝ)) • τ
  rw [hv, modularProjectiveEmbedding_smul]

end
end Dubon2026
