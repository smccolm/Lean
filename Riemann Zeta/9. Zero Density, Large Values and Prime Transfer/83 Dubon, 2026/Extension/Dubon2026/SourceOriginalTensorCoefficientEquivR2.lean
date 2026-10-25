import Dubon2026.SourceOriginalTensorCoefficientMapR2
import Mathlib.FieldTheory.LinearDisjoint

/-! DUB-17/18 -> actual Hecke norm -> coefficient extension of Atkin-Lehner.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
Definitions/Def_ModularCurve_GeometricBaseChange.lean. The existing local
coefficient-independence theorem supplies tensor injectivity. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open scoped TensorProduct
open IntermediateField

variable (L : Type*) [Field L] [Algebra ℚ L]
variable (F₀ : IntermediateField ℚ (LaurentSeries ℚ))

variable [Algebra.IsAlgebraic ℚ L]

theorem isField_tensorProduct : IsField (L ⊗[ℚ] F₀) := by
  letI : IsDomain (L ⊗[ℚ] F₀) :=
    Function.Injective.isDomain (baseChangeHom L F₀).toRingHom (baseChangeHom_injective L F₀)
  exact Algebra.TensorProduct.isField_of_isAlgebraic ℚ L F₀ (Or.inl inferInstance)

private theorem isField_range_baseChangeHom : IsField (baseChangeHom L F₀).range :=
  MulEquiv.isField (isField_tensorProduct L F₀)
    (AlgEquiv.ofInjective _ (baseChangeHom_injective L F₀)).symm.toMulEquiv

theorem exists_baseChangeHom_eq {y : LaurentSeries L} (hy : y ∈ laurentBaseChange L F₀) :
    ∃ x : L ⊗[ℚ] F₀, baseChangeHom L F₀ x = y := by
  let K : IntermediateField L (LaurentSeries L) :=
    (baseChangeHom L F₀).range.toIntermediateField' (isField_range_baseChangeHom L F₀)
  have hle : laurentBaseChange L F₀ ≤ K := by
    change IntermediateField.adjoin L _ ≤ K
    refine IntermediateField.adjoin_le_iff.mpr ?_
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨(1 : L) ⊗ₜ ⟨f, hf⟩, baseChangeHom_one_tmul L F₀ ⟨f, hf⟩⟩
  exact hle hy

/-- Identify the actual Laurent coefficient extension with its algebraic tensor realization. -/
def baseChangeEquiv : L ⊗[ℚ] F₀ ≃ₐ[L] laurentBaseChange L F₀ :=
  AlgEquiv.ofBijective
    { toFun := fun x => ⟨baseChangeHom L F₀ x, baseChangeHom_mem L F₀ x⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun x y => Subtype.ext (map_mul _ x y)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun x y => Subtype.ext (map_add _ x y)
      commutes' := fun c => Subtype.ext ((baseChangeHom L F₀).commutes c) }
    ⟨fun x y h => baseChangeHom_injective L F₀ (congrArg Subtype.val h), fun y => by
      obtain ⟨x, hx⟩ := exists_baseChangeHom_eq L F₀ y.2
      exact ⟨x, Subtype.ext hx⟩⟩

theorem baseChangeEquiv_one_tmul (f : F₀) :
    baseChangeEquiv L F₀ (1 ⊗ₜ f) = ⟨coeffEmb L f, coeffEmb_mem_laurentBaseChange L f.2⟩ :=
  Subtype.ext (baseChangeHom_one_tmul L F₀ f)

/-- Extend a rational field automorphism through the literal tensor coefficient realization. -/
def geomAut : (F₀ ≃ₐ[ℚ] F₀) →* (laurentBaseChange L F₀ ≃ₐ[L] laurentBaseChange L F₀) :=
  MonoidHom.mk'
    (fun σ => ((baseChangeEquiv L F₀).symm.trans
      (Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[L] L) σ)).trans (baseChangeEquiv L F₀))
    (fun σ τ => AlgEquiv.ext fun x => by
      change baseChangeEquiv L F₀ (Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[L] L) (σ * τ)
          ((baseChangeEquiv L F₀).symm x)) =
        baseChangeEquiv L F₀ (Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[L] L) σ
          ((baseChangeEquiv L F₀).symm (baseChangeEquiv L F₀
            (Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[L] L) τ
              ((baseChangeEquiv L F₀).symm x)))))
      rw [AlgEquiv.symm_apply_apply]
      congr 1
      induction (baseChangeEquiv L F₀).symm x using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul c f => rfl
      | add y z hy hz => simp only [map_add, hy, hz])

theorem geomAut_apply (σ : F₀ ≃ₐ[ℚ] F₀) (x : laurentBaseChange L F₀) :
    geomAut L F₀ σ x = baseChangeEquiv L F₀
      (Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[L] L) σ ((baseChangeEquiv L F₀).symm x)) :=
  rfl

theorem geomAut_baseChangeEquiv_tmul (σ : F₀ ≃ₐ[ℚ] F₀) (c : L) (f : F₀) :
    geomAut L F₀ σ (baseChangeEquiv L F₀ (c ⊗ₜ f)) = baseChangeEquiv L F₀ (c ⊗ₜ σ f) := by
  rw [geomAut_apply, AlgEquiv.symm_apply_apply]
  rfl

theorem geomAut_coeffEmb (σ : F₀ ≃ₐ[ℚ] F₀) (f : F₀) :
    geomAut L F₀ σ ⟨coeffEmb L f, coeffEmb_mem_laurentBaseChange L f.2⟩ =
      ⟨coeffEmb L (σ f), coeffEmb_mem_laurentBaseChange L (σ f).2⟩ := by
  rw [← baseChangeEquiv_one_tmul, geomAut_baseChangeEquiv_tmul, baseChangeEquiv_one_tmul]

theorem coe_geomAut_coeffEmb (σ : F₀ ≃ₐ[ℚ] F₀) (f : F₀) :
    (geomAut L F₀ σ ⟨coeffEmb L f, coeffEmb_mem_laurentBaseChange L f.2⟩ : LaurentSeries L) =
      coeffEmb L (σ f) :=
  congrArg Subtype.val (geomAut_coeffEmb L F₀ σ f)

end
end Dubon2026.SourceFunctionField
