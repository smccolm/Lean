import Dubon2026.AuxiliaryPowerSeriesAugmentation
import Mathlib.RingTheory.MvPowerSeries.Rename

/-! Reindex the actual character parameters by a fixed finite set.
The variable ideal and every original quotient matrix are preserved.
This supplies the common variable ideal needed on DUB-17's patching
dependency; arithmetic Hecke freeness and vanishing annihilators are
separate obligations. -/

namespace Dubon2026
noncomputable section
open Matrix IsLocalRing

variable (O : Type*) [CommRing O] {R A ι n G η : Type*}
  [CommRing R] [IsLocalRing R] [Algebra O R] [CommRing A] [Algebra O A]
  [Fintype ι] [Fintype n] [DecidableEq n]
  (Q : Finset Nat.Primes) (q : ℕ)
  (τ : G → GeneralLinearGroup n R) (τ₀ : G → GeneralLinearGroup n A)

/-- The actual parameter map with its variables indexed by a fixed
set equivalent to the selected prime and character directions. -/
def auxiliaryPowerSeriesFixedParameterMap
    (d : AuxiliaryPowerSeriesAugmentationComparison O (ι := ι) Q q τ τ₀)
    (e : η ≃ Q × ι) : MvPowerSeries η O →ₐ[O] R :=
  d.parameters.parameterMap.comp (MvPowerSeries.renameEquiv O e).toAlgHom

/-- Each fixed variable still records its original tame character. -/
theorem auxiliaryPowerSeriesFixedParameterMap_X
    (d : AuxiliaryPowerSeriesAugmentationComparison O (ι := ι) Q q τ τ₀)
    (e : η ≃ Q × ι) (i : η) :
    auxiliaryPowerSeriesFixedParameterMap O Q q τ τ₀ d e (MvPowerSeries.X i) =
      (d.augmentation.characters (e i).1 (d.parameters.generators (e i).1)).val (e i).2 - 1 := by
  change d.parameters.parameterMap (MvPowerSeries.rename e (MvPowerSeries.X i)) = _
  rw [MvPowerSeries.rename_X]
  exact d.parameters.variableValue (e i)

/-- Bijective reindexing preserves the full augmentation ideal. -/
theorem auxiliaryPowerSeriesFixedParameterMap_augmentation
    (d : AuxiliaryPowerSeriesAugmentationComparison O (ι := ι) Q q τ τ₀)
    (e : η ≃ Q × ι) :
    Ideal.map (auxiliaryPowerSeriesFixedParameterMap O Q q τ τ₀ d e).toRingHom
      (Ideal.span (Set.range (MvPowerSeries.X (R := O) (σ := η)))) =
        auxiliaryFamilyAugmentationIdeal O d.augmentation.characters := by
  rw [Ideal.map_span, ← Set.range_comp]
  have hr : Set.range ((auxiliaryPowerSeriesFixedParameterMap O Q q τ τ₀ d e) ∘
      MvPowerSeries.X) = Set.range (d.parameters.parameterMap ∘ MvPowerSeries.X) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      refine ⟨e i, ?_⟩
      change d.parameters.parameterMap (MvPowerSeries.X (e i)) =
        d.parameters.parameterMap (MvPowerSeries.rename e (MvPowerSeries.X i))
      rw [MvPowerSeries.rename_X]
    · rintro ⟨j, rfl⟩
      refine ⟨e.symm j, ?_⟩
      change d.parameters.parameterMap (MvPowerSeries.rename e (MvPowerSeries.X (e.symm j))) =
        d.parameters.parameterMap (MvPowerSeries.X j)
      rw [MvPowerSeries.rename_X, e.apply_symm_apply]
  change Ideal.span (Set.range ((auxiliaryPowerSeriesFixedParameterMap O Q q τ τ₀ d e) ∘
    MvPowerSeries.X)) = _
  rw [hr]
  have h := d.parameters.augmentation
  rw [Ideal.map_span, ← Set.range_comp] at h
  exact h

/-- The fixed variable ideal recovers the original base ring. -/
def auxiliaryPowerSeriesFixedQuotientEquiv
    (d : AuxiliaryPowerSeriesAugmentationComparison O (ι := ι) Q q τ τ₀)
    (e : η ≃ Q × ι) :
    (R ⧸ Ideal.map (auxiliaryPowerSeriesFixedParameterMap O Q q τ τ₀ d e).toRingHom
      (Ideal.span (Set.range (MvPowerSeries.X (R := O) (σ := η))))) ≃ₐ[O] A :=
  (Ideal.quotientEquivAlgOfEq O
    (auxiliaryPowerSeriesFixedParameterMap_augmentation O Q q τ τ₀ d e)).trans
      d.augmentation.equiv

/-- The fixed-variable quotient comparison preserves every original
universal matrix, with the same character family and base ring. -/
theorem auxiliaryPowerSeriesFixedQuotientEquiv_matrix
    (d : AuxiliaryPowerSeriesAugmentationComparison O (ι := ι) Q q τ τ₀)
    (e : η ≃ Q × ι) (g : G) :
    GeneralLinearGroup.map
      (auxiliaryPowerSeriesFixedQuotientEquiv O Q q τ τ₀ d e).toAlgHom.toRingHom
      (GeneralLinearGroup.map
        (Ideal.Quotient.mk (Ideal.map
          (auxiliaryPowerSeriesFixedParameterMap O Q q τ τ₀ d e).toRingHom
          (Ideal.span (Set.range (MvPowerSeries.X (R := O) (σ := η)))))) (τ g)) = τ₀ g := by
  let J := Ideal.map (auxiliaryPowerSeriesFixedParameterMap O Q q τ τ₀ d e).toRingHom
    (Ideal.span (Set.range (MvPowerSeries.X (R := O) (σ := η))))
  let K := auxiliaryFamilyAugmentationIdeal O d.augmentation.characters
  let f := Ideal.quotientEquivAlgOfEq O
    (auxiliaryPowerSeriesFixedParameterMap_augmentation O Q q τ τ₀ d e)
  have hf : GeneralLinearGroup.map f.toAlgHom.toRingHom
      (GeneralLinearGroup.map (Ideal.Quotient.mk J) (τ g)) =
      GeneralLinearGroup.map (Ideal.Quotient.mk K) (τ g) := by
    apply Units.ext
    apply Matrix.ext
    intro i j
    exact Ideal.quotientEquivAlgOfEq_mk O
      (auxiliaryPowerSeriesFixedParameterMap_augmentation O Q q τ τ₀ d e) ((τ g).val i j)
  change GeneralLinearGroup.map (d.augmentation.equiv.toAlgHom.toRingHom.comp f.toAlgHom.toRingHom)
    (GeneralLinearGroup.map (Ideal.Quotient.mk J) (τ g)) = τ₀ g
  rw [GeneralLinearGroup.map_comp, MonoidHom.comp_apply, hf]
  exact d.augmentation.matrix g

end
end Dubon2026
