import Dubon2026.OriginalIdeleGeneratorBaseChangeTransfer

/-! # Original generator transfer for literal finite intermediate fields

Resolve the field diagram over an abstract ambient field before its
arithmetic specialization. This proves the actual field-map application
needed for DUB-17 without repeatedly unfolding the unramified union.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2

variable (U : Type) [Field U] [CharZero U]
  (K E L M : IntermediateField ℚ U)
  [FiniteDimensional ℚ K] [FiniteDimensional ℚ E]
  [FiniteDimensional ℚ L] [FiniteDimensional ℚ M]
  (hKE : K ≤ E) (hKL : K ≤ L) (hEM : E ≤ M) (hLM : L ≤ M)
  [hGalKE : letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
    IsGalois K E]
  [hGalKL : letI : Algebra K L := (IntermediateField.inclusion hKL).toAlgebra
    IsGalois K L]
  [hGalKM : letI : Algebra K M := (IntermediateField.inclusion (hKE.trans hEM)).toAlgebra
    IsGalois K M]

/-- Literal finite intermediate fields inherit the original idele-witness generator transfer, using their actual inclusion algebras and scalar towers. -/
theorem originalIntermediateField_class_generator_of_idele :
    letI : NumberField K := NumberField.of_module_finite ℚ K
    letI : NumberField E := NumberField.of_module_finite ℚ E
    letI : NumberField L := NumberField.of_module_finite ℚ L
    letI : NumberField M := NumberField.of_module_finite ℚ M
    letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
    letI : Algebra K L := (IntermediateField.inclusion hKL).toAlgebra
    letI : Algebra K M := (IntermediateField.inclusion (hKE.trans hEM)).toAlgebra
    letI : Algebra E M := (IntermediateField.inclusion hEM).toAlgebra
    letI : Algebra L M := (IntermediateField.inclusion hLM).toAlgebra
    letI : IsScalarTower K E M := IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq' rfl
    letI : Module K E := Algebra.toModule
    letI : IsGalois K L := hGalKL
    ∀ (n' : ℕ), Module.finrank K E ∣ n' → n' ≠ 0 →
    ∀ x : groupCohomology (originalFullIdeleRep K L) 2,
      addOrderOf ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalFullClassRepHom K L) x) = n' →
      (groupCohomology.functor ℤ Gal(M/E) 2).map (originalFullClassRepHom E M)
        ((n' / Module.finrank K E) • originalFullIdeleBaseChangeH2 K E L M x) = 0 →
      ∃ y : groupCohomology (originalIdeleClassRep K E) 2,
        Nat.card (groupCohomology (originalIdeleClassRep K E) 2) = Module.finrank K E ∧
        Submodule.span ℤ {y} = ⊤ := by
  letI : NumberField K := NumberField.of_module_finite ℚ K
  letI : NumberField E := NumberField.of_module_finite ℚ E
  letI : NumberField L := NumberField.of_module_finite ℚ L
  letI : NumberField M := NumberField.of_module_finite ℚ M
  letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
  letI : Module K E := Algebra.toModule
  letI : SMul K E := ((IntermediateField.inclusion hKE).toAlgebra).toSMul
  letI : IsScalarTower ℚ K E := IsScalarTower.of_algHom (IntermediateField.inclusion hKE)
  letI : Algebra K L := (IntermediateField.inclusion hKL).toAlgebra
  letI : Module K L := Algebra.toModule
  letI : SMul K L := ((IntermediateField.inclusion hKL).toAlgebra).toSMul
  letI : IsScalarTower ℚ K L := IsScalarTower.of_algHom (IntermediateField.inclusion hKL)
  letI : Algebra K M := (IntermediateField.inclusion (hKE.trans hEM)).toAlgebra
  letI : Module K M := Algebra.toModule
  letI : SMul K M := ((IntermediateField.inclusion (hKE.trans hEM)).toAlgebra).toSMul
  letI : IsScalarTower ℚ K M := IsScalarTower.of_algHom (IntermediateField.inclusion (hKE.trans hEM))
  letI : Algebra E M := (IntermediateField.inclusion hEM).toAlgebra
  letI : Module E M := Algebra.toModule
  letI : SMul E M := ((IntermediateField.inclusion hEM).toAlgebra).toSMul
  letI : IsScalarTower ℚ E M := IsScalarTower.of_algHom (IntermediateField.inclusion hEM)
  letI : Algebra L M := (IntermediateField.inclusion hLM).toAlgebra
  letI : Module L M := Algebra.toModule
  letI : SMul L M := ((IntermediateField.inclusion hLM).toAlgebra).toSMul
  letI : IsScalarTower ℚ L M := IsScalarTower.of_algHom (IntermediateField.inclusion hLM)
  letI : IsScalarTower K E M := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsGalois K L := hGalKL

  letI : IsGalois K E := hGalKE
  letI : IsGalois K M := hGalKM
  letI : FiniteDimensional K M := FiniteDimensional.right ℚ K M
  intro n' hd hn'0 x ho hz
  obtain ⟨y, hc, hs, _⟩ := originalIdeleClass_generator_of_idele_baseChange_zero
    K E L M n' hd hn'0 x ho hz
  exact ⟨y, hc, hs⟩

end
end Dubon2026
