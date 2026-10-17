import Dubon2026.OriginalInfiniteKernelSystemFromAuxiliary

/-! # Canonical class systems over literal intermediate-field towers

Resolve the genuine inclusion algebras over an abstract ambient field,
then use the proved auxiliary-idele normalization. This keeps the arithmetic
application on DUB-17's required original objects within default limits.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2
attribute [-instance] SubfieldClass.instSMulRat

/-- Retain the supplied rational algebra on each literal intermediate field. -/
local instance originalInfiniteKernelIntermediateRationalAlgebra
    (U : Type) [Field U] [Algebra ℚ U] (F : IntermediateField ℚ U) : Algebra ℚ F := F.algebra'

variable (U : Type) [Field U] [Algebra ℚ U]
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

/-- The actual auxiliary-idele normalization theorem applies to literal finite intermediate fields with all original scalar towers resolved. -/
theorem originalIntermediateField_infinite_kernel_system_of_auxiliary_idele :
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
    ∀ (totalE : groupCohomology (originalFullIdeleRep K E) 2 →+ AddCircle (1 : ℚ))
    (totalL : groupCohomology (originalFullIdeleRep K L) 2 →+ AddCircle (1 : ℚ))
    (totalM : groupCohomology (originalFullIdeleRep K M) 2 →+ AddCircle (1 : ℚ))
    (_hE : ∀ x, totalM (originalFullIdeleBaseChangeH2 K K E M x) = totalE x)
    (_hL : ∀ x, totalM (originalFullIdeleBaseChangeH2 K K L M x) = totalL x)
    (_hkernel : ∀ x,
      (∀ v : NumberField.InfinitePlace M, originalFullIdeleInfiniteH2 K M v x = 0) →
      (groupCohomology.functor ℤ Gal(M/K) 2).map
      (originalFullClassRepHom K M) x = 0 → totalM x = 0)
    (n : ℕ) (_hd : Module.finrank K E ∣ n) (_hn : n ≠ 0)
    (x : groupCohomology (originalFullIdeleRep K L) 2)
    (_hx : addOrderOf ((groupCohomology.functor ℤ Gal(L/K) 2).map
      (originalFullClassRepHom K L) x) = n)
    (_hz : (groupCohomology.functor ℤ Gal(M/E) 2).map (originalFullClassRepHom E M)
      ((n / Module.finrank K E) • originalFullIdeleBaseChangeH2 K E L M x) = 0)
    (_ht : totalL x = ↑((1 : ℚ) / n))
    (_hInf : ∀ v : NumberField.InfinitePlace L, originalFullIdeleInfiniteH2 K L v x = 0),
    OriginalInfiniteKernelClassInvariantSystem K E totalE := by
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
  intro totalE totalL totalM hE hL hkernel n hd hn x hx hz ht hInf
  exact originalIdeleClass_infinite_kernel_system_of_auxiliary_idele K E L M
    totalE totalL totalM hE hL hkernel n hd hn x hx hz ht hInf

end
end Dubon2026
