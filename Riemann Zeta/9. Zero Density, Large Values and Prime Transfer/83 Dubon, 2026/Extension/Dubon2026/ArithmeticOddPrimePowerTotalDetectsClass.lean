import Dubon2026.ArithmeticAllPrimeInfiniteKernelClassSystem
import Dubon2026.OriginalInfiniteKernelOddTotal

/-! # Zero detection at the required odd-primary Sylow stage

Reuse the proved prime-power class invariant system at the common comparison
field's actual Sylow fixed field. Its degree is odd, so no infinite-coordinate
condition is needed on the source-induced idele representative. This is the
finite zero-detection input for reverse localization on DUB-17's dependency
chain; it does not identify the source local cup-pairing total.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2
attribute [-instance] SubfieldClass.instSMulRat AlgebraicClosure.instSMulOfIsScalarTower
  UniformSpace.Completion.instSMul
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticRelativeStageClassAddCommGroup arithmeticRelativeStageIdeleAddCommGroup

/-- The canonical total detects the actual full-class image at every
required odd prime-power arithmetic stage, including noncyclic stages and
degree one. The class invariant and its infinite-coordinate condition are
derived from the original arithmetic objects. -/
theorem rationalArithmeticRelativeOddPrimePower_total_zero_iff_class_zero
    (a : 𝓞 ℚ) (K E : IntermediateField ℚ (rationalUnramifiedExtension a))
    [FiniteDimensional ℚ K] [FiniteDimensional ℚ E] (hKE : K ≤ E)
    [hGalKE : letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
      IsGalois K E]
    (q t : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hqa : (q : 𝓞 ℚ) ∣ a)
    (hdegree : letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
      letI : Module K E := Algebra.toModule
      Module.finrank K E = q ^ t)
    (x : rationalArithmeticRelativeStageIdeleH2 a K E hKE) :
    letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
    rationalArithmeticRelativeStageIdeleTotalInvariant a K E hKE x = 0 ↔
      (groupCohomology.functor ℤ Gal(E/K) 2).map (originalFullClassRepHom K E) x = 0 := by
  letI : Algebra K E := (IntermediateField.inclusion hKE).toAlgebra
  letI : Module K E := Algebra.toModule
  letI : SMul K E := ((IntermediateField.inclusion hKE).toAlgebra).toSMul
  letI : IsScalarTower ℚ K E := IsScalarTower.of_algHom (IntermediateField.inclusion hKE)
  letI : FiniteDimensional K E := FiniteDimensional.right ℚ K E
  letI : IsGalois K E := hGalKE
  let total := rationalArithmeticRelativeStageIdeleTotalInvariant a K E hKE
  have hsystem := rationalArithmeticRelativeAllPrimePower_exists_infinite_kernel_class_system
    (hGalKE := hGalKE) a K E hKE q t hq hqa hdegree
  let inv := originalInfiniteKernelClassInvariant K E total hsystem
  have hi : Function.Injective inv := originalInfiniteKernelClassInvariant_injective K E total hsystem
  have hn : Odd (Module.finrank K E) := (congrArg Odd hdegree).mpr (hq.odd_of_ne_two hq2).pow
  have ht := originalInfiniteKernelClassInvariant_total_of_odd K E total hsystem hn x
  constructor
  · intro hz
    apply hi
    exact (ht.trans hz).trans (map_zero inv).symm
  · intro hz
    exact ht.symm.trans ((congrArg inv hz).trans (map_zero inv))

end
end Dubon2026
