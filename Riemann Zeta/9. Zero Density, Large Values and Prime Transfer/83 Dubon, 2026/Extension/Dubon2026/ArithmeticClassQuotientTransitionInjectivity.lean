import Dubon2026.OriginalClassQuotientBaseInvariants
import Dubon2026.ArithmeticClassesModOutsideColimit

/-! # Original class-quotient stages embed under arithmetic transition

The proved reflection of outside-unit images is independent of the
displayed base Galois action. It gives injectivity for the actual field
tower and arithmetic directed system. These faithful coefficient maps
are needed for the continuous class-formation invariant comparison in
DUB-17's global duality and exact dual Selmer relation.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2

section Tower
variable (K E L : Type) [Field K] [Field E] [NumberField E]
  [Field L] [NumberField L] [Algebra K E] [Algebra E L] [Algebra K L]
  [IsScalarTower K E L] [IsGalois K E] [FiniteDimensional E L] [IsGalois E L]
  (S : Finset (HeightOneSpectrum (𝓞 E))) (T : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(E/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K E σ v ∈ S)
  (hT : ∀ (σ : Gal(L/K)) v, v ∈ T ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ T)
  (hST : ∀ w, w ∈ T ↔ originalFinitePrimeBelow E L w ∈ S)

/-- Literal quotient base change is injective for the original displayed Galois tower. -/
theorem originalClassesModOutsideTower_injective :
    Function.Injective (originalClassesModOutsideBaseChangeRepHom K E L S T hS hT hST).hom := by
  have hs : ∀ (σ : Gal(E/E)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv E E σ v ∈ S := by
    intro σ v
    have he : σ = 1 := Subsingleton.elim _ _
    rw [he, numberFieldGaloisPlaceEquiv_one]
  have ht : ∀ (σ : Gal(L/E)) v, v ∈ T ↔ numberFieldGaloisPlaceEquiv E L σ v ∈ T :=
    fun σ v => hT (σ.restrictScalars K) v
  exact originalClassesModOutsideBaseChange_injective E L S T hs ht hST
end Tower

section Arithmetic
variable (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
  (a : 𝓞 K) (ha : a ≠ 0)

/-- Every actual original arithmetic class-quotient transition is injective. -/
theorem arithmeticClassesModOutsideTransitionMap_injective
    (E F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (hEF : E ≤ F) :
    Function.Injective (arithmeticClassesModOutsideTransitionMap K Ω a ha E F hEF) := by
  letI : NumberField E := NumberField.of_module_finite K E
  letI : NumberField F := NumberField.of_module_finite K F
  letI : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
  letI : Module E F := Algebra.toModule
  haveI : IsScalarTower K E F := .of_algebraMap_eq' rfl
  haveI : FiniteDimensional E F := FiniteDimensional.right K E F
  haveI : IsGalois E F := IsGalois.tower_top_of_isGalois K E F
  exact originalClassesModOutsideTower_injective K E F _ _ _ _
    (arithmeticSPlaceFiniteStage_support K Ω a ha E F hEF)

variable [DecidableEq (FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))]

/-- Each original finite class quotient embeds faithfully in the actual arithmetic coefficient colimit. -/
theorem arithmeticClassesModOutsideColimitOf_injective
    (E : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a)) :
    Function.Injective (coefficientRepresentationColimitOf
      (arithmeticGlobalClassesModOutsideStageRep K Ω a ha)
      (arithmeticGlobalClassesModOutsideStageTransition K Ω a ha) E).hom := by
  letI : DirectedSystem (fun F => arithmeticGlobalClassesModOutsideStageRep K Ω a ha F)
      (fun E F h => (arithmeticGlobalClassesModOutsideStageTransition K Ω a ha E F h).hom.toLinearMap) :=
    arithmeticClassesModOutsideDirectedSystem K Ω a ha
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  change Module.DirectLimit.of ℤ _
    (fun F => arithmeticGlobalClassesModOutsideStageRep K Ω a ha F)
    (fun E F h => (arithmeticGlobalClassesModOutsideStageTransition K Ω a ha E F h).hom.toLinearMap)
    E x = 0 at hx
  obtain ⟨F, hEF, hF⟩ := Module.DirectLimit.of.zero_exact hx
  apply arithmeticClassesModOutsideTransitionMap_injective K Ω a ha E F hEF
  exact hF.trans (map_zero _).symm
end Arithmetic

end
end Dubon2026
