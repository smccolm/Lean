import Dubon2026.ArithmeticFiniteLocalH2Vanishing
import Dubon2026.ArithmeticFiniteLocalRestrictionSquare
import Dubon2026.ContinuousH2RestrictionSquare
import Dubon2026.FiniteCoefficientGaloisH2Stage

/-! # Original arithmetic H2 restrictions of genuine finite-stage classes

The proved field square and coefficient comparison identify the original
arithmetic restriction with inflation from its constructed unramified local
stage. Actual local H2 vanishing then removes this restriction away from the
exceptional integer, without assuming the desired arithmetic vanishing.
-/

namespace Dubon2026
noncomputable section
open scoped NumberField

attribute [local instance] arithmeticFiniteLocalStageAlgebra
  arithmeticFiniteLocalStageGalois arithmeticFiniteLocalStageRationalAlgebra

variable (a : 𝓞 ℚ)

/-- Use the original arithmetic extension's proved Galois structure. -/
local instance arithmeticFiniteStageH2Galois : IsGalois ℚ (rationalUnramifiedExtension a) :=
  originalUnramifiedGaloisUnion_isGalois a

variable (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
  (p : ℕ) (hp : p.Prime) (q : ℕ) [Fact q.Prime]
  (A : Rep.{0} (ZMod q) Gal(rationalUnramifiedExtension a / ℚ))
  [Finite A] [TopologicalSpace A] [DiscreteTopology A] [ContinuousSMul (ZMod q) A]
  (hA : Continuous (fun z : Gal(rationalUnramifiedExtension a / ℚ) × A => A.ρ z.1 z.2))
  (ρ : Representation (ZMod q) Gal(F/ℚ) A)
  (hρ : ∀ g : Gal(rationalUnramifiedExtension a / ℚ), ∀ b : A,
    ρ (AlgEquiv.restrictNormalHom F g) b = A.ρ g b)

/-- The actual arithmetic restriction of a genuine finite-stage H2 class is
zero away from the exceptional integer. The finite local stage, unramifiedness,
restriction square and local inflation vanishing are all constructed or proved. -/
theorem arithmeticFiniteStageH2Restriction_eq_zero (ha : a ≠ 0) (hpa : ¬(p : 𝓞 ℚ) ∣ a)
    (y : ContinuousRepresentationH2 (Rep.of ρ) continuous_of_discreteTopology) :
    continuousRepresentationH2Restriction A hA
      (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
      (rationalPrimeArithmeticRestriction a p hp).continuous
      (finiteCoefficientGaloisH2Inflation A hA F ρ hρ y) = 0 := by
  let π : Gal(rationalUnramifiedExtension a / ℚ) →* Gal(F/ℚ) := AlgEquiv.restrictNormalHom F
  have hπ : Continuous π := InfiniteGalois.restrictNormalHom_continuous F.toIntermediateField
  let j := (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
  have hj : Continuous j := (rationalPrimeArithmeticRestriction a p hp).continuous
  let k := rationalArithmeticFiniteLocalRestriction a F p hp
  have hk : Continuous k := continuous_of_discreteTopology
  let r : Gal(rationalPrimeLocalClosure p hp / rationalPrimeLocalField p hp) →*
      Gal(rationalArithmeticFiniteLocalStage a F p hp / rationalPrimeLocalField p hp) :=
    AlgEquiv.restrictNormalHom (rationalArithmeticFiniteLocalStage a F p hp)
  have hr : Continuous r := InfiniteGalois.restrictNormalHom_continuous
    (rationalArithmeticFiniteLocalStage a F p hp).toIntermediateField
  have hsq : π.comp j = k.comp r := rationalArithmeticFiniteLocalRestriction_square a F p hp
  exact continuousH2RestrictionSquare_eq_zero A (Rep.of ρ) hA continuous_of_discreteTopology
    π hπ j hj k hk r hr hsq LinearMap.id continuous_id hρ y
    (arithmeticFiniteLocalStageH2_absolute_inflation_eq_zero a F p hp q
      (restrictedCoefficientRep (Rep.of ρ) k)
      (restrictedCoefficientAction_continuous (Rep.of ρ) k hk continuous_of_discreteTopology)
      ha hpa (continuousRepresentationH2Restriction (Rep.of ρ) continuous_of_discreteTopology k hk y))

end
end Dubon2026
