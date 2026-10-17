import Dubon2026.ArithmeticFiniteSourceScalarZero
import Dubon2026.ArithmeticCommonScalarAnnihilator

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2
attribute [-instance] SubfieldClass.instSMulRat
variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- Retain the original rational inclusion of the arithmetic union. -/
local instance finiteSourceScalarAnnihilatorUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

/-- Retain the actual rational structure on each arithmetic stage. -/
local instance finiteSourceScalarAnnihilatorStageAlgebra {V : Type} [Field V] [Algebra ℚ V]
    (E : FiniteGaloisIntermediateField ℚ V) : Algebra ℚ E := E.algebra'

/-- Retain the same structure on its underlying intermediate field. -/
local instance finiteSourceScalarAnnihilatorIntermediateAlgebra {V : Type} [Field V] [Algebra ℚ V]
    (E : IntermediateField ℚ V) : Algebra ℚ E := E.algebra'

/-- The actual finite arithmetic stage is a number field. -/
local instance finiteSourceScalarAnnihilatorNumberField
    (E : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a)) : NumberField E :=
  NumberField.of_module_finite ℚ E

/-- The specified source-induced full class at the common field inherits
the scalar class annihilator through the proved literal quotient isomorphism.
This supplies the exact prime-torsion hypothesis for Sylow detection. -/
theorem arithmeticSourceIdeleFiniteFullClass_nsmul_zero
    (E M : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (hEM : E ≤ M) (L : OriginalUnramifiedGaloisStage (Ω := Ω) a)
    (hLM : originalUnramifiedStageInUnion a L ≤ M)
    (d : groupCohomology.cocycles₂ (ArithmeticSPlaceFiniteStageRep ℚ Ω a ha E))
    (s : groupCohomology.cocycles₂ (arithmeticOriginalStageClassRep Ω a ha L))
    (hcmp : groupCohomology.H2π _ (arithmeticClassStageTwoCocycleTransition ℚ Ω a ha E M hEM
      (groupCohomology.mapCocycles₂ (MonoidHom.id Gal(E/ℚ))
        (arithmeticSPlaceFiniteStageQuotient ℚ Ω a ha E ≫
          arithmeticSourceClassStageComparison ℚ Ω a ha E) d)) =
      groupCohomology.H2π _ (arithmeticClassStageTwoCocycleTransition ℚ Ω a ha
        (originalUnramifiedStageInUnion a L) M hLM
        (arithmeticOriginalStageClassTwoCocycleToImage Ω a ha L s)))
    (p : ℕ) (hs : p • groupCohomology.H2π _ s = 0) :
    p • (groupCohomology.functor ℤ Gal(M/ℚ) 2).map (originalFullClassRepHom ℚ M)
      (arithmeticSourceIdeleFiniteFullH2Transition Ω a ha E M hEM d) = 0 := by
  let e := (rationalArithmeticClassesModOutsideStageH2Iso Ω a ha M).toLinearEquiv
  let c := (groupCohomology.functor ℤ Gal(M/ℚ) 2).map (originalFullClassRepHom ℚ M)
    (arithmeticSourceIdeleFiniteFullH2Transition Ω a ha E M hEM d)
  have hq : e c = groupCohomology.H2π _ (arithmeticClassStageTwoCocycleTransition ℚ Ω a ha
      (originalUnramifiedStageInUnion a L) M hLM
      (arithmeticOriginalStageClassTwoCocycleToImage Ω a ha L s)) :=
    (arithmeticSourceIdeleFiniteFullH2Transition_class Ω a ha E M hEM d).symm.trans hcmp
  have hz := arithmeticOriginalStageClassTwoCocycle_common_nsmul_zero Ω a ha L M hLM s p hs
  apply e.injective
  exact (map_nsmul e p c).trans
    ((congrArg (fun z => p • z) hq).trans (hz.trans (map_zero e).symm))

end
end Dubon2026
