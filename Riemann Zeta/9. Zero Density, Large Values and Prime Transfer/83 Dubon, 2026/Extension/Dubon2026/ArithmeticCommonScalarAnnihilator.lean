import Dubon2026.ArithmeticClassStageCocycleZeroReflection

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2
attribute [-instance] SubfieldClass.instSMulRat
variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- Retain the original rational inclusion of the arithmetic union. -/
local instance commonScalarAnnihilatorUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

/-- Retain the actual rational structure on each arithmetic stage. -/
local instance commonScalarAnnihilatorStageAlgebra {V : Type} [Field V] [Algebra ℚ V]
    (E : FiniteGaloisIntermediateField ℚ V) : Algebra ℚ E := E.algebra'

/-- Retain the same structure on its underlying intermediate field. -/
local instance commonScalarAnnihilatorIntermediateAlgebra {V : Type} [Field V] [Algebra ℚ V]
    (E : IntermediateField ℚ V) : Algebra ℚ E := E.algebra'

/-- The actual finite arithmetic stage is a number field. -/
local instance commonScalarAnnihilatorNumberField
    (E : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a)) : NumberField E :=
  NumberField.of_module_finite ℚ E

/-- The actual scalar class retains its prime annihilator after realization
and passage to the common arithmetic comparison field. This is the precise
annihilation input for Sylow detection of the source-induced full class. -/
theorem arithmeticOriginalStageClassTwoCocycle_common_nsmul_zero
    (L : OriginalUnramifiedGaloisStage (Ω := Ω) a)
    (M : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (hLM : originalUnramifiedStageInUnion a L ≤ M)
    (s : groupCohomology.cocycles₂ (arithmeticOriginalStageClassRep Ω a ha L))
    (p : ℕ) (hs : p • groupCohomology.H2π _ s = 0) :
    p • groupCohomology.H2π _ (arithmeticClassStageTwoCocycleTransition ℚ Ω a ha
      (originalUnramifiedStageInUnion a L) M hLM
      (arithmeticOriginalStageClassTwoCocycleToImage Ω a ha L s)) = 0 := by
  let F := originalUnramifiedStageInUnion a L
  have hF : p • groupCohomology.H2π _ (arithmeticOriginalStageClassTwoCocycleToImage Ω a ha L s) = 0 := by
    let e := originalUnramifiedStageInUnionEquiv a L
    letI : Algebra L.val F := e.toAlgHom.toAlgebra
    letI : Module L.val F := e.toAlgHom.toAlgebra.toModule
    letI : SMul L.val F := e.toAlgHom.toAlgebra.toSMul
    letI : IsScalarTower ℚ L.val F := IsScalarTower.of_algHom e.toAlgHom
    let f := groupCohomology.map
      (AlgEquiv.restrictNormalHom L.val : Gal(F/ℚ) →* Gal(L.val/ℚ))
      (arithmeticOriginalStageClassToImage Ω a ha L) 2
    have hmap := groupCohomology.H2π_comp_map_apply
      (AlgEquiv.restrictNormalHom L.val : Gal(F/ℚ) →* Gal(L.val/ℚ))
      (arithmeticOriginalStageClassToImage Ω a ha L) s
    exact (congrArg (fun z => p • z) hmap).symm.trans
      ((map_nsmul f.hom p _).symm.trans ((congrArg f hs).trans (map_zero f.hom)))
  letI : Algebra F M := (IntermediateField.inclusion hLM).toAlgebra
  letI : Module F M := Algebra.toModule
  letI : SMul F M := ((IntermediateField.inclusion hLM).toAlgebra).toSMul
  letI : IsScalarTower ℚ F M := IsScalarTower.of_algHom (IntermediateField.inclusion hLM)
  let g := groupCohomology.map (AlgEquiv.restrictNormalHom F : Gal(M/ℚ) →* Gal(F/ℚ))
    (arithmeticClassesModOutsideFiniteTransition ℚ Ω a ha F M hLM) 2
  have hmap := groupCohomology.H2π_comp_map_apply
    (AlgEquiv.restrictNormalHom F : Gal(M/ℚ) →* Gal(F/ℚ))
    (arithmeticClassesModOutsideFiniteTransition ℚ Ω a ha F M hLM)
    (arithmeticOriginalStageClassTwoCocycleToImage Ω a ha L s)
  exact (congrArg (fun z => p • z) hmap).symm.trans
    ((map_nsmul g.hom p _).symm.trans ((congrArg g hF).trans (map_zero g.hom)))

end
end Dubon2026
