import Dubon2026.ArithmeticClassesModOutsideH1
import Dubon2026.OriginalClassesModOutsideCyclicH2

/-! # Exact cyclic H2 at the original rational arithmetic stages

The original unramified-union theorem discharges the fixed-support local
hypothesis. The actual quotient induces a bijection on H2 and preserves
the degree cardinality, supplying the cyclic finite-stage class-formation
input on DUB-17's global localization exactness route.
-/

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField

variable (Ω : Type) [Field Ω] [Algebra ℚ Ω]
  (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- The original field inclusion supplies the rational algebra structure used in this comparison. -/
local instance classCyclicH2UnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

variable (F : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))

/-- The original field inclusion supplies the rational algebra structure used in this comparison. -/
local instance classCyclicH2StageAlgebra : Algebra ℚ F := F.algebra'
/-- The original finite arithmetic extension is a number field. -/
local instance classCyclicH2StageNumberField : NumberField F := NumberField.of_module_finite ℚ F

variable [IsCyclic Gal(F/ℚ)]

/-- Every original quotient H2 class at an actual cyclic arithmetic stage has a unique full-class H2 preimage. -/
theorem rationalArithmeticClassesModOutsideStage_H2_unique_lift
    (x : groupCohomology (arithmeticClassesModOutsideStageRep ℚ Ω a ha F) 2) :
    ∃! y : groupCohomology (originalIdeleClassRep ℚ F) 2,
      (groupCohomology.functor ℤ Gal(F/ℚ) 2).map
        (originalIdeleClassesModOutsideRepHom ℚ F
          (arithmeticSUnitFiniteStageSupport ℚ Ω a ha F)
          (originalExceptionalIntegerSupport_galoisStable F ℚ a ha)) y = x := by
  let e := (originalClassesModOutsideCyclicH2Iso ℚ F
    (arithmeticSUnitFiniteStageSupport ℚ Ω a ha F)
    (originalExceptionalIntegerSupport_galoisStable F ℚ a ha)
    (rationalArithmeticFiniteStage_outside_unramified Ω a ha F)).toLinearEquiv
  exact ⟨e.symm x, e.apply_symm_apply x, fun y hy => e.injective (hy.trans (e.apply_symm_apply x).symm)⟩

/-- The literal quotient's H2 at an actual cyclic arithmetic stage is finite of order equal to its field degree. -/
theorem rationalArithmeticClassesModOutsideStage_cyclic_second_card :
    Finite (groupCohomology (arithmeticClassesModOutsideStageRep ℚ Ω a ha F) 2) ∧
      Nat.card (groupCohomology (arithmeticClassesModOutsideStageRep ℚ Ω a ha F) 2) =
        Module.finrank ℚ F :=
  originalClassesModOutside_cyclic_second_card ℚ F _ _
    (rationalArithmeticFiniteStage_outside_unramified Ω a ha F)

end
end Dubon2026
