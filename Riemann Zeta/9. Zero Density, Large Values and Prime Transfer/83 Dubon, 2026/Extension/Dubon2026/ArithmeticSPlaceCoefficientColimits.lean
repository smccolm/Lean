import Dubon2026.ArithmeticSPlaceDirectedSystems
import Dubon2026.ArithmeticSUnitCoefficientColimit

/-! # Original source coefficient colimits and their actual maps

The genuine finite-stage diagonal and quotient squares induce the ES-to-JS
and JS-to-CS maps on the original fixed-support directed limits. These maps
are required for the source arithmetic exact sequence in DUB-17 duality.
-/

namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance 1100] Rep.hV2

variable (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
  (a : 𝓞 K) (ha : a ≠ 0)
  [DecidableEq (FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))]

/-- The actual source S-place idele coefficient colimit at the fixed exceptional support. -/
abbrev ArithmeticSPlaceColimit :=
  Module.DirectLimit (fun F => ArithmeticSPlaceFiniteStageRep K Ω a ha F)
    (arithmeticSPlaceTransitionMap K Ω a ha)

/-- The actual source S-place class coefficient colimit, using its original quotient transitions. -/
abbrev ArithmeticSPlaceClassColimit :=
  Module.DirectLimit (fun F => ArithmeticSPlaceClassFiniteStageRep K Ω a ha F)
    (arithmeticSPlaceClassTransitionMap K Ω a ha)

omit [DecidableEq (FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))] in
private theorem principal_transition
    (E F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (hEF : E ≤ F) :
    (arithmeticSPlaceFiniteStagePrincipal K Ω a ha F).hom.toLinearMap.comp
      (arithmeticSUnitCoefficientTransition K Ω a ha E F hEF) =
        (arithmeticSPlaceTransitionMap K Ω a ha E F hEF).comp
          (arithmeticSPlaceFiniteStagePrincipal K Ω a ha E).hom.toLinearMap := by
  letI : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
  apply LinearMap.ext
  intro x
  exact (arithmeticSPlaceFiniteTransition_principal K Ω a ha E F hEF x).symm

omit [DecidableEq (FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))] in
private theorem quotient_transition
    (E F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (hEF : E ≤ F) :
    (arithmeticSPlaceFiniteStageQuotient K Ω a ha F).hom.toLinearMap.comp
      (arithmeticSPlaceTransitionMap K Ω a ha E F hEF) =
        (arithmeticSPlaceClassTransitionMap K Ω a ha E F hEF).comp
          (arithmeticSPlaceFiniteStageQuotient K Ω a ha E).hom.toLinearMap := by
  letI : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
  apply LinearMap.ext
  intro x
  exact (arithmeticSPlaceClassFiniteTransition_quotient K Ω a ha E F hEF x).symm

/-- The original finite-stage diagonal inclusions induce the actual source colimit map. -/
def arithmeticSPlaceColimitPrincipal :
    ArithmeticSUnitCoefficientColimit K Ω a ha →ₗ[ℤ] ArithmeticSPlaceColimit K Ω a ha :=
  Module.DirectLimit.map (fun F => (arithmeticSPlaceFiniteStagePrincipal K Ω a ha F).hom.toLinearMap)
    (principal_transition K Ω a ha)

/-- The original finite-stage class quotients induce the actual source colimit quotient map. -/
def arithmeticSPlaceColimitQuotient :
    ArithmeticSPlaceColimit K Ω a ha →ₗ[ℤ] ArithmeticSPlaceClassColimit K Ω a ha :=
  Module.DirectLimit.map (fun F => (arithmeticSPlaceFiniteStageQuotient K Ω a ha F).hom.toLinearMap)
    (quotient_transition K Ω a ha)

/-- The actual colimit diagonal preserves the original finite-stage S-unit representative. -/
theorem arithmeticSPlaceColimitPrincipal_of
    (F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (x : arithmeticSUnitFiniteStageRep K Ω a ha F) :
    arithmeticSPlaceColimitPrincipal K Ω a ha
      (Module.DirectLimit.of ℤ
        (FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
        (fun F => arithmeticSUnitFiniteStageRep K Ω a ha F)
        (arithmeticSUnitCoefficientTransition K Ω a ha) F x) =
      Module.DirectLimit.of ℤ
        (FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
        (fun F => ArithmeticSPlaceFiniteStageRep K Ω a ha F)
        (arithmeticSPlaceTransitionMap K Ω a ha) F
        ((arithmeticSPlaceFiniteStagePrincipal K Ω a ha F).hom x) :=
  Module.DirectLimit.map_apply_of
    (fun F => (arithmeticSPlaceFiniteStagePrincipal K Ω a ha F).hom.toLinearMap)
    (principal_transition K Ω a ha) x

/-- The actual colimit quotient preserves the original source finite-stage idele representative. -/
theorem arithmeticSPlaceColimitQuotient_of
    (F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (x : ArithmeticSPlaceFiniteStageRep K Ω a ha F) :
    arithmeticSPlaceColimitQuotient K Ω a ha
      (Module.DirectLimit.of ℤ
        (FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
        (fun F => ArithmeticSPlaceFiniteStageRep K Ω a ha F)
        (arithmeticSPlaceTransitionMap K Ω a ha) F x) =
      Module.DirectLimit.of ℤ
        (FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
        (fun F => ArithmeticSPlaceClassFiniteStageRep K Ω a ha F)
        (arithmeticSPlaceClassTransitionMap K Ω a ha) F
        ((arithmeticSPlaceFiniteStageQuotient K Ω a ha F).hom x) :=
  Module.DirectLimit.map_apply_of
    (fun F => (arithmeticSPlaceFiniteStageQuotient K Ω a ha F).hom.toLinearMap)
    (quotient_transition K Ω a ha) x

end
end Dubon2026
