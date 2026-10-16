import Dubon2026.ArithmeticFiniteStageCocycles
import Dubon2026.OriginalFullIdeleCohomologySequence

/-! # The actual full-idele H2 at a finite arithmetic stage

Keep the fixed original finite-stage coefficient and its canonical field
inclusion named while the local prime varies. The principal class is the
literal existing cohomology map applied to the original finite cocycle.
This supplies the source of DUB-17's full-idele invariant sum; neither a
class invariant nor its descent is assumed.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra

variable (a : 𝓞 ℚ)
  (F : IntermediateField ℚ (rationalUnramifiedExtension a))
  (H : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a)) (hFH : F ≤ H.toIntermediateField)

/-- The actual original full-idele H2 of the specified finite arithmetic extension. -/
def rationalArithmeticFiniteStageIdeleH2 : Type := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  exact ↥(groupCohomology (originalFullIdeleRep F H) 2)

/-- Retain the actual additive group structure on the original finite-stage full-idele cohomology. -/
local instance arithmeticFiniteStageIdeleAddCommGroup :
    AddCommGroup (rationalArithmeticFiniteStageIdeleH2 a F H hFH) := by
  dsimp only [rationalArithmeticFiniteStageIdeleH2]
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  infer_instance

/-- The genuine principal image of the original finite-stage cocycle class. -/
def rationalArithmeticFiniteStagePrincipalClass
    (y : rationalArithmeticFiniteStageCocycles a F H hFH) :
    rationalArithmeticFiniteStageIdeleH2 a F H hFH := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits F H) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits F H) := ⟨rfl⟩
  let z : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits F H) := y
  exact (groupCohomology.functor ℤ Gal(H/F) 2).map (originalFullPrincipalRepHom F H)
    (groupCohomology.H2π (Rep.ofAlgebraAutOnUnits F H) z.val)

/-- The named principal class is definitionally the original principal-inclusion map on the same finite global cocycle. -/
theorem rationalArithmeticFiniteStagePrincipalClass_eq
    (y : rationalArithmeticFiniteStageCocycles a F H hFH) :
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits F H) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits F H) := ⟨rfl⟩
    let z : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits F H) := y
    rationalArithmeticFiniteStagePrincipalClass a F H hFH y =
      (groupCohomology.functor ℤ Gal(H/F) 2).map (originalFullPrincipalRepHom F H)
        (groupCohomology.H2π (Rep.ofAlgebraAutOnUnits F H) z.val) := rfl

end
end Dubon2026
