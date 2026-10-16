import Dubon2026.ArithmeticOrbitPrimeCompletion
import Dubon2026.ArithmeticRelativeStageCocycles
import Dubon2026.OriginalFullIdeleCohomologySequence

/-! # Original cyclic class invariants at a relative arithmetic stage

Apply the existing original-object argument to an actual finite extension
which is Galois over its specified base. No normality over the rationals
is required. This is the auxiliary-stage interface needed by DUB-17's
class-generator transfer, with all local maps and scalar towers retained.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField

variable (a : 𝓞 ℚ)
  (F : IntermediateField ℚ (rationalUnramifiedExtension a))
  (H : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ H]
  (hFH : F ≤ H)

/-- The actual original full-idele H2 of the specified finite arithmetic extension. -/
def rationalArithmeticRelativeStageIdeleH2 : Type := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  exact ↥(groupCohomology (originalFullIdeleRep F H) 2)

/-- Retain the actual additive group structure on the original finite-stage full-idele cohomology. -/
local instance arithmeticRelativeStageIdeleAddCommGroup :
    AddCommGroup (rationalArithmeticRelativeStageIdeleH2 a F H hFH) := by
  dsimp only [rationalArithmeticRelativeStageIdeleH2]
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  infer_instance

/-- The genuine principal image of the original finite-stage cocycle class. -/
def rationalArithmeticRelativeStagePrincipalClass
    (y : rationalArithmeticRelativeStageCocycles a F H hFH) :
    rationalArithmeticRelativeStageIdeleH2 a F H hFH := by
  letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits F H) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits F H) := ⟨rfl⟩
  let z : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits F H) := y
  exact (groupCohomology.functor ℤ Gal(H/F) 2).map (originalFullPrincipalRepHom F H)
    (groupCohomology.H2π (Rep.ofAlgebraAutOnUnits F H) z.val)

/-- The named principal class is definitionally the original principal-inclusion map on the same finite global cocycle. -/
theorem rationalArithmeticRelativeStagePrincipalClass_eq
    (y : rationalArithmeticRelativeStageCocycles a F H hFH) :
    letI : Algebra F H := (IntermediateField.inclusion hFH).toAlgebra
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits F H) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits F H) := ⟨rfl⟩
    let z : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits F H) := y
    rationalArithmeticRelativeStagePrincipalClass a F H hFH y =
      (groupCohomology.functor ℤ Gal(H/F) 2).map (originalFullPrincipalRepHom F H)
        (groupCohomology.H2π (Rep.ofAlgebraAutOnUnits F H) z.val) := rfl

end
end Dubon2026
