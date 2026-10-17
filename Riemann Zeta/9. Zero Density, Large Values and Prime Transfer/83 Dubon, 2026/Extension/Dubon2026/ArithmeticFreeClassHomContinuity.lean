import Dubon2026.ArithmeticFreeClassHomCocycle
import Dubon2026.OriginalInternalHomActionContinuity
import Dubon2026.ArithmeticFiniteStageActionContinuity
/-! # Continuity of the actual free-cover full-class Hom action

The finite coefficient and finite Galois stage make the original free cover
a finite integer lattice. Its proved action and original full-class action
therefore give continuous Hom evaluation, needed for DUB-17 cup adjunction.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2
variable (Ω : Type) [Field Ω] [Algebra ℚ Ω] (a : 𝓞 ℚ) (ha : a ≠ 0)

/-- Retain the original union's displayed rational inclusion. -/
local instance freeClassContinuityUnionAlgebra : Algebra ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a) :=
  (originalUnramifiedGaloisUnion (Ω := Ω) a).algebra'

variable [DecidableEq (FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  (P : FiniteGaloisIntermediateField ℚ (originalUnramifiedGaloisUnion (Ω := Ω) a))

/-- Retain the original finite stage's displayed rational inclusion. -/
local instance freeClassContinuityStageAlgebra : Algebra ℚ P := P.algebra'

variable (B : Rep.{0} ℤ Gal(P/ℚ))

variable [TopologicalSpace (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [DiscreteTopology (arithmeticClassesModOutsideColimitRep ℚ Ω a ha)]
  [TopologicalSpace (arithmeticRelationFreeClassHom Ω a ha P B)]
  [DiscreteTopology (arithmeticRelationFreeClassHom Ω a ha P B)]

/-- The full-class action on the original finite-stage free-cover Hom is
continuous, using the original Krull topology and derived finite generation. -/
theorem arithmeticRelationFreeClassHomAction_continuous [Finite B] :
    Continuous (fun z : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ) ×
      arithmeticRelationFreeClassHom Ω a ha P B =>
        (arithmeticRelationFreeClassHom Ω a ha P B).ρ z.1 z.2) := by
  let π : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / ℚ) →* Gal(P/ℚ) :=
    AlgEquiv.restrictNormalHom P
  let A := Rep.res π (Rep.free ℤ Gal(P/ℚ) B)
  let D := arithmeticClassesModOutsideColimitRep ℚ Ω a ha
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  letI : FiniteDimensional ℚ P := P.finiteDimensional
  letI : Module.Finite ℤ (Gal(P/ℚ) →₀ ℤ) := Module.Finite.finsupp
  letI : Module.Finite ℤ A := by
    change Module.Finite ℤ (B →₀ Gal(P/ℚ) →₀ ℤ)
    exact Module.Finite.finsupp
  exact originalInternalHomAction_continuous_of_finiteGenerated A D
    (arithmeticFiniteStageRepresentationAction_continuous ℚ Ω a P (Rep.free ℤ Gal(P/ℚ) B))
    (arithmeticClassesModOutsideColimitAction_continuous ℚ Ω a ha)

end
end Dubon2026
