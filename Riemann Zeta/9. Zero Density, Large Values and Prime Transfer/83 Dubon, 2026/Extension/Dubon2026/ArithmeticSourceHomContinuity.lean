import Dubon2026.ArithmeticSourceHomExactSequence
import Dubon2026.FiniteSourceHomActionContinuity

/-! # Continuous actions on the original arithmetic source Hom sequence

The original ES, JS and CS actions are already proved continuous. Applying
the finite-source Hom continuity argument supplies the three continuous
Hom actions required to use the existing continuous cohomology exactness
theorems with this actual arithmetic sequence. Only the original source
coefficient action is an input; no target-action premise is retained.
-/

namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance 1100] Rep.hV2

variable (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
  (a : 𝓞 K) (ha : a ≠ 0)
  [DecidableEq (FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  (A : Rep.{0} ℤ Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K))

/-- Original S-unit-valued Hom with its literal conjugate arithmetic action. -/
abbrev arithmeticSourceSUnitHomRep :=
  (CategoryTheory.ihom A).obj (originalArithmeticSUnitRepresentation K Ω a ha)

/-- Original source-idele-valued Hom with its literal conjugate arithmetic action. -/
abbrev arithmeticSourceIdeleHomRep :=
  (CategoryTheory.ihom A).obj (arithmeticSPlaceColimitRep K Ω a ha)

/-- Original source-class-valued Hom with its literal conjugate arithmetic action. -/
abbrev arithmeticSourceClassHomRep :=
  (CategoryTheory.ihom A).obj (arithmeticSPlaceClassColimitRep K Ω a ha)

variable [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  (hA : Continuous (fun z : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) × A => A.ρ z.1 z.2))

include hA in
omit [DecidableEq (FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))] in
/-- The original finite coefficient action gives continuous arithmetic S-unit-valued Hom, using the derived ES action. -/
theorem arithmeticSourceSUnitHomAction_continuous
    [TopologicalSpace (arithmeticSourceSUnitHomRep K Ω a ha A)]
    [DiscreteTopology (arithmeticSourceSUnitHomRep K Ω a ha A)] :
    Continuous (fun z : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) ×
        arithmeticSourceSUnitHomRep K Ω a ha A =>
      (arithmeticSourceSUnitHomRep K Ω a ha A).ρ z.1 z.2) := by
  letI : TopologicalSpace (originalArithmeticSUnitRepresentation K Ω a ha) := ⊥
  letI : DiscreteTopology (originalArithmeticSUnitRepresentation K Ω a ha) := ⟨rfl⟩
  exact finiteSourceHomAction_continuous A (originalArithmeticSUnitRepresentation K Ω a ha)
    hA (originalArithmeticSUnitAction_continuous K Ω a ha)

include hA in
/-- The original finite coefficient action gives continuous source-idele-valued Hom, using the derived JS colimit action. -/
theorem arithmeticSourceIdeleHomAction_continuous
    [TopologicalSpace (arithmeticSourceIdeleHomRep K Ω a ha A)]
    [DiscreteTopology (arithmeticSourceIdeleHomRep K Ω a ha A)] :
    Continuous (fun z : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) ×
        arithmeticSourceIdeleHomRep K Ω a ha A =>
      (arithmeticSourceIdeleHomRep K Ω a ha A).ρ z.1 z.2) := by
  letI : TopologicalSpace (arithmeticSPlaceColimitRep K Ω a ha) := ⊥
  letI : DiscreteTopology (arithmeticSPlaceColimitRep K Ω a ha) := ⟨rfl⟩
  exact finiteSourceHomAction_continuous A (arithmeticSPlaceColimitRep K Ω a ha)
    hA (arithmeticSPlaceColimitAction_continuous K Ω a ha)

include hA in
/-- The original finite coefficient action gives continuous source-class-valued Hom, using the derived CS colimit action. -/
theorem arithmeticSourceClassHomAction_continuous
    [TopologicalSpace (arithmeticSourceClassHomRep K Ω a ha A)]
    [DiscreteTopology (arithmeticSourceClassHomRep K Ω a ha A)] :
    Continuous (fun z : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) ×
        arithmeticSourceClassHomRep K Ω a ha A =>
      (arithmeticSourceClassHomRep K Ω a ha A).ρ z.1 z.2) := by
  letI : TopologicalSpace (arithmeticSPlaceClassColimitRep K Ω a ha) := ⊥
  letI : DiscreteTopology (arithmeticSPlaceClassColimitRep K Ω a ha) := ⟨rfl⟩
  exact finiteSourceHomAction_continuous A (arithmeticSPlaceClassColimitRep K Ω a ha)
    hA (arithmeticSPlaceClassColimitAction_continuous K Ω a ha)

end
end Dubon2026
