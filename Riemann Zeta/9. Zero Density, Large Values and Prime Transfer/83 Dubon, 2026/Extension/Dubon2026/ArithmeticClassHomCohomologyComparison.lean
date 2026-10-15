import Dubon2026.ArithmeticSourceClassHomComparison
import Dubon2026.ContinuousH1AdditiveCoefficientEquiv
import Dubon2026.ContinuousH2AdditiveCoefficientEquiv

/-! # Actual continuous cohomology under the prime-field class Hom comparison

The original Hom comparison transports continuous cocycles and coboundaries
pointwise. Its full-class action is continuous by finite source evaluation.
These H1/H2 comparisons are the class-coefficient edge of the DUB-17 duality
route; class formation, Ext and local restriction identifications remain.
-/

namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance 1100] Rep.hV2

variable (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
  (a : 𝓞 K) (ha : a ≠ 0)
  [DecidableEq (FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  (A : Rep.{0} ℤ Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K))
  [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  (hA : Continuous (fun z : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) × A => A.ρ z.1 z.2))
  [TopologicalSpace (arithmeticFullClassHomRep K Ω a ha A)]
  [DiscreteTopology (arithmeticFullClassHomRep K Ω a ha A)]

include hA in
/-- The actual full-class Hom conjugate action is continuous, derived from its original coefficient action. -/
theorem arithmeticFullClassHomAction_continuous :
    Continuous (fun z : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K) ×
        arithmeticFullClassHomRep K Ω a ha A =>
      (arithmeticFullClassHomRep K Ω a ha A).ρ z.1 z.2) := by
  letI : TopologicalSpace (arithmeticClassesModOutsideColimitRep K Ω a ha) := ⊥
  letI : DiscreteTopology (arithmeticClassesModOutsideColimitRep K Ω a ha) := ⟨rfl⟩
  exact finiteSourceHomAction_continuous A (arithmeticClassesModOutsideColimitRep K Ω a ha)
    hA (arithmeticClassesModOutsideColimitAction_continuous K Ω a ha)

variable [IsAlgClosure K Ω] (q : ℕ) [Fact q.Prime] [Module (ZMod q) A]
  (hqa : (q : 𝓞 K) ∣ a)
  [TopologicalSpace (arithmeticSourceClassHomRep K Ω a ha A)]
  [DiscreteTopology (arithmeticSourceClassHomRep K Ω a ha A)]

/-- The original coefficient structure used in this comparison. -/
local instance classHomComparisonSourceSMul : @ContinuousSMul ℤ (arithmeticSourceClassHomRep K Ω a ha A)
    (arithmeticSourceClassHomRep K Ω a ha A).hV2.toSMul inferInstance inferInstance :=
  ⟨continuous_of_discreteTopology⟩
/-- The original coefficient structure used in this comparison. -/
local instance classHomComparisonTargetSMul : @ContinuousSMul ℤ (arithmeticFullClassHomRep K Ω a ha A)
    (arithmeticFullClassHomRep K Ω a ha A).hV2.toSMul inferInstance inferInstance :=
  ⟨continuous_of_discreteTopology⟩

/-- The original postcomposition map as an actual additive equivalence on prime-field Hom. -/
def arithmeticSourceClassHomAddEquiv :
    arithmeticSourceClassHomRep K Ω a ha A ≃+ arithmeticFullClassHomRep K Ω a ha A :=
  (LinearEquiv.ofBijective (arithmeticSourceClassHomComparison K Ω a ha A).hom.toLinearMap
    ⟨arithmeticSourceClassHomComparison_injective K Ω a ha A,
      arithmeticSourceClassHomComparison_surjective K Ω a ha A q hqa⟩).toAddEquiv

omit [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  [TopologicalSpace (arithmeticFullClassHomRep K Ω a ha A)]
  [DiscreteTopology (arithmeticFullClassHomRep K Ω a ha A)]
  [TopologicalSpace (arithmeticSourceClassHomRep K Ω a ha A)]
  [DiscreteTopology (arithmeticSourceClassHomRep K Ω a ha A)] in
private theorem classHom_equivariant
    (g : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K))
    (x : arithmeticSourceClassHomRep K Ω a ha A) :
    arithmeticSourceClassHomAddEquiv K Ω a ha A q hqa
      ((arithmeticSourceClassHomRep K Ω a ha A).ρ g x) =
        (arithmeticFullClassHomRep K Ω a ha A).ρ g
          (arithmeticSourceClassHomAddEquiv K Ω a ha A q hqa x) :=
  Rep.hom_comm_apply (arithmeticSourceClassHomComparison K Ω a ha A) g x

/-- Original continuous source-class Hom H1 is the actual full-class Hom H1 for prime-field coefficients. -/
def arithmeticSourceClassHomH1Equiv :
    ContinuousRepresentationH1 (arithmeticSourceClassHomRep K Ω a ha A)
      (arithmeticSourceClassHomAction_continuous K Ω a ha A hA) ≃+
    ContinuousRepresentationH1 (arithmeticFullClassHomRep K Ω a ha A)
      (arithmeticFullClassHomAction_continuous K Ω a ha A hA) :=
  continuousH1AdditiveCoefficientEquiv _ _ (arithmeticSourceClassHomAddEquiv K Ω a ha A q hqa)
    continuous_of_discreteTopology continuous_of_discreteTopology
    (classHom_equivariant K Ω a ha A q hqa) _ _

/-- Original continuous source-class Hom H2 is the actual full-class Hom H2 for the same coefficients. -/
def arithmeticSourceClassHomH2Equiv :
    ContinuousRepresentationH2 (arithmeticSourceClassHomRep K Ω a ha A)
      (arithmeticSourceClassHomAction_continuous K Ω a ha A hA) ≃+
    ContinuousRepresentationH2 (arithmeticFullClassHomRep K Ω a ha A)
      (arithmeticFullClassHomAction_continuous K Ω a ha A hA) :=
  continuousH2AdditiveCoefficientEquiv _ _ (arithmeticSourceClassHomAddEquiv K Ω a ha A q hqa)
    continuous_of_discreteTopology continuous_of_discreteTopology
    (classHom_equivariant K Ω a ha A q hqa) _ _

/-- Every original H1 cocycle is transported by the literal source-to-full-class coefficient map. -/
theorem arithmeticSourceClassHomH1Equiv_mk
    (c : continuousRepresentationCocyclesOne (arithmeticSourceClassHomRep K Ω a ha A)) :
    arithmeticSourceClassHomH1Equiv K Ω a ha A hA q hqa (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (continuousCocycleOneAdditiveEquiv _ _
        (arithmeticSourceClassHomAddEquiv K Ω a ha A q hqa)
        continuous_of_discreteTopology continuous_of_discreteTopology
        (classHom_equivariant K Ω a ha A q hqa) c) := rfl

/-- Every original H2 cocycle retains the same pointwise class-comparison values. -/
theorem arithmeticSourceClassHomH2Equiv_mk
    (c : continuousRepresentationCocyclesTwo (arithmeticSourceClassHomRep K Ω a ha A)) :
    arithmeticSourceClassHomH2Equiv K Ω a ha A hA q hqa (Submodule.Quotient.mk c) =
      Submodule.Quotient.mk (continuousCocycleTwoAdditiveEquiv _ _
        (arithmeticSourceClassHomAddEquiv K Ω a ha A q hqa)
        continuous_of_discreteTopology continuous_of_discreteTopology
        (classHom_equivariant K Ω a ha A q hqa) c) := rfl

end
end Dubon2026
