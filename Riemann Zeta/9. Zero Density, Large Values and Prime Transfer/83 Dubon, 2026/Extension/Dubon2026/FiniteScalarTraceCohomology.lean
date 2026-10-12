import Dubon2026.FiniteScalarTraceDuality
import Dubon2026.ContinuousCharacterDualH2Naturality
import Dubon2026.ContinuousH1AdditiveCoefficientEquiv
import Dubon2026.ContinuousH2AdditiveCoefficientEquiv

/-! # The actual field-trace comparison on original continuous cohomology

The original coefficient action is unchanged under prime-field restriction.
The genuine trace-dual equivalence supplies its H1 comparison, while the
actual scalar trace induces the H2 map. These are the cohomological maps
needed to transfer proved prime-field nondegeneracy to the original finite
extension-field cup in DUB-17's trace-zero local pairing.
-/

namespace Dubon2026
noncomputable section

attribute [local instance] finiteScalarPrimeModule characterDualSequenceContinuousSMul

variable {k G : Type} [Field k] [Finite k] [Group G]
  (q : ℕ) [Fact q.Prime] [CharP k q] [Algebra (ZMod q) k]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{0} k G) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))

/-- The original continuous H1 is unchanged as an additive group by the
existing prime-field restriction, with identical cocycle values and boundaries. -/
def finiteScalarPrimeH1Equiv : ContinuousRepresentationH1 A hA ≃+
    ContinuousRepresentationH1 (finiteScalarPrimeRep q A) hA :=
  continuousH1AdditiveCoefficientEquiv A (finiteScalarPrimeRep q A) (AddEquiv.refl A)
    continuous_id continuous_id (fun _ _ => rfl) _ _

variable (χ : G →* ZMod q) (hχ : Continuous χ)

omit [Finite k] [CharP k q] [DiscreteTopology k] [IsTopologicalRing k]
  [IsTopologicalGroup G] in
/-- Scalar extension of the original prime-field character is continuous
because its actual algebra map has discrete domain. -/
theorem finiteScalarCharacter_continuous (hχ : Continuous χ) :
    Continuous ((algebraMap (ZMod q) k).toMonoidHom.comp χ) :=
  (continuous_of_discreteTopology (f := algebraMap (ZMod q) k)).comp hχ

variable
  [TopologicalSpace (characterDualCoefficientRep A ((algebraMap (ZMod q) k).toMonoidHom.comp χ))]
  [DiscreteTopology (characterDualCoefficientRep A ((algebraMap (ZMod q) k).toMonoidHom.comp χ))]
  [TopologicalSpace (characterDualCoefficientRep (finiteScalarPrimeRep q A) χ)]
  [DiscreteTopology (characterDualCoefficientRep (finiteScalarPrimeRep q A) χ)]

/-- The actual field trace carries the original extension-field dual H1
bijectively to the genuine prime-field dual H1, through its proved action identity. -/
def finiteScalarTraceDualH1Equiv :
    ContinuousRepresentationH1
      (characterDualCoefficientRep A ((algebraMap (ZMod q) k).toMonoidHom.comp χ))
      (finiteCharacterDualAction_continuous A ((algebraMap (ZMod q) k).toMonoidHom.comp χ)
        hA (finiteScalarCharacter_continuous q χ hχ)) ≃+
    ContinuousRepresentationH1 (characterDualCoefficientRep (finiteScalarPrimeRep q A) χ)
      (finiteCharacterDualAction_continuous (finiteScalarPrimeRep q A) χ hA hχ) :=
  continuousH1AdditiveCoefficientEquiv _ _ (finiteScalarTraceDualEquiv q A χ)
    continuous_of_discreteTopology continuous_of_discreteTopology
    (finiteScalarTraceDualMap_equivariant q A χ) _ _

omit [Finite k] [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G] in
/-- The genuine scalar trace intertwines the original scalar-extended
character and the prime-field character on the same coefficient values. -/
theorem finiteScalarTraceCharacter_equivariant (g : G) (a : k) :
    Algebra.trace (ZMod q) k
      ((finiteScalarPrimeRep q (coefficientCharacterRep ((algebraMap (ZMod q) k).toMonoidHom.comp χ))).ρ g a) =
      (coefficientCharacterRep χ).ρ g (Algebra.trace (ZMod q) k a) := by
  change Algebra.trace (ZMod q) k (algebraMap (ZMod q) k (χ g) * a) =
    χ g * Algebra.trace (ZMod q) k a
  simpa only [Algebra.smul_def, smul_eq_mul] using (Algebra.trace (ZMod q) k).map_smul (χ g) a

/-- Actual scalar trace on original continuous H2, preserving its continuous
coboundary witnesses through the original coefficient maps. -/
def finiteScalarTraceCharacterH2Map :
    ContinuousRepresentationH2
      (coefficientCharacterRep ((algebraMap (ZMod q) k).toMonoidHom.comp χ))
      (coefficientCharacterAction_continuous _ (finiteScalarCharacter_continuous q χ hχ)) →+
    ContinuousRepresentationH2 (coefficientCharacterRep χ)
      (coefficientCharacterAction_continuous χ hχ) :=
  (continuousCoefficientH2Map
    (finiteScalarPrimeRep q (coefficientCharacterRep ((algebraMap (ZMod q) k).toMonoidHom.comp χ)))
    (coefficientCharacterRep χ)
    ((Algebra.trace (ZMod q) k).toAddMonoidHom.toZModLinearMap q)
    continuous_of_discreteTopology (finiteScalarTraceCharacter_equivariant q χ)
    (coefficientCharacterAction_continuous _ (finiteScalarCharacter_continuous q χ hχ))
    (coefficientCharacterAction_continuous χ hχ)).toAddMonoidHom.comp
    (continuousH2AdditiveCoefficientEquiv
      (coefficientCharacterRep ((algebraMap (ZMod q) k).toMonoidHom.comp χ))
      (finiteScalarPrimeRep q (coefficientCharacterRep ((algebraMap (ZMod q) k).toMonoidHom.comp χ)))
      (AddEquiv.refl k) continuous_id continuous_id (fun _ _ => rfl) _ _).toAddMonoidHom

end
end Dubon2026
