import Dubon2026.FiniteScalarTraceCohomology
import Dubon2026.ContinuousCharacterDualH2Pairing

/-! # Actual field trace preserves the original H2/invariant pairing

The genuine trace-dual coefficient equivalence identifies original H2,
while prime-field restriction retains the same invariant coefficients.
Pointwise evaluation proves their original endpoint pairing identity. This
transfers the proved prime-field H0/H2 duality required in DUB-17's global
duality sequence to the actual finite extension-field coefficients.
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
  (χ : G →* ZMod q) (hχ : Continuous χ)
  [TopologicalSpace (characterDualCoefficientRep A ((algebraMap (ZMod q) k).toMonoidHom.comp χ))]
  [DiscreteTopology (characterDualCoefficientRep A ((algebraMap (ZMod q) k).toMonoidHom.comp χ))]
  [TopologicalSpace (characterDualCoefficientRep (finiteScalarPrimeRep q A) χ)]
  [DiscreteTopology (characterDualCoefficientRep (finiteScalarPrimeRep q A) χ)]

/-- Prime-field restriction keeps exactly the original invariant coefficients. -/
def finiteScalarPrimeInvariantEquiv : A.ρ.invariants ≃+ (finiteScalarPrimeRep q A).ρ.invariants :=
  AddEquiv.refl _

/-- Actual field-trace duality induces an equivalence on the original
continuous H2 quotients, preserving the genuine coefficient actions. -/
def finiteScalarTraceDualH2Equiv :
    ContinuousRepresentationH2
      (characterDualCoefficientRep A ((algebraMap (ZMod q) k).toMonoidHom.comp χ))
      (finiteCharacterDualAction_continuous A ((algebraMap (ZMod q) k).toMonoidHom.comp χ)
        hA (finiteScalarCharacter_continuous q χ hχ)) ≃+
    ContinuousRepresentationH2 (characterDualCoefficientRep (finiteScalarPrimeRep q A) χ)
      (finiteCharacterDualAction_continuous (finiteScalarPrimeRep q A) χ hA hχ) :=
  continuousH2AdditiveCoefficientEquiv _ _ (finiteScalarTraceDualEquiv q A χ)
    continuous_of_discreteTopology continuous_of_discreteTopology
    (finiteScalarTraceDualMap_equivariant q A χ) _ _

/-- Field trace of the actual original H2/invariant pairing equals the
prime-field pairing of the genuine trace-dual class and the same invariant. -/
theorem finiteScalarTraceCharacterH2Map_invariantPairing
    (x : ContinuousRepresentationH2
      (characterDualCoefficientRep A ((algebraMap (ZMod q) k).toMonoidHom.comp χ))
      (finiteCharacterDualAction_continuous A ((algebraMap (ZMod q) k).toMonoidHom.comp χ)
        hA (finiteScalarCharacter_continuous q χ hχ))) (w : A.ρ.invariants) :
    finiteScalarTraceCharacterH2Map q χ hχ
      (continuousCharacterDualH2InvariantPairing A ((algebraMap (ZMod q) k).toMonoidHom.comp χ)
        (finiteScalarCharacter_continuous q χ hχ) hA x w) =
      continuousCharacterDualH2InvariantPairing (finiteScalarPrimeRep q A) χ hχ hA
        (finiteScalarTraceDualH2Equiv q A hA χ hχ x) (finiteScalarPrimeInvariantEquiv q A w) := by
  induction x using Submodule.Quotient.induction_on with
  | _ c => rfl

end
end Dubon2026
