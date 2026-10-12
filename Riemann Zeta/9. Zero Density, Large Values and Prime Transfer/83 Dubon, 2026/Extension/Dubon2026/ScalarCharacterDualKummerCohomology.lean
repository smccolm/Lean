import Dubon2026.ScalarCharacterDualKummerCoefficients
import Dubon2026.ContinuousCupAdditiveCoefficientEquiv
import Dubon2026.ContinuousCharacterDualCupNaturality
import Mathlib.Topology.Instances.ZMod

/-! # Original scalar character-dual cohomology and Kummer cohomology

The actual additive coefficient identifications induce genuine H1/H2
equivalences. Their exact cup comparison connects the split-module scalar
premise directly to the original Kummer pairing needed for DUB-17.
-/

namespace Dubon2026
noncomputable section

attribute [local instance] characterDualSequenceContinuousSMul

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (q : ℕ) [Fact q.Prime] (χ : Gal(Ω/K) →* ZMod q) (hχ : Continuous χ)
  (e : coefficientCharacterRep χ ≃+ galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)
  (heρ : ∀ g a, e ((coefficientCharacterRep χ).ρ g a) =
    (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q).ρ g (e a))
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
  [TopologicalSpace (characterDualCoefficientRep (coefficientCharacterRep (1 : Gal(Ω/K) →* ZMod q)) χ)]
  [DiscreteTopology (characterDualCoefficientRep (coefficientCharacterRep (1 : Gal(Ω/K) →* ZMod q)) χ)]

/-- The actual prime-field trivial H1 is the same original integer-linear
trivial H1, through the identity on the original coefficient group. -/
def scalarTrivialLineH1IntegerEquiv :
    ContinuousRepresentationH1 (coefficientCharacterRep (1 : Gal(Ω/K) →* ZMod q))
      (coefficientCharacterAction_continuous (1 : Gal(Ω/K) →* ZMod q) continuous_const) ≃+
    ContinuousRepresentationH1 (Rep.of (1 : Representation ℤ Gal(Ω/K) (ZMod q))) continuous_snd :=
  continuousH1AdditiveCoefficientEquiv _ _ (AddEquiv.refl (ZMod q))
    continuous_of_discreteTopology continuous_of_discreteTopology (fun _ a => one_mul a) _ _

/-- The original scalar character-dual H1 is identified with the original
Kummer root H1, preserving its actual coefficient map and Galois action. -/
def scalarCharacterDualH1RootEquiv :
    ContinuousRepresentationH1
      (characterDualCoefficientRep (coefficientCharacterRep (1 : Gal(Ω/K) →* ZMod q)) χ)
      (finiteCharacterDualAction_continuous (coefficientCharacterRep (1 : Gal(Ω/K) →* ZMod q)) χ
        (coefficientCharacterAction_continuous (1 : Gal(Ω/K) →* ZMod q) continuous_const) hχ) ≃+
      GaloisRootContinuousH1 (K := K) (Ω := Ω) q :=
  continuousH1AdditiveCoefficientEquiv _ _ (scalarCharacterDualRootCoefficientEquiv K Ω q χ e)
    continuous_of_discreteTopology continuous_of_discreteTopology
    (scalarCharacterDualRootCoefficientEquiv_equivariant K Ω q χ e heρ) _ _

/-- The same actual character-line identification transports the genuine cup
target to the original continuous root H2. -/
def scalarCharacterLineH2RootEquiv :
    ContinuousRepresentationH2 (coefficientCharacterRep χ)
      (coefficientCharacterAction_continuous χ hχ) ≃+
      GaloisRootContinuousH2 (K := K) (Ω := Ω) q :=
  continuousH2AdditiveCoefficientEquiv _ _ e continuous_of_discreteTopology
    continuous_of_discreteTopology heρ _ _

/-- The actual scalar dual cup becomes the original integer-linear Kummer
cup with its factors in the displayed order. No perfectness premise enters this comparison. -/
theorem scalarCharacterDualH1Cup_kummer
    (x : ContinuousRepresentationH1 (coefficientCharacterRep (1 : Gal(Ω/K) →* ZMod q))
      (coefficientCharacterAction_continuous (1 : Gal(Ω/K) →* ZMod q) continuous_const))
    (y : ContinuousRepresentationH1
      (characterDualCoefficientRep (coefficientCharacterRep (1 : Gal(Ω/K) →* ZMod q)) χ)
      (finiteCharacterDualAction_continuous (coefficientCharacterRep (1 : Gal(Ω/K) →* ZMod q)) χ
        (coefficientCharacterAction_continuous (1 : Gal(Ω/K) →* ZMod q) continuous_const) hχ)) :
    scalarCharacterLineH2RootEquiv K Ω q χ hχ e heρ
      (continuousCharacterDualH1Cup (coefficientCharacterRep (1 : Gal(Ω/K) →* ZMod q)) χ hχ
        (coefficientCharacterAction_continuous (1 : Gal(Ω/K) →* ZMod q) continuous_const) x y) =
      continuousH1Cup (Rep.of (1 : Representation ℤ Gal(Ω/K) (ZMod q)))
        (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)
        (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)
        (galoisRootExponentPairing q).flip
        (fun g a b => galoisRootExponentPairing_equivariant q g b a)
        continuous_of_discreteTopology continuous_snd (discreteGaloisRootAction_continuous q)
        (discreteGaloisRootAction_continuous q)
        (scalarTrivialLineH1IntegerEquiv K Ω q x)
        (scalarCharacterDualH1RootEquiv K Ω q χ hχ e heρ y) := by
  exact continuousH1Cup_additiveCoefficientEquiv
    (coefficientCharacterRep (1 : Gal(Ω/K) →* ZMod q))
    (characterDualCoefficientRep (coefficientCharacterRep (1 : Gal(Ω/K) →* ZMod q)) χ)
    (coefficientCharacterRep χ)
    (Rep.of (1 : Representation ℤ Gal(Ω/K) (ZMod q)))
    (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)
    (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)
    (AddEquiv.refl (ZMod q)) continuous_of_discreteTopology continuous_of_discreteTopology
    (fun _ a => one_mul a)
    (scalarCharacterDualRootCoefficientEquiv K Ω q χ e) continuous_of_discreteTopology
    continuous_of_discreteTopology (scalarCharacterDualRootCoefficientEquiv_equivariant K Ω q χ e heρ)
    e continuous_of_discreteTopology continuous_of_discreteTopology heρ
    (characterDualEvaluation (coefficientCharacterRep (1 : Gal(Ω/K) →* ZMod q)) χ)
    (galoisRootExponentPairing q).flip
    (characterDualEvaluation_equivariant (coefficientCharacterRep (1 : Gal(Ω/K) →* ZMod q)) χ)
    (fun g a b => galoisRootExponentPairing_equivariant q g b a)
    continuous_of_discreteTopology continuous_of_discreteTopology
    (scalarCharacterDualRootCoefficient_pairing K Ω q χ e) _ _ _ _ _ _ x y

end
end Dubon2026
