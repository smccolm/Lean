import Dubon2026.ArithmeticRootLocalMap
import Dubon2026.ArithmeticCyclotomicCohomologyRestriction

/-! # Compatible original root cohomology under arithmetic restriction

Restrict the genuine global root cocycles and then apply the actual root
embedding. The square with the original cyclotomic H2 restriction commutes.
This is the cohomological normalization edge needed before DUB-17's global
sum-of-local-invariants theorem, which remains a separate obligation.
-/

namespace Dubon2026
noncomputable section
open scoped NumberField

variable (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a)
  (p : ℕ) (hp : p.Prime)

/-- Use the original rational algebra in the arithmetic root cohomology. -/
local instance arithmeticRootH2Algebra : Algebra ℚ (rationalUnramifiedExtension a) :=
  (rationalUnramifiedExtension a).algebra'

variable [TopologicalSpace (rationalArithmeticRootRepresentation a q)]
  [DiscreteTopology (rationalArithmeticRootRepresentation a q)]
  [TopologicalSpace (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]

local instance arithmeticGlobalRootContinuousSMul :
    @ContinuousSMul ℤ (rationalArithmeticRootRepresentation a q)
      (rationalArithmeticRootRepresentation a q).hV2.toSMul inferInstance inferInstance :=
  ⟨continuous_of_discreteTopology⟩

omit [Fact q.Prime] in
/-- Continuity of the genuine global root action follows from the original
Krull topology and the already proved discrete Galois root action. -/
theorem rationalArithmeticRootAction_continuous :
    Continuous (fun z : rationalArithmeticGaloisGroup a ×
      rationalArithmeticRootRepresentation a q =>
        (rationalArithmeticRootRepresentation a q).ρ z.1 z.2) := by
  letI : IsGalois ℚ (rationalUnramifiedExtension a) := originalUnramifiedGaloisUnion_isGalois a
  letI : TopologicalSpace (galoisRootOfUnityRepresentation
      (K := ℚ) (Ω := rationalUnramifiedExtension a) q) :=
    inferInstanceAs (TopologicalSpace (rationalArithmeticRootRepresentation a q))
  letI : DiscreteTopology (galoisRootOfUnityRepresentation
      (K := ℚ) (Ω := rationalUnramifiedExtension a) q) :=
    inferInstanceAs (DiscreteTopology (rationalArithmeticRootRepresentation a q))
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits ℚ (rationalUnramifiedExtension a)) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits ℚ (rationalUnramifiedExtension a)) := ⟨rfl⟩
  exact discreteGaloisRootAction_continuous
    (K := ℚ) (Ω := rationalUnramifiedExtension a) q

/-- The original global cyclotomic H2 identifies with genuine global root
H2 by the single compatible primitive root, retaining continuous witnesses. -/
def rationalArithmeticCyclotomicH2RootEquiv :
    ContinuousRepresentationH2 (coefficientCharacterRep
      (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom)
      (coefficientCharacterAction_continuous _
        (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).continuous) ≃+
    ContinuousRepresentationH2 (rationalArithmeticRootRepresentation a q)
      (rationalArithmeticRootAction_continuous a q) :=
  continuousH2AdditiveCoefficientEquiv _ _
    (rationalArithmeticRootCoefficientEquiv a q hqa)
    continuous_of_discreteTopology continuous_of_discreteTopology
    (rationalArithmeticRootCoefficientEquiv_equivariant a q hqa) _ _

/-- The local cyclotomic H2 uses the image of the same global primitive
root under the exact embedding defining arithmetic restriction. -/
def rationalArithmeticLocalCyclotomicH2RootEquiv :
    ContinuousRepresentationH2 (coefficientCharacterRep
      (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom)
      (coefficientCharacterAction_continuous _
        (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).continuous) ≃+
    GaloisRootContinuousH2 (K := rationalPrimeLocalField p hp)
      (Ω := rationalPrimeLocalClosure p hp) q :=
  continuousH2AdditiveCoefficientEquiv _ _
    (rationalArithmeticLocalRootCoefficientEquiv a q hqa p hp)
    continuous_of_discreteTopology continuous_of_discreteTopology
    (rationalArithmeticLocalRootCoefficientEquiv_equivariant a q hqa p hp) _ _

/-- Genuine global root H2 restricts through the actual arithmetic Galois
map and the coefficient map proved to be the original field embedding. -/
def rationalArithmeticRootH2Restriction :
    ContinuousRepresentationH2 (rationalArithmeticRootRepresentation a q)
      (rationalArithmeticRootAction_continuous a q) →+
    GaloisRootContinuousH2 (K := rationalPrimeLocalField p hp)
      (Ω := rationalPrimeLocalClosure p hp) q :=
  let A := rationalArithmeticRootRepresentation a q
  let j := rationalPrimeArithmeticRestriction a p hp
  (continuousH2AdditiveCoefficientEquiv (restrictedCoefficientRep A j.toMonoidHom) _
    (rationalArithmeticRootLocalEquiv a q hqa p hp)
    continuous_of_discreteTopology continuous_of_discreteTopology
    (rationalArithmeticRootLocalEquiv_equivariant a q hqa p hp)
    (restrictedCoefficientAction_continuous A j.toMonoidHom j.continuous
      (rationalArithmeticRootAction_continuous a q)) _).toAddMonoidHom.comp
        (continuousRepresentationH2Restriction A (rationalArithmeticRootAction_continuous a q)
          j.toMonoidHom j.continuous).toAddMonoidHom

/-- The original global-to-local cyclotomic H2 square commutes with the
coherent root identifications, on the actual continuous cocycle quotients. -/
theorem rationalArithmeticRootH2Restriction_compatible
    (x : ContinuousRepresentationH2 (coefficientCharacterRep
      (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom)
      (coefficientCharacterAction_continuous _
        (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).continuous)) :
    rationalArithmeticRootH2Restriction a q hqa p hp
      (rationalArithmeticCyclotomicH2RootEquiv a q hqa x) =
      rationalArithmeticLocalCyclotomicH2RootEquiv a q hqa p hp
        (rationalPrimeCyclotomicH2Restriction a q hqa p hp x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ c =>
    have he := congrArg (rationalArithmeticLocalCyclotomicH2RootEquiv a q hqa p hp)
      (rationalPrimeCyclotomicH2Restriction_mk a q hqa p hp c)
    refine Eq.trans ?_ he.symm
    apply congrArg Submodule.Quotient.mk
    apply Subtype.ext
    apply Subtype.ext
    funext z
    change rationalArithmeticRootLocalEquiv a q hqa p hp
      (rationalArithmeticRootCoefficientEquiv a q hqa
        (c.val (rationalPrimeArithmeticRestriction a p hp z.1,
          rationalPrimeArithmeticRestriction a p hp z.2))) = _
    have hc := continuousCocycleTwoCoefficientCongr_apply
      (rationalArithmeticCyclotomicRepresentation_restriction a q hqa p hp (k := ZMod q))
      (continuousRepresentationCocycleTwoRestriction (coefficientCharacterRep
        (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom)
        (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
        (rationalPrimeArithmeticRestriction a p hp).continuous c) z
    exact (congrArg (rationalArithmeticLocalRootCoefficientEquiv a q hqa p hp)
      ((rationalArithmeticRootCoefficientEquiv a q hqa).symm_apply_apply _)).trans
        (congrArg (rationalArithmeticLocalRootCoefficientEquiv a q hqa p hp) hc).symm

end
end Dubon2026
