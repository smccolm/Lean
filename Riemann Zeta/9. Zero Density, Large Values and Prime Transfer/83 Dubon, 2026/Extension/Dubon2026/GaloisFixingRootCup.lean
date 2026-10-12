import Dubon2026.GaloisFixingRootCohomology
import Dubon2026.ContinuousRootCharacterCup

/-! # The original root cup under the actual fixing-subgroup identification -/

namespace Dubon2026
noncomputable section

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (E : IntermediateField K Ω) [IsGalois E Ω] (n : ℕ) [NeZero n]
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- Reuse the original root coefficient topology on the same roots over the finite base. -/
local instance fixingRootCupStageTopology : TopologicalSpace (galoisRootOfUnityRepresentation (K := E) (Ω := Ω) n) :=
  inferInstanceAs (TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n))
/-- The unchanged original root coefficient topology remains discrete. -/
local instance fixingRootCupStageDiscrete : DiscreteTopology (galoisRootOfUnityRepresentation (K := E) (Ω := Ω) n) :=
  inferInstanceAs (DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n))
/-- Reuse the original unit coefficient topology on the same units over the finite base. -/
local instance fixingRootCupUnitTopology : TopologicalSpace (Rep.ofAlgebraAutOnUnits E Ω) :=
  inferInstanceAs (TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω))
/-- The unchanged original unit coefficient topology remains discrete. -/
local instance fixingRootCupUnitDiscrete : DiscreteTopology (Rep.ofAlgebraAutOnUnits E Ω) :=
  inferInstanceAs (DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω))

/-- The original field character as its literal cocycle on the fixing subgroup. -/
def galoisFixingFiniteCharacterCocycle (χ : Gal(Ω/E) →ₜ* Multiplicative (ZMod n)) :
    continuousRepresentationCocyclesOne
      (restrictedCoefficientRep (Rep.of (1 : Representation ℤ Gal(Ω/K) (ZMod n)))
        E.fixingSubgroup.subtype) :=
  continuousRepresentationCocycleOneRestriction
    (Rep.of (1 : Representation ℤ Gal(Ω/E) (ZMod n)))
    E.fixingSubgroupEquiv.toMonoidHom (fixingSubgroupEquiv_continuous K Ω E)
    (continuousGaloisFiniteCharacterOneCocycle n χ)

/-- The same actual exponent cup on the original fixing subgroup. -/
def galoisFixingRootCharacterH1Cup (χ : Gal(Ω/E) →ₜ* Multiplicative (ZMod n)) :=
  (continuousH1Cup
    (restrictedCoefficientRep (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n) E.fixingSubgroup.subtype)
    (restrictedCoefficientRep (Rep.of (1 : Representation ℤ Gal(Ω/K) (ZMod n))) E.fixingSubgroup.subtype)
    (restrictedCoefficientRep (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n) E.fixingSubgroup.subtype)
    (galoisRootExponentPairing (K := K) (Ω := Ω) n)
    (fun g a b => galoisRootExponentPairing_equivariant (K := K) (Ω := Ω) n (g : Gal(Ω/K)) a b)
    continuous_of_discreteTopology
    (restrictedCoefficientAction_continuous (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n) E.fixingSubgroup.subtype continuous_subtype_val
      (discreteGaloisRootAction_continuous (K := K) (Ω := Ω) n))
    (restrictedCoefficientAction_continuous (Rep.of (1 : Representation ℤ Gal(Ω/K) (ZMod n))) E.fixingSubgroup.subtype continuous_subtype_val continuous_snd)
    (restrictedCoefficientAction_continuous (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n) E.fixingSubgroup.subtype continuous_subtype_val
      (discreteGaloisRootAction_continuous (K := K) (Ω := Ω) n))).flip
        (Submodule.Quotient.mk (galoisFixingFiniteCharacterCocycle K Ω E n χ))

/-- The actual fixing-subgroup identifications preserve the original Kummer
character cup, by the literal original continuous cocycle formula. -/
theorem galoisFixingRootH2Equiv_cup (χ : Gal(Ω/E) →ₜ* Multiplicative (ZMod n))
    (x : GaloisRootContinuousH1 (K := E) (Ω := Ω) n) :
    galoisFixingRootH2Equiv K Ω E n (continuousGaloisRootCharacterH1Cup n χ x) =
      galoisFixingRootCharacterH1Cup K Ω E n χ (galoisFixingRootH1Equiv K Ω E n x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ c => rfl

end
end Dubon2026
