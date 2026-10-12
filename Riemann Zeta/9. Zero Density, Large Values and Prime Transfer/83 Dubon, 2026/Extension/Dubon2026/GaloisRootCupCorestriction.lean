import Dubon2026.GaloisRootContinuousRestriction
import Dubon2026.GaloisRootContinuousCorestriction
import Dubon2026.ContinuousFiniteCharacterH1
import Dubon2026.ContinuousCupCorestriction
import Dubon2026.ContinuousCupRestriction
import Dubon2026.GaloisFixingRootCup

/-! # Actual finite-field projection formula for the Kummer character cup

An original cyclotomic-stage character transfers to an actual base character.
The equality uses original continuous cups, restrictions and finite coset traces.
-/

namespace Dubon2026
noncomputable section

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (E : IntermediateField K Ω) [FiniteDimensional K E] [IsGalois E Ω] (n : ℕ) [NeZero n]
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- Reuse the original root coefficient topology on the same roots over the finite base. -/
local instance rootCupCorestrictionStageTopology : TopologicalSpace (galoisRootOfUnityRepresentation (K := E) (Ω := Ω) n) :=
  inferInstanceAs (TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n))
/-- The unchanged original root coefficient topology remains discrete. -/
local instance rootCupCorestrictionStageDiscrete : DiscreteTopology (galoisRootOfUnityRepresentation (K := E) (Ω := Ω) n) :=
  inferInstanceAs (DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n))
/-- Reuse the original unit coefficient topology on the same units over the finite base. -/
local instance rootCupCorestrictionUnitTopology : TopologicalSpace (Rep.ofAlgebraAutOnUnits E Ω) :=
  inferInstanceAs (TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω))
/-- The unchanged original unit coefficient topology remains discrete. -/
local instance rootCupCorestrictionUnitDiscrete : DiscreteTopology (Rep.ofAlgebraAutOnUnits E Ω) :=
  inferInstanceAs (DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω))

/-- Every original finite-field character transfers to an actual base character
whose cup is the genuine corestriction of the original restricted cup. -/
theorem galoisRootCharacterCup_corestriction
    (χ : Gal(Ω/E) →ₜ* Multiplicative (ZMod n)) :
    ∃ ψ : Gal(Ω/K) →ₜ* Multiplicative (ZMod n),
      ∀ x : GaloisRootContinuousH1 (K := K) (Ω := Ω) n,
        galoisRootContinuousCorestriction K Ω E n
          (continuousGaloisRootCharacterH1Cup (K := E) (Ω := Ω) n χ
            (galoisRootContinuousRestriction K Ω E n x)) =
          continuousGaloisRootCharacterH1Cup (K := K) (Ω := Ω) n ψ x := by
  letI : Fintype (Gal(Ω/K) ⧸ E.fixingSubgroup) := Fintype.ofFinite _
  let A := galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n
  let B := Rep.of (1 : Representation ℤ Gal(Ω/K) (ZMod n))
  let hA := discreteGaloisRootAction_continuous (K := K) (Ω := Ω) n
  let S := E.fixingSubgroup
  let y : ContinuousRepresentationH1 (restrictedCoefficientRep B S.subtype)
      (restrictedCoefficientAction_continuous B S.subtype continuous_subtype_val continuous_snd) :=
    Submodule.Quotient.mk (galoisFixingFiniteCharacterCocycle K Ω E n χ)
  obtain ⟨ψ, hψ⟩ := continuousGaloisFiniteCharacterH1_surjective (K := K) (Ω := Ω) n
    (continuousRepresentationH1Corestriction B continuous_snd S E.fixingSubgroup_isOpen y)
  refine ⟨ψ, fun x => ?_⟩
  have hp := continuousH1Cup_corestriction_projection A B A
    (galoisRootExponentPairing (K := K) (Ω := Ω) n)
    (galoisRootExponentPairing_equivariant (K := K) (Ω := Ω) n)
    continuous_of_discreteTopology hA continuous_snd hA S E.fixingSubgroup_isOpen x y
  let cup := continuousH1Cup A B A (galoisRootExponentPairing (K := K) (Ω := Ω) n)
    (galoisRootExponentPairing_equivariant (K := K) (Ω := Ω) n)
    continuous_of_discreteTopology hA continuous_snd hA
  have ht : cup x (continuousRepresentationH1Corestriction B continuous_snd S E.fixingSubgroup_isOpen y) =
      continuousGaloisRootCharacterH1Cup (K := K) (Ω := Ω) n ψ x :=
    congrArg (cup x) hψ.symm
  change continuousRepresentationH2Corestriction A hA S E.fixingSubgroup_isOpen
    (galoisFixingRootH2Equiv K Ω E n
      (continuousGaloisRootCharacterH1Cup (K := E) (Ω := Ω) n χ (galoisRootContinuousRestriction K Ω E n x))) = _
  let cor := continuousRepresentationH2Corestriction A hA S E.fixingSubgroup_isOpen
  have hs := congrArg cor (galoisFixingRootH2Equiv_cup K Ω E n χ
    (galoisRootContinuousRestriction K Ω E n x))
  have hr := congrArg (fun z => cor (galoisFixingRootCharacterH1Cup K Ω E n χ z))
    (galoisFixingRootH1Equiv_restriction K Ω E n x)
  exact hs.trans (hr.trans (hp.trans ht))

end
end Dubon2026
