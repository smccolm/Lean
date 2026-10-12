import Dubon2026.GaloisFixingRootCohomology
import Dubon2026.ContinuousCorestrictionCoefficientMap
import Dubon2026.GaloisUnitContinuousCorestriction

/-! # Actual finite-field corestriction on original root cohomology

The Kummer inclusion square is proved on the actual continuous coset trace.
It transfers the proved unit-H2 corestriction theorem to original root classes.
-/

namespace Dubon2026
noncomputable section

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (E : IntermediateField K Ω) [FiniteDimensional K E] [IsGalois E Ω] (n : ℕ)
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- Reuse the original root coefficient topology on the same roots over the finite base. -/
local instance rootCorestrictionStageTopology : TopologicalSpace (galoisRootOfUnityRepresentation (K := E) (Ω := Ω) n) :=
  inferInstanceAs (TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n))
/-- The unchanged original root coefficient topology remains discrete. -/
local instance rootCorestrictionStageDiscrete : DiscreteTopology (galoisRootOfUnityRepresentation (K := E) (Ω := Ω) n) :=
  inferInstanceAs (DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n))
/-- Reuse the original unit coefficient topology on the same units over the finite base. -/
local instance rootCorestrictionUnitTopology : TopologicalSpace (Rep.ofAlgebraAutOnUnits E Ω) :=
  inferInstanceAs (TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω))
/-- The unchanged original unit coefficient topology remains discrete. -/
local instance rootCorestrictionUnitDiscrete : DiscreteTopology (Rep.ofAlgebraAutOnUnits E Ω) :=
  inferInstanceAs (DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω))

/-- The original root H2 corestriction is the actual coset trace after the
genuine field-to-fixing-subgroup identification. -/
def galoisRootContinuousCorestriction :
    GaloisRootContinuousH2 (K := E) (Ω := Ω) n →+
      GaloisRootContinuousH2 (K := K) (Ω := Ω) n := by
  letI : Fintype (Gal(Ω/K) ⧸ E.fixingSubgroup) := Fintype.ofFinite _
  exact (continuousRepresentationH2Corestriction
    (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)
    (discreteGaloisRootAction_continuous (K := K) (Ω := Ω) n)
    E.fixingSubgroup E.fixingSubgroup_isOpen).toAddMonoidHom.comp
      (galoisFixingRootH2Equiv K Ω E n).toAddMonoidHom

/-- The actual Kummer inclusion commutes with original finite-field
corestriction; no invariant or replacement transfer defines either map. -/
theorem galoisRootContinuousCorestriction_inclusion
    (x : GaloisRootContinuousH2 (K := E) (Ω := Ω) n) :
    galoisKummerH2Inclusion (K := K) (Ω := Ω) n
      (galoisRootContinuousCorestriction K Ω E n x) =
      galoisUnitContinuousCorestriction K Ω E
        (galoisKummerH2Inclusion (K := E) (Ω := Ω) n x) := by
  letI : Fintype (Gal(Ω/K) ⧸ E.fixingSubgroup) := Fintype.ofFinite _
  let A := galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n
  let B := Rep.ofAlgebraAutOnUnits K Ω
  let φ := (galoisKummerInclusion (K := K) (Ω := Ω) n).hom.toLinearMap
  let hφ := galoisKummerInclusion_continuous (K := K) (Ω := Ω) n
  let hφρ := Rep.hom_comm_apply (galoisKummerInclusion (K := K) (Ω := Ω) n)
  let hA := discreteGaloisRootAction_continuous (K := K) (Ω := Ω) n
  let hB := discreteGaloisUnitAction_continuous (K := K) (Ω := Ω)
  change continuousCoefficientH2Map A B φ hφ hφρ hA hB
      (continuousRepresentationH2Corestriction A hA E.fixingSubgroup E.fixingSubgroup_isOpen
        (galoisFixingRootH2Equiv K Ω E n x)) = _
  rw [continuousCoefficientH2Map_corestriction]
  change continuousRepresentationH2Corestriction B hB E.fixingSubgroup E.fixingSubgroup_isOpen
      _ = continuousRepresentationH2Corestriction B hB E.fixingSubgroup E.fixingSubgroup_isOpen
        (galoisFixingUnitH2 K Ω E (galoisKummerH2Inclusion (K := E) (Ω := Ω) n x))
  congr 1
  induction x using Submodule.Quotient.induction_on with
  | _ c => rfl

end
end Dubon2026
