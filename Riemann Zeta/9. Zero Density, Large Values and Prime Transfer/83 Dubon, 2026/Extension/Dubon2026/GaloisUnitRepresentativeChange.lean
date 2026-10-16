import Dubon2026.ContinuousCosetRepresentativeChange
import Dubon2026.GaloisUnitContinuousCorestriction

/-! # Representative independence for actual Galois unit corestriction

This consumes the cocycle on the actual finite extension, its original
fixing-subgroup identification, and the original continuous transfer.
-/

namespace Dubon2026
noncomputable section

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (E : IntermediateField K Ω) [FiniteDimensional K E] [IsGalois E Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits E Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits E Ω)]

/-- The original unit corestriction is represented by the literal trace
computed using any changed representatives of the genuine fixing cosets. -/
theorem galoisUnitContinuousCorestriction_changed_representatives
    (a : Gal(Ω/K) ⧸ E.fixingSubgroup → E.fixingSubgroup)
    (c : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits E Ω)) :
    letI : Fintype (Gal(Ω/K) ⧸ E.fixingSubgroup) := Fintype.ofFinite _
    (Submodule.Quotient.mk
      (continuousChangedCosetTraceCocycle (Rep.ofAlgebraAutOnUnits K Ω)
        (discreteGaloisUnitAction_continuous (K := K) (Ω := Ω))
        E.fixingSubgroup E.fixingSubgroup_isOpen a (galoisFixingUnitCocycle K Ω E c)) :
      GaloisUnitContinuousH2 (K := K) (Ω := Ω)) =
        galoisUnitContinuousCorestriction K Ω E (Submodule.Quotient.mk c) := by
  letI : Fintype (Gal(Ω/K) ⧸ E.fixingSubgroup) := Fintype.ofFinite _
  exact continuousChangedCosetTraceCocycle_class (Rep.ofAlgebraAutOnUnits K Ω)
    (discreteGaloisUnitAction_continuous (K := K) (Ω := Ω)) E.fixingSubgroup
    E.fixingSubgroup_isOpen a (galoisFixingUnitCocycle K Ω E c)

end
end Dubon2026
