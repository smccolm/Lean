import Dubon2026.GaloisFixingSubgroupUnitCohomology
import Dubon2026.ContinuousCohomologyCorestriction

/-! # Actual continuous corestriction for the original finite field extension -/

namespace Dubon2026
noncomputable section

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (E : IntermediateField K Ω) [FiniteDimensional K E] [IsGalois E Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits E Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits E Ω)]

/-- Corestriction for the original finite separable extension is the
genuine finite coset trace on continuous unit cocycles, reindexed by its
actual Galois fixing subgroup. The local invariant is not used to define it. -/
def galoisUnitContinuousCorestriction :
    GaloisUnitContinuousH2 (K := E) (Ω := Ω) →ₗ[ℤ]
      GaloisUnitContinuousH2 (K := K) (Ω := Ω) := by
  letI : Fintype (Gal(Ω/K) ⧸ E.fixingSubgroup) := Fintype.ofFinite _
  exact (continuousRepresentationH2Corestriction (Rep.ofAlgebraAutOnUnits K Ω)
    (discreteGaloisUnitAction_continuous (K := K) (Ω := Ω))
    E.fixingSubgroup E.fixingSubgroup_isOpen).comp (galoisFixingUnitH2 K Ω E)

/-- Actual continuous field restriction followed by the original coset
corestriction equals multiplication by the exact original field degree. -/
theorem galoisUnitContinuousCorestriction_restriction
    (x : GaloisUnitContinuousH2 (K := K) (Ω := Ω)) :
    galoisUnitContinuousCorestriction K Ω E (continuousGaloisUnitBaseChangeH2 K E Ω Ω x) =
      Module.finrank K E • x := by
  letI : Fintype (Gal(Ω/K) ⧸ E.fixingSubgroup) := Fintype.ofFinite _
  change continuousRepresentationH2Corestriction (Rep.ofAlgebraAutOnUnits K Ω)
      (discreteGaloisUnitAction_continuous (K := K) (Ω := Ω))
      E.fixingSubgroup E.fixingSubgroup_isOpen
      (galoisFixingUnitH2 K Ω E (continuousGaloisUnitBaseChangeH2 K E Ω Ω x)) = _
  rw [galoisFixingUnitH2_baseChange, continuousRepresentationH2Corestriction_restriction,
    galoisFixingCosets_card]

end
end Dubon2026
