import Dubon2026.FiniteGaloisUnitNormRange
import Dubon2026.ContinuousFiniteCyclicH2

/-! # Actual continuous H2 vanishes for the finite-field Galois unit representation -/

namespace Dubon2026
noncomputable section
open CategoryTheory

variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]

variable [Finite L] [FiniteDimensional K L] [IsGalois K L]
  [TopologicalSpace Gal(L/K)] [DiscreteTopology Gal(L/K)]

attribute [local instance] IsCyclic.commGroup

/-- The original integer action is continuous in the original discrete coefficient topology. -/
instance galoisUnitDiscreteContinuousSMul :
    @ContinuousSMul ℤ (Rep.ofAlgebraAutOnUnits K L)
      (Rep.ofAlgebraAutOnUnits K L).hV2.toSMul inferInstance inferInstance :=
  ⟨continuous_of_discreteTopology⟩

omit [Finite L] [FiniteDimensional K L] [IsGalois K L] in
/-- The original finite-field Galois action on the original discrete unit
coefficient representation is jointly continuous in the same discrete topology. -/
theorem finiteFieldGaloisUnitAction_continuous :
    Continuous (fun z : Gal(L/K) × Rep.ofAlgebraAutOnUnits K L =>
      (Rep.ofAlgebraAutOnUnits K L).ρ z.1 z.2) :=
  continuous_of_discreteTopology

/-- The original continuous H2 of the finite-field Galois unit representation
vanishes. Cyclicity is derived from the actual finite fields; the norm quotient
and the original field-unit norm surjectivity provide the actual coboundaries. -/
theorem continuousFiniteFieldGaloisUnitH2_eq_zero
    (x : ContinuousRepresentationH2 (Rep.ofAlgebraAutOnUnits K L)
      (finiteFieldGaloisUnitAction_continuous (K := K) (L := L))) : x = 0 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Gal(L/K))
  obtain ⟨v, rfl⟩ := continuousFiniteCyclicH2Pi_surjective (Rep.ofAlgebraAutOnUnits K L)
    (finiteFieldGaloisUnitAction_continuous (K := K) (L := L)) g hg x
  apply (continuousFiniteCyclicH2Pi_eq_zero_iff (Rep.ofAlgebraAutOnUnits K L)
    (finiteFieldGaloisUnitAction_continuous (K := K) (L := L)) g hg v).mpr
  apply finiteFieldGaloisUnit_invariant_mem_normRange v.val
  apply (Representation.mem_invariants_iff_of_forall_mem_zpowers
    (Rep.ofAlgebraAutOnUnits K L).ρ g hg v.val).mpr
  have hv := v.property
  change (Rep.ofAlgebraAutOnUnits K L).ρ g v.val - v.val = 0 at hv
  exact sub_eq_zero.mp hv

end
end Dubon2026
