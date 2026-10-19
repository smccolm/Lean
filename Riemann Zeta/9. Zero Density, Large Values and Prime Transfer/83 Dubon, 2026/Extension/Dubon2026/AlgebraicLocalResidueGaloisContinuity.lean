import Dubon2026.AlgebraicLocalResidueGalois
import Dubon2026.AlgebraicLocalInertia

/-! Continuity and surjectivity of the original residue Galois map.
These connect the proved Frobenius generator to DUB-17's actual finite
inertia quotients, with the original field and residue action preserved. -/

namespace Dubon2026
noncomputable section
open scoped Topology

variable (K L : Type) [NontriviallyNormedField K] [NormedField L]
  [NormedAlgebra K L] [IsUltrametricDist K] [IsUltrametricDist L] [CompleteSpace K]
  [IsGalois K L]

attribute [local instance] algebraicLocalIntegerAction algebraicLocalIntegerBaseAlgebra
  algebraicLocalIntegerBaseIsLocalHom

/-- The original residue Galois map has precisely the original inertia kernel. -/
theorem algebraicLocalResidueGalois_ker :
    (algebraicLocalResidueGalois K L).ker = algebraicLocalInertia K L := by
  ext g
  rw [MonoidHom.mem_ker, algebraicLocalInertia_mem_iff]
  constructor
  · intro h x
    exact congrArg (fun e => e x) h
  · intro h
    exact AlgEquiv.ext h

/-- Every original residue automorphism lifts through the same original Galois map. -/
theorem algebraicLocalResidueGalois_surjective :
    Function.Surjective (algebraicLocalResidueGalois K L) := by
  let R := algebraicLocalIntegerRing K
  let S := algebraicLocalIntegerRing L
  letI : SMulCommClass Gal(L/K) R S := algebraicLocalIntegerAction_smulComm K L
  letI : Algebra.IsInvariant R S Gal(L/K) := algebraicLocalIntegerAction_isInvariant K L
  letI : TopologicalSpace S := ⊥
  letI : DiscreteTopology S := ⟨rfl⟩
  letI : ContinuousSMul Gal(L/K) S := algebraicLocalIntegerAction_continuous K L
  intro σ
  obtain ⟨g, hg⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite
    (G := Gal(L/K)) (IsLocalRing.maximalIdeal R) (IsLocalRing.maximalIdeal S) σ
  refine ⟨g.val, AlgEquiv.ext fun x => ?_⟩
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective x
  exact congrArg (fun e => e (IsLocalRing.residue S x)) hg

/-- Each original residue stabilizer is open, by lifting its element to an
original algebraic integer and using the original Krull stabilizer. -/
theorem algebraicLocal_residue_stabilizer_isOpen
    (x : IsLocalRing.ResidueField (algebraicLocalIntegerRing L)) :
    IsOpen (MulAction.stabilizer Gal(L/K) x : Set Gal(L/K)) := by
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective x
  apply Subgroup.isOpen_mono (H₁ := MulAction.stabilizer Gal(L/K) x.val) ?_
    (stabilizer_isOpen_of_isIntegral (K := K) x.val)
  intro g hg
  change g • IsLocalRing.residue _ x = IsLocalRing.residue _ x
  rw [← IsLocalRing.ResidueField.residue_smul]
  congr 1
  exact Subtype.ext hg

/-- Finite base residue fields make the original residue Galois map continuous
for its actual Krull topology, using finite residue subfields as neighborhoods. -/
theorem algebraicLocalResidueGalois_continuous
    [Finite (IsLocalRing.ResidueField (algebraicLocalIntegerRing K))] :
    Continuous (algebraicLocalResidueGalois K L) := by
  classical
  let k := IsLocalRing.ResidueField (algebraicLocalIntegerRing K)
  let κ := IsLocalRing.ResidueField (algebraicLocalIntegerRing L)
  apply continuous_of_continuousAt_one _ (continuousAt_def.mpr _)
  intro N hN
  rw [map_one, krullTopology_mem_nhds_one_iff] at hN
  obtain ⟨E, hE, hEN⟩ := hN
  letI : FiniteDimensional k E := hE
  letI : Finite E := Module.finite_of_finite k
  let W := ⋂ x : E, (MulAction.stabilizer Gal(L/K) (x : κ) : Set Gal(L/K))
  have hW : IsOpen W := isOpen_iInter_of_finite
    (fun x : E => algebraicLocal_residue_stabilizer_isOpen K L (x : κ))
  have h1 : (1 : Gal(L/K)) ∈ W := by
    simp only [W, Set.mem_iInter, SetLike.mem_coe, Subgroup.one_mem, implies_true]
  apply Filter.mem_of_superset (hW.mem_nhds h1)
  intro g hg
  apply hEN
  apply (IntermediateField.mem_fixingSubgroup_iff E _).mpr
  intro x hx
  exact Set.mem_iInter.mp hg ⟨x, hx⟩

end
end Dubon2026
