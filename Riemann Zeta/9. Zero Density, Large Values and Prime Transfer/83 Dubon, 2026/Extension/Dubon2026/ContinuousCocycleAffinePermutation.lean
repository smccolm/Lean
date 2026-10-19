import Dubon2026.CocycleAffinePermutation
import Dubon2026.ContinuousGaloisFiniteFactors

/-! The original continuous finite-coefficient cocycle has a continuous finite
affine permutation action. This places its local non-coboundary test within
the already proved prescribed-Frobenius prime theorem on the DUB-17 chain. -/

namespace Dubon2026
noncomputable section
open Filter Topology

variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep R G) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  [ContinuousSMul R A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))

include hA

omit [IsTopologicalGroup G] in
/-- The affine cocycle kernel is open because the finite set of original
coefficient vectors has open stabilizers under the actual continuous action. -/
theorem continuousCocycleAffinePermutation_kernel_isOpen
    (c : continuousRepresentationCocyclesOne A) :
    IsOpen ((cocycleAffinePermutation A c.val).ker : Set G) := by
  have he : ((cocycleAffinePermutation A c.val).ker : Set G) =
      ⋂ x : A, {g : G | A.ρ g x + c.val g = x} := by
    ext g
    simp only [Set.mem_iInter, Set.mem_setOf_eq, SetLike.mem_coe, MonoidHom.mem_ker]
    constructor
    · intro hg x
      exact congrArg (fun e : Equiv.Perm A => e x) hg
    · intro hg
      apply Equiv.ext
      exact hg
  rw [he]
  apply isOpen_iInter_of_finite
  intro x
  exact (isOpen_discrete ({x} : Set A)).preimage
    ((hA.comp (continuous_id.prodMk continuous_const)).add c.property)

/-- Openness of the actual affine kernel supplies continuity into the discrete
permutation group, so the native finite Galois factorization applies. -/
theorem continuousCocycleAffinePermutation_continuous
    [TopologicalSpace (Equiv.Perm A)] [DiscreteTopology (Equiv.Perm A)]
    (c : continuousRepresentationCocyclesOne A) :
    Continuous (cocycleAffinePermutation A c.val) := by
  apply continuous_of_tendsto_nhds_one
  apply tendsto_const_nhds.congr'
  filter_upwards [(continuousCocycleAffinePermutation_kernel_isOpen A hA c).mem_nhds
    (Subgroup.one_mem _)] with g hg
  exact (MonoidHom.mem_ker.mp hg).symm

end
end Dubon2026
