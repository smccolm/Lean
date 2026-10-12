import Dubon2026.ContinuousGaloisFiniteFactors
import Dubon2026.ContinuousRepresentationRestriction

/-! # An actual finite splitting field for a continuous finite coefficient action

This supplies the field needed to reduce full local cocycle finiteness to the
proved constant-module case in the DUB-17 finite-module duality chain.
-/

namespace Dubon2026
noncomputable section

variable {R G : Type} [CommRing R] [Group G] [TopologicalSpace G]
  (A : Rep R G) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))

include hA in
/-- The actual finite coefficient action has open kernel, since equality to the
identity is the finite intersection of original coefficient stabilizers. -/
theorem continuousFiniteCoefficient_kernel_isOpen :
    IsOpen (A.ρ.asGroupHom.ker : Set G) := by
  have he : (A.ρ.asGroupHom.ker : Set G) = ⋂ a : A, {g : G | A.ρ g a = a} := by
    ext g
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    constructor
    · intro hg a
      exact congrArg (fun u : Units (A →ₗ[R] A) => u.val a) hg
    · intro hg
      apply Units.ext
      apply LinearMap.ext
      exact hg
  rw [he]
  apply isOpen_iInter_of_finite
  intro a
  exact (isOpen_discrete ({a} : Set A)).preimage
    (hA.comp (continuous_id.prodMk continuous_const))

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]

/-- The original continuous finite coefficient action becomes trivial on the
actual Galois fixing subgroup of a genuine finite Galois intermediate field.
The existing open-kernel finite-factor theorem constructs that field. -/
theorem continuousFiniteCoefficient_exists_splittingField
    (B : Rep R Gal(Ω/K)) [Finite B] [TopologicalSpace B] [DiscreteTopology B]
    (hB : Continuous (fun z : Gal(Ω/K) × B => B.ρ z.1 z.2)) :
    ∃ F : FiniteGaloisIntermediateField K Ω,
      ∀ g : Gal(Ω/K), g ∈ F.toIntermediateField.fixingSubgroup → ∀ b : B, B.ρ g b = b := by
  obtain ⟨F, ψ, hψ⟩ := galois_open_kernel_finite_factor B.ρ.asGroupHom
    (continuousFiniteCoefficient_kernel_isOpen B hB)
  refine ⟨F, fun g hg b => ?_⟩
  have hr : AlgEquiv.restrictNormalHom F g = 1 := by
    change g ∈ (AlgEquiv.restrictNormalHom F).ker
    rwa [F.toIntermediateField.restrictNormalHom_ker]
  have ht : B.ρ.asGroupHom g = 1 := (hψ g).symm.trans (by rw [hr, map_one])
  exact congrArg (fun u : Units (B →ₗ[R] B) => u.val b) ht

end
end Dubon2026
