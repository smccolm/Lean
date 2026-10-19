import Dubon2026.ContinuousGaloisFiniteFactors

/-! The original open kernel gives a faithful finite Galois factor of
an actual discrete representation. This reuses the repository's fixed
field and kernel-quotient construction, retaining faithfulness so that
killing the auxiliary inertia matrices implies unramifiedness of the
field itself. That implication is needed for the base-support quotient
comparison in the Dubon Theorem 2.6 arithmetic patching chain. -/

namespace Dubon2026
noncomputable section

variable {K Ω T : Type*} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [Group T]

/-- The actual fixed field of an open representation kernel is finite
Galois, and its induced representation is faithful. -/
theorem galois_open_kernel_faithful_finite_factor (χ : Gal(Ω/K) →* T)
    (hopen : IsOpen (χ.ker : Set Gal(Ω/K))) :
    ∃ F : FiniteGaloisIntermediateField K Ω,
      ∃ ψ : Gal(F/K) →* T, Function.Injective ψ ∧
        ∀ g : Gal(Ω/K), ψ (AlgEquiv.restrictNormalHom F g) = χ g := by
  let H : ClosedSubgroup Gal(Ω/K) := ⟨χ.ker, χ.ker.isClosed_of_isOpen hopen⟩
  let L := IntermediateField.fixedField χ.ker
  have hfix : L.fixingSubgroup = χ.ker := InfiniteGalois.fixingSubgroup_fixedField H
  letI : FiniteDimensional K L := by
    apply (InfiniteGalois.isOpen_iff_finite L).mp
    simpa only [hfix] using hopen
  letI : IsGalois K L := by
    apply (InfiniteGalois.normal_iff_isGalois L).mp
    rw [hfix]
    infer_instance
  let F : FiniteGaloisIntermediateField K Ω := {
    toIntermediateField := L
    finiteDimensional := inferInstance
    isGalois := inferInstance }
  let e := InfiniteGalois.normalAutEquivQuotient H
  let ψ : Gal(F/K) →* T := (QuotientGroup.kerLift χ).comp e.symm.toMonoidHom
  refine ⟨F, ψ, (QuotientGroup.kerLift_injective χ).comp e.symm.injective, ?_⟩
  intro g
  change QuotientGroup.kerLift χ (e.symm (e (QuotientGroup.mk' χ.ker g))) = χ g
  rw [e.symm_apply_apply]
  rfl

/-- Every actual continuous representation into a discrete group has
an actual faithful finite Galois factor. -/
theorem continuous_galois_faithful_finite_factor [TopologicalSpace T] [DiscreteTopology T]
    (χ : Gal(Ω/K) →ₜ* T) :
    ∃ F : FiniteGaloisIntermediateField K Ω,
      ∃ ψ : Gal(F/K) →* T, Function.Injective ψ ∧
        ∀ g : Gal(Ω/K), ψ (AlgEquiv.restrictNormalHom F g) = χ g := by
  apply galois_open_kernel_faithful_finite_factor χ.toMonoidHom
  exact (isOpen_discrete ({1} : Set T)).preimage χ.continuous

end
end Dubon2026
