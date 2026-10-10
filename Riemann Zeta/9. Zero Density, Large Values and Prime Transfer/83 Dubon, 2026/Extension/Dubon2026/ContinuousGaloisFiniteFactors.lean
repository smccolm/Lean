import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.OpenSubgroup

/-! # Actual finite Galois subextensions for original continuous discrete characters -/

namespace Dubon2026

noncomputable section

variable {K Ω T : Type*} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  [Group T]

/-- Every original Galois homomorphism with open kernel factors through the actual finite Galois field fixed by that kernel. -/
theorem galois_open_kernel_finite_factor (χ : Gal(Ω/K) →* T)
    (hopen : IsOpen (χ.ker : Set Gal(Ω/K))) :
    ∃ F : FiniteGaloisIntermediateField K Ω,
      ∃ ψ : Gal(F/K) →* T, ∀ g : Gal(Ω/K),
        ψ (AlgEquiv.restrictNormalHom F g) = χ g := by
  let H : ClosedSubgroup Gal(Ω/K) := ⟨χ.ker, χ.ker.isClosed_of_isOpen hopen⟩
  let L := IntermediateField.fixedField χ.ker
  have hfix : L.fixingSubgroup = χ.ker :=
    InfiniteGalois.fixingSubgroup_fixedField H
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
  let ψ : Gal(F/K) →* T :=
    (QuotientGroup.lift χ.ker χ le_rfl).comp e.symm.toMonoidHom
  refine ⟨F, ψ, ?_⟩
  intro g
  change QuotientGroup.lift χ.ker χ le_rfl
    (e.symm (e (QuotientGroup.mk' χ.ker g))) = χ g
  rw [e.symm_apply_apply]
  rfl

/-- Every original continuous character into an actual discrete group factors through an original finite Galois subextension. -/
theorem continuous_galois_finite_factor [TopologicalSpace T] [DiscreteTopology T]
    (χ : Gal(Ω/K) →ₜ* T) :
    ∃ F : FiniteGaloisIntermediateField K Ω,
      ∃ ψ : Gal(F/K) →* T, ∀ g : Gal(Ω/K),
        ψ (AlgEquiv.restrictNormalHom F g) = χ g := by
  apply galois_open_kernel_finite_factor χ.toMonoidHom
  exact (isOpen_discrete ({1} : Set T)).preimage χ.continuous

end
end Dubon2026
