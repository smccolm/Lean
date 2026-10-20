import Dubon2026.NumberFieldIntegralFiniteAdeles
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Mathlib.Topology.Algebra.IsUniformGroup.Basic

/-! # Discreteness of the original principal number-field adeles

For finite arithmetic stabilizers in DUB-17, an integral finite component
and bounded infinite components give a finite neighborhood. The pinned
bounded-conjugates theorem and the existing rational proof pattern avoid
a separate adelic base-change theory or a common-denominator construction.
-/

namespace Dubon2026

noncomputable section

open NumberField IsDedekindDomain
open scoped NumberField RestrictedProduct Topology

variable (K : Type*) [Field K] [NumberField K]

omit [NumberField K] in
/-- The norm of the actual principal embedding in its infinite completion. -/
theorem numberFieldInfiniteCompletion_norm (v : InfinitePlace K) (x : K) :
    ‖algebraMap K v.Completion x‖ = v x := by
  change ‖((WithAbs.equiv v.val).symm x : v.Completion)‖ = v x
  rw [InfinitePlace.Completion.norm_coe]
  rfl

/-- The original adelic topology is Hausdorff. -/
theorem numberFieldAdele_t2Space : T2Space (AdeleRing (𝓞 K) K) := by
  letI : T2Space (InfiniteAdeleRing K) := inferInstanceAs
    (T2Space ((v : InfinitePlace K) → v.Completion))
  letI : T2Space (FiniteAdeleRing (𝓞 K) K) := inferInstanceAs
    (T2Space (Πʳ v : HeightOneSpectrum (𝓞 K), [v.adicCompletion K, v.adicCompletionIntegers K]))
  exact inferInstanceAs (T2Space (InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K))

/-- The original principal subgroup is discrete in the full number-field adele topology. -/
theorem numberFieldAdelePrincipal_discreteTopology :
    DiscreteTopology (AdeleRing.principalSubgroup (𝓞 K) K) := by
  letI := numberFieldAdele_t2Space K
  let H := AdeleRing.principalSubgroup (𝓞 K) K
  let S : Set H := {x | (∀ v : InfinitePlace K, ‖x.val.1 v‖ < 1) ∧
    x.val.2 ∈ numberFieldIntegralFiniteAdeles K}
  have hSopen : IsOpen S := by
    apply IsOpen.inter
    · change IsOpen {x : H | ∀ v : InfinitePlace K, ‖x.val.1 v‖ < 1}
      rw [Set.setOf_forall]
      apply isOpen_iInter_of_finite
      intro v
      exact isOpen_lt ((continuous_apply v).comp (continuous_fst.comp continuous_subtype_val)).norm
        continuous_const
    · exact (numberFieldIntegralFiniteAdeles_isOpen K).preimage
        (continuous_snd.comp continuous_subtype_val)
  have hS0 : (0 : H) ∈ S := by
    constructor
    · intro v
      change ‖(0 : v.Completion)‖ < 1
      simp
    · exact (numberFieldIntegralFiniteAdeles K).zero_mem
  let B : Set K := {x | IsIntegral ℤ x ∧ ∀ φ : K →+* ℂ, ‖φ x‖ ≤ 1}
  have hB : B.Finite := Embeddings.finite_of_norm_le K ℂ 1
  let F : K → H := fun x => ⟨algebraMap K (AdeleRing (𝓞 K) K) x, x, rfl⟩
  have hS : S.Finite := by
    apply (hB.image F).subset
    intro x hx
    obtain ⟨k, hk⟩ := x.property
    refine ⟨k, ?_, Subtype.ext hk⟩
    constructor
    · apply (numberFieldFiniteAdele_integral_iff K k).mp
      have h := hx.2
      rw [← hk] at h
      exact h
    · intro φ
      have h := hx.1 (InfinitePlace.mk φ)
      rw [← hk] at h
      change ‖algebraMap K (InfinitePlace.mk φ).Completion k‖ < 1 at h
      rw [numberFieldInfiniteCompletion_norm, InfinitePlace.apply] at h
      exact h.le
  exact discreteTopology_of_isOpen_singleton_zero
    (isOpen_singleton_of_finite_mem_nhds (0 : H) (hSopen.mem_nhds hS0) hS)

end
end Dubon2026
