import Dubon2026.CoefficientRetractionIdealPowers
import Mathlib.Topology.Algebra.Algebra
import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.Topology.UniformSpace.UniformEmbedding

/-! # The genuine inherited coefficient topology is maximal-adic under an actual local retraction -/

namespace Dubon2026
noncomputable section
open Topology

variable {O R : Type*} [CommRing O] [CommRing R] [IsLocalRing R] [Algebra O R]

/-- Reflection of every original maximal-ideal power identifies the inherited coefficient-subalgebra topology with its own actual maximal-adic topology. -/
theorem coefficientRetraction_isAdic [TopologicalSpace R] [IsTopologicalRing R]
    (hR : IsAdic (IsLocalRing.maximalIdeal R))
    (S : Subalgebra O R) [IsLocalRing S] [IsLocalHom S.val.toRingHom]
    (f : R →ₐ[O] S) (hfix : ∀ x : S, f x = x) :
    IsAdic (IsLocalRing.maximalIdeal S) := by
  letI : IsTopologicalRing S := inferInstanceAs (IsTopologicalRing S.toSubring)
  have hp (n : ℕ) : (fun x : S => (x : R)) ⁻¹'
      ((IsLocalRing.maximalIdeal R ^ n : Ideal R) : Set R) =
      ((IsLocalRing.maximalIdeal S ^ n : Ideal S) : Set S) := by
    exact congrArg (fun J : Ideal S => (J : Set S))
      (coefficientRetraction_maximalIdeal_pow_comap S f hfix n)
  apply isAdic_iff.mpr
  constructor
  · intro n
    rw [← hp n]
    exact ((isAdic_iff.mp hR).1 n).preimage continuous_subtype_val
  · intro U hU
    have hb : (𝓝 (0 : S)).HasBasis (fun _ : ℕ => True)
        (fun n => (fun x : S => (x : R)) ⁻¹'
          ((IsLocalRing.maximalIdeal R ^ n : Ideal R) : Set R)) := by
      rw [nhds_subtype]
      exact hR.hasBasis_nhds_zero.comap (fun x : S => (x : R))
    obtain ⟨n, _hn, hnU⟩ := hb.mem_iff.mp hU
    refine ⟨n, ?_⟩
    rw [← hp n]
    exact hnU

/-- A closed original coefficient subalgebra with an actual local retraction is complete for its own maximal ideal when the original coefficient ring is genuinely complete. -/
theorem coefficientRetraction_isAdicComplete [WithIdeal R]
    [IsAdicComplete (WithIdeal.i : Ideal R) R]
    (hR : (WithIdeal.i : Ideal R) = IsLocalRing.maximalIdeal R)
    (S : Subalgebra O R) [IsLocalRing S] [IsLocalHom S.val.toRingHom]
    (hS : IsClosed (S : Set R))
    (f : R →ₐ[O] S) (hfix : ∀ x : S, f x = x) :
    IsAdicComplete (IsLocalRing.maximalIdeal S) S := by
  letI : CompleteSpace R := (IsAdic.isPrecomplete_iff
    (I := (WithIdeal.i : Ideal R)) rfl).mp inferInstance
  letI : T2Space R := (IsAdic.isHausdorff_iff
    (I := (WithIdeal.i : Ideal R)) rfl).mp inferInstance
  letI : CompleteSpace S := hS.isComplete.completeSpace_coe
  letI : IsUniformAddGroup S :=
    inferInstanceAs (IsUniformAddGroup S.toSubring.toAddSubgroup)
  have htop : IsAdic (IsLocalRing.maximalIdeal R) := by rw [← hR]; rfl
  exact (IsAdic.isAdicComplete_iff (coefficientRetraction_isAdic htop S f hfix)).mpr
    ⟨inferInstance, inferInstance⟩

end
end Dubon2026
