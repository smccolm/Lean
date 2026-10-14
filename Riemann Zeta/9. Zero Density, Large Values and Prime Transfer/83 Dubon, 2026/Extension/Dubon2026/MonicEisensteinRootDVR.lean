import Dubon2026.PrimeConstantRootIdeal
import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral

/-! # The actual Eisenstein root algebra is a discrete valuation ring

Every maximal ideal contracts to the original maximal ideal. The actual
Eisenstein root power belongs to its extension, so all maximal ideals
contain the proved maximal root ideal. That ideal is principal, giving
an actual DVR with the adjoined root as uniformizer. This is needed for
the specific cyclotomic and auxiliary root rings in DUB-17 reciprocity.
-/
namespace Dubon2026
noncomputable section
open Polynomial IsLocalRing

/-- The actual monic Eisenstein root algebra is local with its original root ideal maximal. -/
theorem monic_eisenstein_adjoinRoot_local {R : Type} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (f : R[X]) (hf : f.Monic) (π : R) (hπ : Prime π)
    (h0 : f.coeff 0 = π) (he : f.IsEisensteinAt (Ideal.span {π})) :
    IsLocalRing (AdjoinRoot f) := by
  haveI : Module.Finite R (AdjoinRoot f) := hf.finite_adjoinRoot
  let J : Ideal (AdjoinRoot f) := Ideal.span {AdjoinRoot.root f}
  have hJ : J.IsMaximal := prime_constant_adjoinRoot_root_maximal f π hπ h0
  haveI : Nontrivial (AdjoinRoot f) := ⟨⟨0, 1, by
    intro h
    apply hJ.ne_top
    apply (Ideal.eq_top_iff_one J).mpr
    rw [← h]
    exact J.zero_mem⟩⟩
  apply IsLocalRing.of_unique_max_ideal
  refine ⟨J, hJ, ?_⟩
  intro Q hQ
  haveI : Q.IsMaximal := hQ
  have hc : Q.comap (algebraMap R (AdjoinRoot f)) = maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := R) Q)
  have hmax : maximalIdeal R = Ideal.span {π} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ.irreducible
  have hle : (Ideal.span {π}).map (algebraMap R (AdjoinRoot f)) ≤ Q := by
    apply Ideal.map_le_iff_le_comap.mpr
    rw [hc, hmax]
  have hweak : f.IsWeaklyEisensteinAt (Ideal.span {π}) := ⟨he.mem⟩
  have hpow : AdjoinRoot.root f ^ f.natDegree ∈
      (Ideal.span {π}).map (algebraMap R (AdjoinRoot f)) := by
    apply hweak.pow_natDegree_le_of_aeval_zero_of_monic_mem_map
      (by rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]) hf
    rw [hf.natDegree_map]
  have hroot : AdjoinRoot.root f ∈ Q := hQ.isPrime.mem_of_pow_mem _ (hle hpow)
  have hJQ : J ≤ Q := Ideal.span_le.mpr (by simpa only [Set.singleton_subset_iff] using hroot)
  exact (hJ.eq_of_le hQ.ne_top hJQ).symm

/-- For the actual domain root algebra, Eisenstein and monicity give a genuine DVR. -/
theorem monic_eisenstein_adjoinRoot_dvr {R : Type} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (f : R[X]) [IsDomain (AdjoinRoot f)]
    (hf : f.Monic) (hd : 0 < f.natDegree) (π : R) (hπ : Prime π)
    (h0 : f.coeff 0 = π) (he : f.IsEisensteinAt (Ideal.span {π})) :
    IsDiscreteValuationRing (AdjoinRoot f) := by
  haveI : Module.Finite R (AdjoinRoot f) := hf.finite_adjoinRoot
  haveI : IsLocalRing (AdjoinRoot f) := monic_eisenstein_adjoinRoot_local f hf π hπ h0 he
  have hinj : Function.Injective (algebraMap R (AdjoinRoot f)) := by
    apply AdjoinRoot.of.injective_of_degree_ne_zero
    intro h
    exact (Nat.ne_of_gt hd) (Polynomial.natDegree_eq_of_degree_eq_some h)
  have hnf : ¬IsField (AdjoinRoot f) := fun h =>
    IsDiscreteValuationRing.not_isField R (isField_of_isIntegral_of_isField hinj h)
  apply ((IsDiscreteValuationRing.TFAE (AdjoinRoot f) hnf).out 4 0).mp
  have hmax : (Ideal.span {AdjoinRoot.root f} : Ideal (AdjoinRoot f)) = maximalIdeal (AdjoinRoot f) :=
    IsLocalRing.eq_maximalIdeal (prime_constant_adjoinRoot_root_maximal f π hπ h0)
  rw [← hmax]
  infer_instance

end
end Dubon2026
