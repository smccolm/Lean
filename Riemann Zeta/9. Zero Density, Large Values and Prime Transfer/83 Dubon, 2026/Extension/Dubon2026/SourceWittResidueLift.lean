import Mathlib.RingTheory.WittVector.DiscreteValuationRing
import Mathlib.RingTheory.WittVector.Complete
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! The minimal Witt-vector inputs for the odd-prime quotient product in
positive characteristic. The residue-map argument is adapted from
anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_WittVector_exists_valuationSubring_lift_with_transcendental.lean.txt
(Apache-2.0). Native nonvanishing of p replaces its duplicate coefficient proof.
No power-series perturbation or transcendental lifting is required. -/

namespace Dubon2026.SourceWittLift
open WittVector IsLocalRing
noncomputable section
variable (p : ℕ) [hp : Fact p.Prime] (K : Type*) [Field K] [CharP K p]

/-- The native Witt ring of a perfect field of prime characteristic has characteristic zero. -/
theorem witt_charZero [PerfectRing K p] : CharZero (WittVector p K) := by
  refine charZero_of_inj_zero fun n hn => ?_
  by_contra hn0
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 p hp.out.ne_one
  have hmunit : IsUnit (m : WittVector p K) := by
    apply isUnit_of_coeff_zero_ne_zero
    rw [← constantCoeff_apply, map_natCast]
    exact fun h0 => hm ((CharP.cast_eq_zero_iff K p m).mp h0)
  rw [Nat.cast_mul, Nat.cast_pow] at hn
  exact pow_ne_zero a (WittVector.p_nonzero p K) (hmunit.mul_left_eq_zero.mp hn)

/-- The residue characteristic is a nonunit in the Witt ring. -/
theorem witt_not_isUnit_p : ¬ IsUnit (p : WittVector p K) := by
  intro hu
  have h := hu.map (constantCoeff : WittVector p K →+* K)
  rw [map_natCast, CharP.cast_eq_zero] at h
  exact not_isUnit_zero h

/-- A local map from the Witt ring induces the original field's residue embedding. -/
def residueMap [PerfectRing K p] {A : Type*} [CommRing A] [IsLocalRing A]
    (f : WittVector p K →+* A) [IsLocalHom f] : K →+* ResidueField A :=
  RingHom.liftOfRightInverse (constantCoeff : WittVector p K →+* K) (teichmuller p)
    (fun a => by rw [constantCoeff_apply, teichmuller_coeff_zero])
    ⟨(residue A).comp f, by
      rw [ker_constantCoeff, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe,
        RingHom.mem_ker, RingHom.comp_apply, residue_eq_zero_iff, mem_maximalIdeal,
        mem_nonunits_iff]
      exact fun hu => witt_not_isUnit_p p K (IsUnit.of_map f _ hu)⟩

/-- The induced residue embedding agrees with the given local map on constant coefficients. -/
theorem residueMap_constantCoeff [PerfectRing K p] {A : Type*} [CommRing A] [IsLocalRing A]
    (f : WittVector p K →+* A) [IsLocalHom f] (x : WittVector p K) :
    residueMap p K f (constantCoeff x) = residue A (f x) :=
  RingHom.liftOfRightInverse_comp_apply _ _ _ _ x

/-- Teichmuller representatives reduce to the original field elements. -/
theorem residueMap_teichmuller [PerfectRing K p] {A : Type*} [CommRing A] [IsLocalRing A]
    (f : WittVector p K →+* A) [IsLocalHom f] (a : K) :
    residueMap p K f a = residue A (f (teichmuller p a)) := by
  simpa only [constantCoeff_apply, teichmuller_coeff_zero] using
    residueMap_constantCoeff p K f (teichmuller p a)

end
end Dubon2026.SourceWittLift
