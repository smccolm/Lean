import Dubon2026.AlgebraicLocalInertia
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Algebra.Ring.GeomSum

/-! Prime-to-residue-characteristic roots retain their order under reduction.
These elementary inputs serve the actual finite inertia quotient depth in
DUB-17's unramified continuous H1 dimension theorem. -/

namespace Dubon2026
noncomputable section

/-- Reduction detects a torsion element of order invertible in the residue field. -/
theorem local_eq_one_of_residue_eq_one_of_pow_eq_one
    {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
    {u : R} {m : ℕ} (hu : u ^ m = 1)
    (hm : (m : IsLocalRing.ResidueField R) ≠ 0)
    (hr : IsLocalRing.residue R u = 1) : u = 1 := by
  by_contra h
  have hs : (∑ i ∈ Finset.range m, u ^ i) * (u - 1) = 0 := by
    rw [geom_sum_mul, hu, sub_self]
  have hz := (mul_eq_zero.mp hs).resolve_right (sub_ne_zero.mpr h)
  apply hm
  have he := congrArg (IsLocalRing.residue R) hz
  simpa [map_sum, map_pow, hr] using he

/-- Divisibility of these geometric periods detects divisibility of their exponents. -/
theorem local_exponent_dvd_of_pow_sub_one_dvd {a n j : ℕ}
    (ha : 2 ≤ a) (h : a ^ n - 1 ∣ a ^ j - 1) : n ∣ j := by
  have hg := Nat.pow_sub_one_gcd_pow_sub_one a n j
  rw [Nat.gcd_eq_left h] at hg
  have hn : 1 ≤ a ^ n := Nat.one_le_pow _ _ (by omega)
  have hd : 1 ≤ a ^ Nat.gcd n j := Nat.one_le_pow _ _ (by omega)
  have he : a ^ Nat.gcd n j = a ^ n := by omega
  have he' := Nat.pow_right_injective ha he
  rw [← he']
  exact Nat.gcd_dvd_right n j

variable (K L : Type) [NontriviallyNormedField K] [NormedField L]
  [NormedAlgebra K L] [IsUltrametricDist K] [IsUltrametricDist L]

attribute [local instance] algebraicLocalIntegerBaseAlgebra

/-- The cardinal of the actual finite base residue field vanishes in the
original extension residue field, via the actual integer inclusion. -/
theorem algebraicLocal_residue_cast_card_eq_zero
    [Finite (IsLocalRing.ResidueField (algebraicLocalIntegerRing K))] :
    (Nat.card (IsLocalRing.ResidueField (algebraicLocalIntegerRing K)) :
      IsLocalRing.ResidueField (algebraicLocalIntegerRing L)) = 0 := by
  let q := Nat.card (IsLocalRing.ResidueField (algebraicLocalIntegerRing K))
  letI : Fintype (IsLocalRing.ResidueField (algebraicLocalIntegerRing K)) := Fintype.ofFinite _
  have hq : IsLocalRing.residue (algebraicLocalIntegerRing K)
      (q : algebraicLocalIntegerRing K) = 0 := by
    rw [map_natCast]
    simpa only [q, Nat.card_eq_fintype_card] using
      Nat.cast_card_eq_zero (IsLocalRing.ResidueField (algebraicLocalIntegerRing K))
  have hm := (IsLocalRing.residue_eq_zero_iff _).mp hq
  rw [← algebraicLocalInteger_maximalIdeal_under K L] at hm
  change algebraMap (algebraicLocalIntegerRing K) (algebraicLocalIntegerRing L)
    (q : algebraicLocalIntegerRing K) ∈ IsLocalRing.maximalIdeal _ at hm
  rw [map_natCast] at hm
  rw [← map_natCast (IsLocalRing.residue (algebraicLocalIntegerRing L))]
  exact (IsLocalRing.residue_eq_zero_iff _).mpr hm

end
end Dubon2026
