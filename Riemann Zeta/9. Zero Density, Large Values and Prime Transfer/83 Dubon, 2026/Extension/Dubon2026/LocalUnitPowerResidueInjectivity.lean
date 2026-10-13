import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.RingTheory.Valuation.Integers
import Mathlib.RingTheory.Valuation.ValuationSubring

/-! # Unit-exponent roots cannot disappear in the residue field

The geometric-sum identity shows that a root of unity reducing to one is
one when its exponent is a unit. Applied to the ratio of an inertia
translate of a unit Kummer root and that root, this will force inertia to
fix the generating root. The existing original inertia/ramification theorem
then supplies the unramifiedness input to DUB-17's principal localization
norm correction, without a new different or etale-algebra construction.
-/
namespace Dubon2026
noncomputable section

/-- With unit exponent, the residue map is injective on roots reducing to
one in the actual local domain. -/
theorem localRing_unitExponent_root_eq_one
    {A : Type*} [CommRing A] [IsDomain A] [IsLocalRing A]
    (n : ℕ) (hn : IsUnit (n : A)) (z : A)
    (hPow : z ^ n = 1) (hResidue : IsLocalRing.residue A z = 1) : z = 1 := by
  by_contra hz
  have hSum : ∑ i ∈ Finset.range n, z ^ i = 0 := by
    have h := geom_sum_mul z n
    rw [hPow, sub_self] at h
    exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr hz)
  have hZero : (n : IsLocalRing.ResidueField A) = 0 := by
    have h := congrArg (IsLocalRing.residue A) hSum
    simpa only [map_sum, map_pow, hResidue, one_pow, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, mul_one, map_zero] using h
  have hUnit : IsUnit (n : IsLocalRing.ResidueField A) := by
    simpa only [map_natCast] using hn.map (IsLocalRing.residue A)
  exact hUnit.ne_zero hZero

/-- In the actual valuation ring, a unit-exponent root of unity strictly
closer than one to one is one. -/
theorem valuation_unitExponent_root_eq_one
    {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) (n : ℕ) (hn : v (n : K) = 1) (z : K)
    (hz : v z = 1) (hClose : v (z - 1) < 1) (hPow : z ^ n = 1) : z = 1 := by
  let a : v.integer := ⟨z, hz.le⟩
  have hnUnit : IsUnit (n : v.integer) :=
    (Valuation.integer.integers v).isUnit_iff_valuation_eq_one.mpr hn
  have haPow : a ^ n = 1 := Subtype.ext hPow
  have haResidue : IsLocalRing.residue v.integer a = 1 := by
    apply sub_eq_zero.mp
    change IsLocalRing.residue v.integer a - IsLocalRing.residue v.integer 1 = 0
    rw [← map_sub, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal]
    change ¬ IsUnit (a - 1)
    rw [Valuation.Integer.not_isUnit_iff_valuation_lt_one]
    exact hClose
  exact congrArg Subtype.val (localRing_unitExponent_root_eq_one n hnUnit a haPow haResidue)

end
end Dubon2026
