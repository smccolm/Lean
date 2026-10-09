import Dubon2026.RationalFiniteIdeleFactorization
import Dubon2026.FiniteAdeleClassicalIntersection
import Mathlib.Data.Int.Order.Units

/-! # Uniqueness of the positive rational and integral-unit factors of a genuine finite idele -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain

/-- A positive rational number whose genuine finite adele is an integral unit equals one. -/
theorem finiteAdele_positive_rational_unit_eq_one (q : ℚ) (hq : 0 < q)
    (u : finiteAdeleIntegerSubringˣ)
    (hu : algebraMap ℚ (FiniteAdeleRing ℤ ℚ) q = u.val.val) : q = 1 := by
  have hq0 := ne_of_gt hq
  have hi : algebraMap ℚ (FiniteAdeleRing ℤ ℚ) q⁻¹ = u.inv.val := by
    have hmul : algebraMap ℚ (FiniteAdeleRing ℤ ℚ) q⁻¹ * u.val.val = 1 := by
      rw [← hu, ← map_mul, inv_mul_cancel₀ hq0, map_one]
    have huinv : u.val.val * u.inv.val = 1 := congrArg Subtype.val u.val_inv
    calc
      _ = algebraMap ℚ (FiniteAdeleRing ℤ ℚ) q⁻¹ * (u.val.val * u.inv.val) := by rw [huinv, mul_one]
      _ = _ := by rw [← mul_assoc, hmul, one_mul]
  obtain ⟨n, hn⟩ := (finiteAdele_rational_integral_iff q).mp (hu.symm ▸ u.val.property)
  obtain ⟨m, hm⟩ := (finiteAdele_rational_integral_iff q⁻¹).mp (hi.symm ▸ u.inv.property)
  have hnm : n * m = 1 := by
    apply Int.cast_injective (α := ℚ)
    rw [Int.cast_mul, Int.cast_one, hn, hm, mul_inv_cancel₀ hq0]
  have hnunit : IsUnit n := isUnit_iff_exists_inv.mpr ⟨m, hnm⟩
  have hnpos : 0 < n := by
    have hnpos' : (0 : ℚ) < n := hn.symm ▸ hq
    exact_mod_cast hnpos'
  have hn1 : n = 1 := by
    simpa only [abs_of_pos hnpos] using Int.isUnit_iff_abs_eq.mp hnunit
  rw [← hn, hn1, Int.cast_one]

/-- Two actual positive-rational times integral-unit factorizations have the same positive rational factor. -/
theorem finiteIdele_positive_factor_unique (q r : ℚ) (hq : 0 < q) (hr : 0 < r)
    (u v : finiteAdeleIntegerSubringˣ)
    (h : algebraMap ℚ (FiniteAdeleRing ℤ ℚ) q * u.val.val =
      algebraMap ℚ (FiniteAdeleRing ℤ ℚ) r * v.val.val) : q = r := by
  have huinv : u.val.val * u.inv.val = 1 := congrArg Subtype.val u.val_inv
  have he : algebraMap ℚ (FiniteAdeleRing ℤ ℚ) (q / r) = (v * u⁻¹).val.val := by
    calc
      _ = algebraMap ℚ (FiniteAdeleRing ℤ ℚ) r⁻¹ *
          (algebraMap ℚ (FiniteAdeleRing ℤ ℚ) q * u.val.val) * u.inv.val := by
        rw [div_eq_mul_inv, map_mul]
        calc
          _ = (algebraMap ℚ (FiniteAdeleRing ℤ ℚ) q * algebraMap ℚ (FiniteAdeleRing ℤ ℚ) r⁻¹) *
              (u.val.val * u.inv.val) := by rw [huinv, mul_one]
          _ = _ := by ring
      _ = _ := by
        rw [h, ← mul_assoc, ← map_mul, inv_mul_cancel₀ (ne_of_gt hr), map_one, one_mul]
        rfl
  exact (div_eq_one_iff_eq (ne_of_gt hr)).mp
    (finiteAdele_positive_rational_unit_eq_one (q / r) (div_pos hq hr) (v * u⁻¹) he)

/-- The integral units in two genuine positive rational factorizations are equal as actual units. -/
theorem finiteIdele_integral_factor_unique (q r : ℚ) (hq : 0 < q) (hr : 0 < r)
    (u v : finiteAdeleIntegerSubringˣ)
    (h : algebraMap ℚ (FiniteAdeleRing ℤ ℚ) q * u.val.val =
      algebraMap ℚ (FiniteAdeleRing ℤ ℚ) r * v.val.val) : u = v := by
  have hqr := finiteIdele_positive_factor_unique q r hq hr u v h
  subst r
  have he := congrArg (fun x : FiniteAdeleRing ℤ ℚ => algebraMap ℚ (FiniteAdeleRing ℤ ℚ) q⁻¹ * x) h
  simp only [← mul_assoc, ← map_mul, inv_mul_cancel₀ (ne_of_gt hq), map_one, one_mul] at he
  exact Units.ext (Subtype.ext he)

end
end Dubon2026
