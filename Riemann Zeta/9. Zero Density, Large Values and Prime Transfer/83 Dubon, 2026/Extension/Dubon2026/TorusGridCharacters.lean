import Dubon2026.TorusEquidistribution
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! # Exact character averages on finite grids of the prime torus -/

namespace Dubon2026

open scoped BigOperators

noncomputable section

/-- The full product grid with `m` equally spaced points in each prime coordinate. -/
def torusGridPoint (N m : ℕ) [NeZero m] (j : PrimeCoordinate N → ZMod m) : PrimeTorus N :=
  fun p => ZMod.toAddCircle (j p)

theorem fourier_toAddCircle (m : ℕ) [NeZero m] (k : ℤ) (j : ZMod m) :
    fourier k (ZMod.toAddCircle j) = ZMod.stdAddChar ((k : ZMod m) * j) := by
  change (AddCircle.toCircle (k • ZMod.toAddCircle j) : ℂ) =
    (AddCircle.toCircle (ZMod.toAddCircle ((k : ZMod m) * j)) : ℂ)
  rw [← map_zsmul, zsmul_eq_mul]

theorem sum_fourier_grid (m : ℕ) [NeZero m] (k : ℤ) :
    (∑ j : ZMod m, fourier k (ZMod.toAddCircle j)) = if (k : ZMod m) = 0 then (m : ℂ) else 0 := by
  classical
  simp only [fourier_toAddCircle]
  split_ifs with h
  · simp [h, ZMod.card]
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar m h)

theorem mFourier_add_point (N : ℕ) (k : PrimeCoordinate N → ℤ) (x y : PrimeTorus N) :
    UnitAddTorus.mFourier k (x + y) = UnitAddTorus.mFourier k x * UnitAddTorus.mFourier k y := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.add_apply, fourier_apply,
    smul_add, AddCircle.toCircle_add, Circle.coe_mul, Finset.prod_mul_distrib]

theorem sum_mFourier_grid (N m : ℕ) [NeZero m] (k : PrimeCoordinate N → ℤ) :
    (∑ j : PrimeCoordinate N → ZMod m, UnitAddTorus.mFourier k (torusGridPoint N m j)) =
      ∏ p : PrimeCoordinate N, if (k p : ZMod m) = 0 then (m : ℂ) else 0 := by
  classical
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, torusGridPoint]
  rw [← Fintype.prod_sum (fun (p : PrimeCoordinate N) (j : ZMod m) =>
    fourier (k p) (ZMod.toAddCircle j))]
  exact Finset.prod_congr rfl (fun p _ => sum_fourier_grid m (k p))

theorem sum_mFourier_grid_eq_zero {N m : ℕ} [NeZero m] (k : PrimeCoordinate N → ℤ)
    {p : PrimeCoordinate N} (hp : (k p : ZMod m) ≠ 0) :
    (∑ j : PrimeCoordinate N → ZMod m, UnitAddTorus.mFourier k (torusGridPoint N m j)) = 0 := by
  rw [sum_mFourier_grid]
  exact Finset.prod_eq_zero (Finset.mem_univ p) (if_neg hp)

theorem intCast_zmod_ne_zero_of_natAbs_lt {k : ℤ} (hk : k ≠ 0) {m : ℕ}
    (hm : k.natAbs < m) : (k : ZMod m) ≠ 0 := by
  intro h
  apply hk
  exact Int.eq_zero_of_dvd_of_natAbs_lt_natAbs
    ((ZMod.intCast_zmod_eq_zero_iff_dvd k m).mp h) (by simpa using hm)

end

end Dubon2026
