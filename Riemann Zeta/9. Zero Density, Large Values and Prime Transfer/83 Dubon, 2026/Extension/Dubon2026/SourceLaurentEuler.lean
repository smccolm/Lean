import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic

/-! DUB-17/18 -> parabolic Hecke realization -> period surjectivity ->
matching cusp-form dimension lower bound -> regular differential realization
with injective q-expansion. This selected foundation constructs the literal
q d/dq derivation and its map on Kaehler differentials. The original-field application is assembled in
SourceOriginalDifferentialInjectivity with transcendence and separability
proved. Regularity, geometric genus and cusp-form realization remain required.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
Definitions/Def_ModularCurve_HeckeDifferential.lean, Euler section.
-/
namespace Dubon2026.SourceDifferential
noncomputable section
open HahnSeries

section Euler

variable (R : Type*) [CommRing R]

/-- The actual coefficient formula for q times the formal derivative. -/
def qEulerFun (x : LaurentSeries R) : LaurentSeries R where
  coeff n := (n : R) * x.coeff n
  isPWO_support' := x.isPWO_support.mono fun n hn => by
    simp only [Function.mem_support, ne_eq] at hn ⊢
    intro h
    exact hn (by rw [h, mul_zero])

@[simp] theorem qEulerFun_coeff (x : LaurentSeries R) (n : ℤ) :
    (qEulerFun R x).coeff n = (n : R) * x.coeff n := rfl

theorem support_qEulerFun_subset (x : LaurentSeries R) :
    (qEulerFun R x).support ⊆ x.support := fun n hn => by
  contrapose! hn
  simp only [mem_support, ne_eq, not_not] at hn ⊢
  rw [qEulerFun_coeff, hn, mul_zero]

theorem algebraMap_laurentSeries_apply_alt (c : R) :
    algebraMap R (LaurentSeries R) c = single 0 c := by
  have h1 : algebraMap R (PowerSeries R) c = PowerSeries.C c := by simp
  rw [HahnSeries.algebraMap_apply', h1, HahnSeries.ofPowerSeries_C]
  rfl

/-- The proved q d/dq derivation on Laurent series. -/
def qEuler : Derivation R (LaurentSeries R) (LaurentSeries R) where
  toFun := qEulerFun R
  map_add' x y := by
    ext n
    simp only [qEulerFun_coeff, coeff_add, mul_add]
  map_smul' r x := by
    ext n
    simp only [RingHom.id_apply, qEulerFun_coeff]
    rw [Algebra.smul_def, algebraMap_laurentSeries_apply_alt, coeff_single_zero_mul, HahnSeries.coeff_smul,
      qEulerFun_coeff, smul_eq_mul]
    ring
  map_one_eq_zero' := by
    ext n
    simp only [LinearMap.coe_mk, AddHom.coe_mk, qEulerFun_coeff, coeff_zero]
    by_cases hn : n = 0
    · subst hn; simp
    · rw [coeff_one, if_neg hn, mul_zero]
  leibniz' x y := by
    ext a
    simp only [LinearMap.coe_mk, AddHom.coe_mk, qEulerFun_coeff, coeff_add', Pi.add_apply,
      smul_eq_mul]
    rw [coeff_mul,
      coeff_mul_right' (x := x) (y := qEulerFun R y) y.isPWO_support (support_qEulerFun_subset R y),
      coeff_mul_right' (x := y) (y := qEulerFun R x) x.isPWO_support (support_qEulerFun_subset R x),
      Finset.mul_sum]
    have hswap : ∑ ij ∈ Finset.addAntidiagonal y.isPWO_support x.isPWO_support a,
        y.coeff ij.1 * (qEulerFun R x).coeff ij.2
        = ∑ ij ∈ Finset.addAntidiagonal x.isPWO_support y.isPWO_support a,
            (ij.1 : R) * x.coeff ij.1 * y.coeff ij.2 := by
      refine Finset.sum_nbij' Prod.swap Prod.swap ?_ ?_ ?_ ?_ ?_
      · intro ij hij
        exact Finset.swap_mem_addAntidiagonal.mpr hij
      · intro ij hij
        exact Finset.swap_mem_addAntidiagonal.mpr hij
      · intro ij _; rfl
      · intro ij _; rfl
      · intro ij _
        simp only [Prod.fst_swap, Prod.snd_swap, qEulerFun_coeff]
        ring
    rw [hswap, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ij hij => ?_
    rw [Finset.mem_addAntidiagonal] at hij
    rw [qEulerFun_coeff, ← hij.2.2, Int.cast_add]
    ring

@[simp] theorem qEuler_coeff (x : LaurentSeries R) (n : ℤ) :
    (qEuler R x).coeff n = (n : R) * x.coeff n := rfl

theorem qEuler_single (n : ℤ) (r : R) :
    qEuler R (single n r) = single n ((n : R) * r) := by
  ext m
  by_cases h : m = n
  · subst h; simp
  · simp [coeff_single_of_ne h]

end Euler

end
end Dubon2026.SourceDifferential
