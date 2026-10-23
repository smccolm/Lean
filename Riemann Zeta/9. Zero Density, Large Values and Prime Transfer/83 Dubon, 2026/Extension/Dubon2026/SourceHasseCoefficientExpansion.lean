import Dubon2026.SourceLevelOneJPolynomial
import Dubon2026.SourceModularJTranscendence
import Mathlib.Algebra.Polynomial.Lifts

/-! DUB-17/18 -> original Frobenius/inertia -> good reduction -> exact
residue-field degree -> prime j nonmembership -> Hasse polynomial.
The existing level-one polynomial theorem supplies the complex identity.
The integral, unitriangular q-expansions descend its coefficients to integers.
This proves the exact polynomial identity needed downstream, not prime
nonmembership or good reduction by itself.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_StarBank_hassePolyDescent. Existing local j powers and the
level-one polynomial theorem are reused. No resource or pin changes. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial HahnSeries UpperHalfPlane
open scoped MatrixGroups

theorem powerSeries_map_intCast_self (u : PowerSeries ℤ) : u.map (Int.castRingHom ℤ) = u := by
  rw [RingHom.ext_int (Int.castRingHom ℤ) (RingHom.id ℤ)]
  exact congrFun PowerSeries.map_id u

theorem jqModC_pow_mul_etaBlock (K : Type*) [CommRing K] (a N : ℕ) :
    jqModC K ^ a
        * (HahnSeries.single (1 : ℤ) 1
            * HahnSeries.ofPowerSeries ℤ K (dedekindEtaUnit.map (Int.castRingHom K))) ^ N
      = HahnSeries.single ((N : ℤ) - a) 1
        * HahnSeries.ofPowerSeries ℤ K
            (jNum.map (Int.castRingHom K) ^ a * dedekindEtaUnit.map (Int.castRingHom K) ^ N) := by
  have h1 : N • (1 : ℤ) = (N : ℤ) := by simp
  rw [jqModC_pow, mul_pow, HahnSeries.single_pow, one_pow, h1,
    show (HahnSeries.ofPowerSeries ℤ K (dedekindEtaUnit.map (Int.castRingHom K))) ^ N
        = HahnSeries.ofPowerSeries ℤ K (dedekindEtaUnit.map (Int.castRingHom K) ^ N) from
      (map_pow _ _ _).symm,
    mul_mul_mul_comm, HahnSeries.single_mul_single, one_mul,
    show HahnSeries.ofPowerSeries ℤ K (jNum.map (Int.castRingHom K) ^ a)
          * HahnSeries.ofPowerSeries ℤ K (dedekindEtaUnit.map (Int.castRingHom K) ^ N)
        = HahnSeries.ofPowerSeries ℤ K (jNum.map (Int.castRingHom K) ^ a
            * dedekindEtaUnit.map (Int.castRingHom K) ^ N) from (map_mul _ _ _).symm,
    show (-(a : ℤ) + (N : ℤ)) = (N : ℤ) - a from by ring]

theorem coeff_single_mul_ofPowerSeries_nonneg {K : Type*} [Semiring K] (c : ℤ)
    (U : PowerSeries K) (n : ℕ) :
    (HahnSeries.single c (1 : K) * HahnSeries.ofPowerSeries ℤ K U).coeff (c + (n : ℤ))
      = PowerSeries.coeff n U := by
  rw [HahnSeries.coeff_single_mul, one_mul, add_sub_cancel_left]
  exact HahnSeries.ofPowerSeries_apply_coeff U n

theorem coeff_single_mul_ofPowerSeries_neg {K : Type*} [Semiring K] (c : ℤ)
    (U : PowerSeries K) {g : ℤ} (hg : g < c) :
    (HahnSeries.single c (1 : K) * HahnSeries.ofPowerSeries ℤ K U).coeff g = 0 := by
  rw [HahnSeries.coeff_single_mul, one_mul,
    ofPowerSeries_coeff_of_neg _ (show g - c < 0 by omega)]

theorem coeff_ofPowerSeries_map (U : PowerSeries ℤ) (g : ℤ) :
    (HahnSeries.ofPowerSeries ℤ ℂ (U.map (Int.castRingHom ℂ))).coeff g
      = (((HahnSeries.ofPowerSeries ℤ ℤ U).coeff g : ℤ) : ℂ) := by
  rcases le_or_gt 0 g with hg | hg
  · lift g to ℕ using hg
    rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff,
      PowerSeries.coeff_map, Int.coe_castRingHom]
  · rw [ofPowerSeries_coeff_of_neg _ hg,
      ofPowerSeries_coeff_of_neg _ hg, Int.cast_zero]

theorem algebraMap_laurent_eq_single (K : Type*) [CommRing K] (c : K) :
    algebraMap K (LaurentSeries K) c = HahnSeries.single (0 : ℤ) c := by
  have h1 : algebraMap K (PowerSeries K) c = PowerSeries.C c := by simp
  rw [HahnSeries.algebraMap_apply', h1, HahnSeries.ofPowerSeries_C]
  rfl


end
end Dubon2026.SourceFunctionField
