import Dubon2026.SourceModularJSeries

/-! DUB-17/18 -> parabolic Hecke realization -> period surjectivity ->
matching cusp-form lower dimension bound -> regular differential realization.
This selects the original Laurent-series modular function field and its
literal j series. The analytic modularity and finite extension are assembled in
SourceOriginalDifferentialInjectivity. Regularity, geometric genus and
cusp-form realization remain separate proof obligations.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
Definitions/Def_ModularCurve_JqCoeff.lean, JExpansion section.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open HahnSeries IntermediateField

section JExpansion

variable (K : Type*) [CommRing K]

/-- The original j Laurent series over the specified coefficient ring. -/
def jqModC : LaurentSeries K :=
  HahnSeries.single (-1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ K (jNum.map (Int.castRingHom K))

/-- The original level-substituted j Laurent series over the coefficient ring. -/
def jqNModC (N : ℕ) [NeZero N] : LaurentSeries K := qExpand K N (jqModC K)

@[simp]
theorem jqNModC_one : jqNModC K 1 = jqModC K := qExpand_one_apply _

theorem jqModC_rat : jqModC ℚ = jq := rfl

variable {K} in

theorem map_jqModC {K' : Type*} [CommRing K'] (f : K →+* K') :
    (jqModC K).map f = jqModC K' := by
  have hmul : ∀ x y : LaurentSeries K, (x * y).map f = x.map f * y.map f :=
    fun x y => HahnSeries.map_mul f.toNonUnitalRingHom
  have hsingle : (HahnSeries.single (-1 : ℤ) (1 : K)).map f = HahnSeries.single (-1 : ℤ) 1 := by
    ext g
    rw [HahnSeries.map_coeff, HahnSeries.coeff_single, HahnSeries.coeff_single, apply_ite f,
      map_one, map_zero]
  have hseries : ∀ u : PowerSeries K,
      (HahnSeries.ofPowerSeries ℤ K u).map f = HahnSeries.ofPowerSeries ℤ K' (u.map f) := by
    intro u
    ext k
    rw [HahnSeries.map_coeff]
    rcases le_or_gt 0 k with hk | hk
    · lift k to ℕ using hk
      rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff,
        PowerSeries.coeff_map]
    · rw [ofPowerSeries_coeff_of_neg _ hk, ofPowerSeries_coeff_of_neg _ hk, map_zero]
  rw [jqModC, jqModC, hmul, hsingle, hseries,
    show (jNum.map (Int.castRingHom K)).map f = jNum.map (Int.castRingHom K') from by
      rw [show PowerSeries.map f (PowerSeries.map (Int.castRingHom K) jNum)
            = PowerSeries.map (f.comp (Int.castRingHom K)) jNum from
          (congrFun (congrArg DFunLike.coe (PowerSeries.map_comp (Int.castRingHom K) f)) jNum).symm,
        RingHom.ext_int (f.comp (Int.castRingHom K)) (Int.castRingHom K')]]

theorem jqModC_eq_map_intCast : jqModC K = (jqModC ℤ).map (Int.castRingHom K) :=
  (map_jqModC (Int.castRingHom K)).symm

end JExpansion

end
end Dubon2026.SourceFunctionField
