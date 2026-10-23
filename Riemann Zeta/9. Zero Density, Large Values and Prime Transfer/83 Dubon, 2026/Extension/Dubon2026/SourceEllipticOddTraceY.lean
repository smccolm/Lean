import Dubon2026.SourceEllipticOddTraceX
import Dubon2026.SourceEllipticOddGenericY

/-! The actual normalized translation y-sum is the literal odd Velu y-sum.
The actual finite cyclic subgroup is paired using its proved order. The
paired chord identity identifies each term, in every field characteristic.
This discharges the invariant-coordinate identification needed for the
explicit quotient equation on the DUB-17/18 good-reduction dependency. -/

open WeierstrassCurve WeierstrassCurve.Affine
open Dubon2026.SourceEllipticVelu
open Dubon2026.SourceEllipticVelu.OddDiscriminant

namespace Dubon2026.SourceEllipticFunctionField

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic]
variable {Q : W.toAffine.Point} {n : ℕ}

/-- The normalized subgroup translation sum is the explicit odd quotient y-coordinate. -/
theorem translationTraceY_eq_genericVeluY (hQ : addOrderOf Q = 2 * n + 1) :
    @translationTraceY F _ _ W.toAffine _ (AddSubgroup.zmultiples Q)
      (finite_zmultiples_of_order hQ (by omega)) =
      genericVeluY W (oddOrderSummingSet W Q n) := by
  classical
  letI : Finite (AddSubgroup.zmultiples (Q : (W.toAffine⁄F).toAffine.Point)) :=
    finite_zmultiples_of_order hQ (by omega)
  rw [translationTraceY]
  trans ∑ j ∈ Finset.range (2 * n + 1),
    (translation W.toAffine (j • Q) (genericY W.toAffine) -
      algebraMap F W.toAffine.FunctionField (coordsOrZero (j • Q)).2)
  · exact sum_zmultiples_eq_range hQ (by omega)
      (fun P : W.toAffine.Point => translation W.toAffine P (genericY W.toAffine) -
        algebraMap F W.toAffine.FunctionField (coordsOrZero P).2)
  rw [sum_odd_multiples_fold hQ
    (fun P : W.toAffine.Point => translation W.toAffine P (genericY W.toAffine) -
      algebraMap F W.toAffine.FunctionField (coordsOrZero P).2)]
  have hz : translation W.toAffine (0 : W.toAffine.Point) = 1 := translation_zero W.toAffine
  rw [hz, AlgEquiv.one_apply]
  change genericY W.toAffine - algebraMap F W.toAffine.FunctionField 0 + _ = _
  rw [map_zero, sub_zero, genericVeluY, oddOrderSummingSet,
    Finset.sum_image (coordsOrZero_odd_nsmul_injOn hQ), sub_eq_add_neg,
    ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  obtain ⟨x, y, hs, he, _hc⟩ := exists_affine_coords_of_ne_zero
    (kernel_ne_zero hQ (Finset.mem_Icc.mp hk).1 (by have := (Finset.mem_Icc.mp hk).2; omega))
  rw [he]
  have hp := translation_y_pair W.toAffine hs
  have hgx : veluGx (W.map (algebraMap F W.toAffine.FunctionField))
      (algebraMap F W.toAffine.FunctionField x) (algebraMap F W.toAffine.FunctionField y) =
      algebraMap F W.toAffine.FunctionField (veluGx W x y) := by
    simp [veluGx, map_ofNat]
  have hgy : veluGy (W.map (algebraMap F W.toAffine.FunctionField))
      (algebraMap F W.toAffine.FunctionField x) (algebraMap F W.toAffine.FunctionField y) =
      algebraMap F W.toAffine.FunctionField (veluGy W x y) := by
    simp [veluGy, map_ofNat]
  rw [Point.neg_some] at hp ⊢
  simp only [coordsOrZero]
  change translation W.toAffine (Point.some x y hs) (genericY W.toAffine) +
      translation W.toAffine (Point.some x (W.toAffine.negY x y) _) (genericY W.toAffine) = _ at hp
  simp only [WeierstrassCurve.baseChange, ← map_veluU, ← map_veluT, hgx, hgy,
    WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃] at hp
  simp only [negY, map_neg, map_sub, map_mul]
  linear_combination (norm := ring!) hp

end Dubon2026.SourceEllipticFunctionField
