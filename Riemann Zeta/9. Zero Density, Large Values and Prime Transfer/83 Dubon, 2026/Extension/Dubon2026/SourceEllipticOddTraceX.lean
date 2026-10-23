import Dubon2026.SourceEllipticOddSubgroupSum
import Dubon2026.SourceEllipticTranslationPairs
import Dubon2026.SourceEllipticOddGenericCoordinate
import Dubon2026.SourceEllipticOddBaseChange
import Dubon2026.SourceEllipticOddOrbitInvariance

/-! The actual invariant translation x-sum equals the literal odd Velu x-sum.
The actual finite cyclic subgroup is paired by native order enumeration, and
the existing chord identity supplies each summand. This identifies the field
action's invariant with the already proved explicit rational coordinate. -/

open WeierstrassCurve WeierstrassCurve.Affine
open Dubon2026.SourceEllipticVelu
open Dubon2026.SourceEllipticVelu.OddDiscriminant
open Dubon2026.SourceEllipticVelu.OddDiscriminant.Algebra

namespace Dubon2026.SourceEllipticFunctionField

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic]
variable {Q : W.toAffine.Point} {n : ℕ}

/-- The normalized subgroup translation sum is the actual explicit odd quotient x-coordinate. -/
theorem translationTraceX_eq_genericVeluX (hQ : addOrderOf Q = 2 * n + 1) :
    @translationTraceX F _ _ W.toAffine _ (AddSubgroup.zmultiples Q)
      (finite_zmultiples_of_order hQ (by omega)) =
      genericVeluX W (oddOrderSummingSet W Q n) := by
  classical
  letI : Finite (AddSubgroup.zmultiples (Q : (W.toAffine⁄F).toAffine.Point)) :=
    finite_zmultiples_of_order hQ (by omega)
  rw [translationTraceX]
  trans ∑ j ∈ Finset.range (2 * n + 1),
    (translation W.toAffine (j • Q) (genericX W.toAffine) -
      algebraMap F W.toAffine.FunctionField (coordsOrZero (j • Q)).1)
  · exact sum_zmultiples_eq_range hQ (by omega)
      (fun P : W.toAffine.Point => translation W.toAffine P (genericX W.toAffine) -
        algebraMap F W.toAffine.FunctionField (coordsOrZero P).1)
  rw [sum_odd_multiples_fold hQ
    (fun P : W.toAffine.Point => translation W.toAffine P (genericX W.toAffine) -
      algebraMap F W.toAffine.FunctionField (coordsOrZero P).1)]
  have hz : translation W.toAffine (0 : W.toAffine.Point) = 1 := translation_zero W.toAffine
  rw [hz, AlgEquiv.one_apply]
  change genericX W.toAffine - algebraMap F W.toAffine.FunctionField 0 + _ = _
  rw [map_zero, sub_zero, genericVeluX, Xv, oddOrderSummingSet,
    Finset.sum_image (coordsOrZero_odd_nsmul_injOn hQ)]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  obtain ⟨x, y, hs, he, _hc⟩ := exists_affine_coords_of_ne_zero
    (kernel_ne_zero hQ (Finset.mem_Icc.mp hk).1 (by have := (Finset.mem_Icc.mp hk).2; omega))
  rw [he]
  have hp := translation_x_pair W.toAffine hs
  change _ = 2 * algebraMap F W.toAffine.FunctionField x +
    veluT (W.map (algebraMap F W.toAffine.FunctionField))
      (algebraMap F W.toAffine.FunctionField x) (algebraMap F W.toAffine.FunctionField y) /
        (genericX W.toAffine - algebraMap F W.toAffine.FunctionField x) +
    veluU (W.map (algebraMap F W.toAffine.FunctionField))
      (algebraMap F W.toAffine.FunctionField x) (algebraMap F W.toAffine.FunctionField y) /
        (genericX W.toAffine - algebraMap F W.toAffine.FunctionField x) ^ 2 at hp
  rw [← map_veluT, ← map_veluU] at hp
  rw [Point.neg_some] at hp ⊢
  simp only [coordsOrZero]
  change translation W.toAffine (Point.some x y hs) (genericX W.toAffine) +
      translation W.toAffine (Point.some x (W.toAffine.negY x y) _) (genericX W.toAffine) = _ at hp
  linear_combination (norm := ring!) hp

end Dubon2026.SourceEllipticFunctionField
