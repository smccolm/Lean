import Dubon2026.SourceEllipticFixedCurvePointMap
import Dubon2026.SourceEllipticVariableAddEquiv

/-! The lifted field automorphism commutes with the original point inclusion.
The actual coefficient-fixed point maps satisfy this identity on both finite
points and infinity. This is the exact naturality input for the descended
cyclic-root equivalence in the DUB-17/18 inertia and place-fiber comparison. -/
namespace Dubon2026.SourceEllipticVelu
open WeierstrassCurve WeierstrassCurve.Affine OddDiscriminant
open SourceEllipticVariableChange
noncomputable section

private theorem fixedCurvePointMap_some
    {F : Type*} [Field F] [DecidableEq F]
    (g : F →+* F) (W : WeierstrassCurve F) (hW : W.map g = W) {x y : F}
    (hP : W.toAffine.Nonsingular x y) (hQ : W.toAffine.Nonsingular (g x) (g y)) :
    fixedCurvePointMap g W hW (Point.some x y hP) = Point.some (g x) (g y) hQ := by
  have hc : ∀ (V : WeierstrassCurve F) (hV : W.map g = V)
      (hVQ : V.toAffine.Nonsingular (g x) (g y)),
      AddEquiv.cast (M := fun U : WeierstrassCurve F => U.toAffine.Point) hV
        (pointMapHom g W (Point.some x y hP)) = Point.some (g x) (g y) hVQ := by
    rintro V rfl hVQ
    rfl
  exact hc W hW hQ

theorem fixedCurvePointMap_naturality
    {F L : Type*} [Field F] [Field L] [DecidableEq F] [DecidableEq L]
    (f : F →+* L) (W : WeierstrassCurve F)
    (g : F →+* F) (hW : W.map g = W)
    (g' : L →+* L) (hV : (W.map f).map g' = W.map f)
    (hfg : ∀ x, g' (f x) = f (g x)) :
    (pointMapHom f W).comp (fixedCurvePointMap g W hW) =
      (fixedCurvePointMap g' (W.map f) hV).comp (pointMapHom f W) := by
  ext P
  cases P with
  | zero =>
    change ((pointMapHom f W).comp (fixedCurvePointMap g W hW)) 0 =
      ((fixedCurvePointMap g' (W.map f) hV).comp (pointMapHom f W)) 0
    exact (map_zero _).trans (map_zero _).symm
  | some x y h =>
    have hg : W.toAffine.Nonsingular (g x) (g y) := by
      rw [← hW]
      exact (W.toAffine.map_nonsingular g.injective x y).mpr h
    have hf : (W.map f).toAffine.Nonsingular (f x) (f y) :=
      (W.toAffine.map_nonsingular f.injective x y).mpr h
    have hg' : (W.map f).toAffine.Nonsingular (g' (f x)) (g' (f y)) := by
      rw [← hV]
      exact ((W.map f).toAffine.map_nonsingular g'.injective (f x) (f y)).mpr hf
    change pointMapHom f W (fixedCurvePointMap g W hW (Point.some x y h)) =
      fixedCurvePointMap g' (W.map f) hV (Point.some (f x) (f y) hf)
    rw [fixedCurvePointMap_some g W hW h hg, fixedCurvePointMap_some g' (W.map f) hV hf hg']
    exact some_of_eq_of_eq' (hfg x).symm (hfg y).symm

end
end Dubon2026.SourceEllipticVelu
