import Dubon2026.SourceEllipticCyclicRootEquivariance

/-! Identify the coefficient-fixed cyclic kernel map with the actual native
field action on points. This connects the proved algebraically closed
cyclic-root equivariance to the finite-field inertia action required by
the DUB-17/18 place-fiber theorem. -/
namespace Dubon2026.SourceEllipticVelu
open WeierstrassCurve WeierstrassCurve.Affine OddDiscriminant
open SourceFunctionField.IntegralJCoordinate
noncomputable section
variable {L : Type*} [Field L] [DecidableEq L]

/-- The literal field point map followed by the coefficient-fixed curve identification. -/
def fixedCurvePointMap (f : L →+* L) (W : WeierstrassCurve L)
    (hW : W.map f = W) : W.toAffine.Point →+ W.toAffine.Point :=
  (AddEquiv.cast (M := fun V : WeierstrassCurve L => V.toAffine.Point) hW).toAddMonoidHom.comp
    (pointMapHom f W)

theorem fixedCurveCyclicKernelMap_coe (f : L →+* L) (W : WeierstrassCurve L)
    (hW : W.map f = W) (N : ℕ)
    (S : {S : AddSubgroup W.toAffine.Point // IsAddCyclic S ∧ Nat.card S = N}) :
    (fixedCurveCyclicKernelMap f W hW N S).val = S.val.map (fixedCurvePointMap f W hW) := by
  have h : ∀ (V : WeierstrassCurve L) (hV : W.map f = V),
      (hV ▸ primeCyclicKernelMap f W N S).val =
        S.val.map ((AddEquiv.cast (M := fun U : WeierstrassCurve L => U.toAffine.Point)
          hV).toAddMonoidHom.comp (pointMapHom f W)) := by
    rintro V rfl
    rfl
  exact h W hW

private theorem cast_zero {V W : WeierstrassCurve L} (h : V = W) :
    AddEquiv.cast (M := fun U : WeierstrassCurve L => U.toAffine.Point) h 0 = 0 := by
  subst W
  rfl

private theorem cast_some {V W : WeierstrassCurve L} (h : V = W) {x y : L}
    (hV : V.toAffine.Nonsingular x y) (hW : W.toAffine.Nonsingular x y) :
    AddEquiv.cast (M := fun U : WeierstrassCurve L => U.toAffine.Point) h
      (Point.some x y hV) = Point.some x y hW := by
  subst W
  rfl

theorem fixedCurvePointMap_galois {F : Type*} [Field F] [Algebra F L]
    (W : WeierstrassCurve F) (σ : L ≃ₐ[F] L) :
    fixedCurvePointMap σ.toRingHom (W.baseChange L) (W.map_baseChange σ.toAlgHom) =
      Point.map (W' := W) σ.toAlgHom := by
  ext P
  cases P with
  | zero => exact cast_zero (W.map_baseChange σ.toAlgHom)
  | some x y h => exact cast_some (W.map_baseChange σ.toAlgHom) _ _

end
end Dubon2026.SourceEllipticVelu
