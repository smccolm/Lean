import Dubon2026.SourceEllipticFixedCurvePointNaturality
import Dubon2026.SourceEllipticAllLevelCyclicEquivariance

/-! The literal cyclic quotient values commute with a lifted field map.
Native subgroup composition turns the proved point-map diagram into the
kernel diagram. Existing all-level quotient equivariance then supplies the
value identity needed for the descended finite-field inertia action. -/
namespace Dubon2026.SourceEllipticVelu
open WeierstrassCurve OddDiscriminant SourceFunctionField.IntegralJCoordinate
noncomputable section
variable {F L : Type*} [Field F] [Field L] [DecidableEq F] [DecidableEq L]

theorem cyclicKernelMap_fixedCurve_naturality
    (f : F →+* L) (W : WeierstrassCurve F)
    (g : F →+* F) (hW : W.map g = W)
    (g' : L →+* L) (hV : (W.map f).map g' = W.map f)
    (hfg : ∀ x, g' (f x) = f (g x)) (N : ℕ)
    (S : {S : AddSubgroup W.toAffine.Point // IsAddCyclic S ∧ Nat.card S = N}) :
    primeCyclicKernelMap f W N (fixedCurveCyclicKernelMap g W hW N S) =
      fixedCurveCyclicKernelMap g' (W.map f) hV N (primeCyclicKernelMap f W N S) := by
  apply Subtype.ext
  change (fixedCurveCyclicKernelMap g W hW N S).val.map (pointMapHom f W) = _
  rw [fixedCurveCyclicKernelMap_coe, fixedCurveCyclicKernelMap_coe]
  change (S.val.map (fixedCurvePointMap g W hW)).map (pointMapHom f W) =
    (S.val.map (pointMapHom f W)).map (fixedCurvePointMap g' (W.map f) hV)
  rw [AddSubgroup.map_map, AddSubgroup.map_map,
    fixedCurvePointMap_naturality f W g hW g' hV hfg]

theorem cyclicQuotientJ_lift_naturality [IsAlgClosed L]
    (f : F →+* L) (W : WeierstrassCurve F) [W.IsElliptic]
    (g : F →+* F) (hW : W.map g = W)
    (g' : L →+* L) (hfg : ∀ x, g' (f x) = f (g x))
    (N : ℕ) (hNL : (N : L) ≠ 0)
    (S : {S : AddSubgroup W.toAffine.Point // IsAddCyclic S ∧ Nat.card S = N}) :
    cyclicQuotientJ (W.map f) N hNL
      (primeCyclicKernelMap f W N (fixedCurveCyclicKernelMap g W hW N S)) =
      g' (cyclicQuotientJ (W.map f) N hNL (primeCyclicKernelMap f W N S)) := by
  have hcomp : g'.comp f = f.comp g := RingHom.ext hfg
  have hV : (W.map f).map g' = W.map f := by
    rw [WeierstrassCurve.map_map, hcomp, ← WeierstrassCurve.map_map, hW]
  rw [cyclicKernelMap_fixedCurve_naturality f W g hW g' hV hfg]
  exact cyclicQuotientJ_fixedCurve g' (W.map f) hV N hNL _

end
end Dubon2026.SourceEllipticVelu
