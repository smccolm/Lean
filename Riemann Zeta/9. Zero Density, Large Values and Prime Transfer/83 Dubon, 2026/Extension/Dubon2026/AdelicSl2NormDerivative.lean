import Dubon2026.AdelicComplexSl2Action
import Dubon2026.RealSl2NormDerivative

/-! # Exact original norm derivatives for every differentiable special-linear tangent -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

/-- The genuine matrix Lie action is the original Hilbert norm derivative for every actual special-linear curve with the prescribed tangent. -/
theorem adelicComplexSl2Action_hasDerivAt {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (v : adelicRealSmoothSubmodule f)
    (c : ℝ → SL(2, ℝ)) (hc : c 0 = 1) (a b d : ℝ)
    (ha : HasDerivAt (fun t => c t 0 0) a 0)
    (hb : HasDerivAt (fun t => c t 1 0) b 0)
    (hd : HasDerivAt (fun t => c t 0 1) d 0) :
    HasDerivAt (fun t => adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding (c t)) v.val)
      (adelicComplexSl2Action f (complexSl2OfRealTangent a b d) v).val 0 := by
  letI : IsScalarTower ℝ ℂ (AdelicCyclicHilbert f) := inferInstance
  have hD := @realSmoothInfinitesimal_hasDerivAt_tangent (AdelicCyclicHilbert f)
    inferInstance inferInstance inferInstance inferInstance
    ((adelicCyclicHilbertRepresentation f).comp adelicRealSL2Embedding)
    (fun g => (adelicCyclicHilbertOperator f (adelicRealSL2Embedding g)).restrictScalars ℝ)
    (fun _ _ => rfl) v c hc a b d ha hb hd
  have he := complexSl2LinearMap_real_tangent
    (adelicSmoothInfinitesimal f realGeodesicCurve realGeodesicCurve_entries_contDiff)
    (adelicSmoothInfinitesimal f realUpperUnipotent realUpperUnipotent_entries_contDiff)
    (adelicSmoothInfinitesimal f realLowerUnipotent realLowerUnipotent_entries_contDiff) a b d
  have hv := congrArg (fun T : Module.End ℂ (adelicRealSmoothSubmodule f) => (T v).val) he
  change (adelicComplexSl2Action f (complexSl2OfRealTangent a b d) v).val = _ at hv
  rw [hv]
  exact hD

end
end Dubon2026
