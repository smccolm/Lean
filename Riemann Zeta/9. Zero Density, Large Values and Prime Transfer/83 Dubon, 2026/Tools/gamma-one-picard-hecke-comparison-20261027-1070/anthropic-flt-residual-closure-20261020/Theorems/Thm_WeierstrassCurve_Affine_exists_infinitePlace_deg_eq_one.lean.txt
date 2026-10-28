import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_Affine_exists_infinitePlace_deg_eq_one

theorem WeierstrassCurve.Affine.exists_infinitePlace_deg_eq_one {F : Type*} [Field F] (W : WeierstrassCurve.Affine F) : ∃ vInf : AlgebraicCurve.Place F W.FunctionField, vInf.deg = 1 ∧ (¬ ∀ r : W.CoordinateRing, algebraMap W.CoordinateRing W.FunctionField r ∈ vInf.toValuationSubring) ∧ ∀ v : AlgebraicCurve.Place F W.FunctionField, (¬ ∀ r : W.CoordinateRing, algebraMap W.CoordinateRing W.FunctionField r ∈ v.toValuationSubring) → v = vInf := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_Affine_exists_infinitePlace_deg_eq_one.solution
