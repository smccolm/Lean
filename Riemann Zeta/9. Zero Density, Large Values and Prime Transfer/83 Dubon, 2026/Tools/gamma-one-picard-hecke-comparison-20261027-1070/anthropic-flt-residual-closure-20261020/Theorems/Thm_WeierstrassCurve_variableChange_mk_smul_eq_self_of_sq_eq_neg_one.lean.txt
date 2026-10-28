import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_variableChange_mk_smul_eq_self_of_sq_eq_neg_one

theorem WeierstrassCurve.variableChange_mk_smul_eq_self_of_sq_eq_neg_one
    {R : Type*} [CommRing R] (u : Rˣ) (hu : (u : R) ^ 2 = -1) (A : R) :
    (⟨u, 0, 0, 0⟩ : WeierstrassCurve.VariableChange R) • (⟨0, 0, 0, A, 0⟩ : WeierstrassCurve R) =
      ⟨0, 0, 0, A, 0⟩ := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_variableChange_mk_smul_eq_self_of_sq_eq_neg_one.solution
