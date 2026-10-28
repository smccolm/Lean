import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_variableChange_mk_smul_eq_self_of_pow_three_eq_one

theorem WeierstrassCurve.variableChange_mk_smul_eq_self_of_pow_three_eq_one
    {R : Type*} [CommRing R] (u : Rˣ) (hu : (u : R) ^ 3 = 1) (B : R) :
    (⟨u, 0, 0, 0⟩ : WeierstrassCurve.VariableChange R) • (⟨0, 0, 0, 0, B⟩ : WeierstrassCurve R) =
      ⟨0, 0, 0, 0, B⟩ := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_variableChange_mk_smul_eq_self_of_pow_three_eq_one.solution
