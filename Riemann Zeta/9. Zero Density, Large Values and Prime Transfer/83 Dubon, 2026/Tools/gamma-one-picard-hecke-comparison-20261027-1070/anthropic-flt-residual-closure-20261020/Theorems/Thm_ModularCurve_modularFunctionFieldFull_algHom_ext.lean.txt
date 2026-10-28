import Definitions.Def_ModularCurve_X0
import P2M.Util
import P2M.Sol.S_ModularCurve_modularFunctionFieldFull_algHom_ext

open ModularCurve IntermediateField
theorem ModularCurve.modularFunctionFieldFull_algHom_ext {N : ℕ} {A : Type*} [DivisionRing A] [Algebra ℚ A] {f g : modularFunctionFieldFull N →ₐ[ℚ] A} (h : ∀ (d : ℕ) (_ : NeZero d) (hd : d ∣ N), f ⟨qExpand ℚ d jq, jqd_mem_full N hd⟩ = g ⟨qExpand ℚ d jq, jqd_mem_full N hd⟩) : f = g := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_modularFunctionFieldFull_algHom_ext.solution
