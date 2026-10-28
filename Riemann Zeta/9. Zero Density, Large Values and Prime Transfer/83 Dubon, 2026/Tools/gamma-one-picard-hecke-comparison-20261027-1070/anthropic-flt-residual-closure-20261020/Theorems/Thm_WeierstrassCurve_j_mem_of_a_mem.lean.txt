import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_j_mem_of_a_mem

theorem WeierstrassCurve.j_mem_of_a_mem {F : Type*} [Field F] {S : Type*} [SetLike S F] [SubfieldClass S F]
    (W : WeierstrassCurve F) [W.IsElliptic] (K : S)
    (h₁ : W.a₁ ∈ K) (h₂ : W.a₂ ∈ K) (h₃ : W.a₃ ∈ K) (h₄ : W.a₄ ∈ K) (h₆ : W.a₆ ∈ K) : W.j ∈ K := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_j_mem_of_a_mem.solution
