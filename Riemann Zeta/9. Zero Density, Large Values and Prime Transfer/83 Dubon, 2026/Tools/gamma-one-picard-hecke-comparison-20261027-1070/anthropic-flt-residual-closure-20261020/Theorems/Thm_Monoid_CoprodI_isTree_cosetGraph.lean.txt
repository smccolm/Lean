import Mathlib
import P2M.Util
import P2M.Sol.S_Monoid_CoprodI_isTree_cosetGraph

set_option autoImplicit false
theorem Monoid.CoprodI.isTree_cosetGraph {G : Fin 2 → Type*} [∀ i, Group (G i)] :
    (SimpleGraph.fromRel fun v w : (i : Fin 2) × (Monoid.CoprodI G ⧸ (Monoid.CoprodI.of (M := G) (i := i)).range) =>
        v.1 ≠ w.1 ∧ ∃ g : Monoid.CoprodI G,
          v.2 = (QuotientGroup.mk g : Monoid.CoprodI G ⧸ (Monoid.CoprodI.of (M := G) (i := v.1)).range) ∧
          w.2 = (QuotientGroup.mk g : Monoid.CoprodI G ⧸ (Monoid.CoprodI.of (M := G) (i := w.1)).range)).IsTree := by p2m_exact_reverting @_root_.P2MW.S_Monoid_CoprodI_isTree_cosetGraph.solution
