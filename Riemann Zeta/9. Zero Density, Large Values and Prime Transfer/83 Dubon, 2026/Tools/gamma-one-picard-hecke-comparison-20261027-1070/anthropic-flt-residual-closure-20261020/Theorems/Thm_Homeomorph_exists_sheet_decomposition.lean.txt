import Mathlib
import P2M.Util
import P2M.Sol.S_Homeomorph_exists_sheet_decomposition

theorem Homeomorph.exists_sheet_decomposition {E X I : Type*} [TopologicalSpace E]
    [TopologicalSpace X] [TopologicalSpace I] [DiscreteTopology I] {f : E → X} {U : Set X}
    {Ω : Set E} (hpre : IsOpen Ω) (H : Ω ≃ₜ U × I) (hH : ∀ x, ((H x).1 : X) = f x)
    {V : Set X} (hV : IsOpen V) (hVU : V ⊆ U) [Nonempty Ω] :
    ∃ ζ : I → OpenPartialHomeomorph E X,
      (∀ i, (ζ i).target = V) ∧
      (∀ i, ∀ e ∈ (ζ i).source, e ∈ Ω ∧ ζ i e = f e) ∧
      (∀ i, ∀ z ∈ V, (ζ i).symm z ∈ Ω ∧ f ((ζ i).symm z) = z) ∧
      (Pairwise fun i j => Disjoint (ζ i).source (ζ j).source) ∧
      (∀ e : E, e ∈ Ω → f e ∈ V → ∃ i, e ∈ (ζ i).source) := by p2m_exact_reverting @_root_.P2MW.S_Homeomorph_exists_sheet_decomposition.solution
