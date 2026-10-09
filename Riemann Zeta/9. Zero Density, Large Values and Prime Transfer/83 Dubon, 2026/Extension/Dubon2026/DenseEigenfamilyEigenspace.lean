import Dubon2026.OrthogonalClosureBasis
import Dubon2026.UnitaryDistinctEigenOrthogonal
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-! # Exact eigenspaces from a genuine dense family of unitary eigenvectors -/

namespace Dubon2026

noncomputable section

variable {V ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- A complete subspace containing exactly the matching vectors of a dense unitary eigenfamily is the entire actual eigenspace. -/
theorem eigenspace_eq_of_dense_eigenfamily
    (T : Module.End ℂ V) (hT : ∀ x y, inner ℂ (T x) (T y) = inner ℂ x y)
    (u : ι → V) (θ : ι → ℂ) (hθ : ∀ i, ‖θ i‖ = 1)
    (hu : ∀ i, T (u i) = θ i • u i)
    (hd : (Submodule.span ℂ (Set.range u)).topologicalClosure = ⊤)
    (c : ℂ) (S : Submodule ℂ V) [CompleteSpace S]
    (hS : S ≤ Module.End.eigenspace T c)
    (hm : ∀ i, θ i = c → u i ∈ S) : Module.End.eigenspace T c = S := by
  apply le_antisymm _ hS
  intro x hx
  have hp := hS (S.starProjection_apply_mem x)
  have hr := (Module.End.eigenspace T c).sub_mem hx hp
  have hz : x - S.starProjection x = 0 := by
    apply closureSpan_eq_zero_of_inner u
    · rw [hd]
      trivial
    · intro i
      by_cases hi : θ i = c
      · exact (Submodule.sub_starProjection_mem_orthogonal (K := S) x) (u i) (hm i hi)
      · exact unitary_distinct_eigen_inner_zero T hT (u i) _ (θ i) c (hθ i) hi
          (hu i) (Module.End.mem_eigenspace_iff.mp hr)
  exact (sub_eq_zero.mp hz).symm ▸ S.starProjection_apply_mem x

end
end Dubon2026
