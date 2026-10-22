import Dubon2026.SourceOriginalRegularEvaluationFrame
import Dubon2026.SourceOriginalAbelJacobiOpenImage

/-! DUB-17/18 -> original torsion cardinality -> complex Abel-Jacobi.
Every vector modulo actual loop periods is represented by an actual
degree-zero original divisor. Original evaluation separation supplies
an independent frame. The local inverse-function theorem makes the
image subgroup open; connectedness of complex coordinate space makes
it the whole space. No evaluation frame, local surjectivity or inversion
statement is supplied as a hypothesis. The principal-divisor kernel and
period discreteness remain required for the global Pic0 comparison.
Adapted from S_AlgebraicCurve_exists_degree_eq_zero_and_abelJacobiDiv_sub_mem_pathPeriodLattice,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Set KaehlerDifferential
variable (N : ℕ) [NeZero N]

theorem original_jacobi_inversion {n : ℕ}
    (b : Module.Basis (Fin n) ℂ (regularDifferentials ℂ (modularFunctionFieldOver N ℂ)))
    (P₀ : Place ℂ (modularFunctionFieldOver N ℂ)) (u : Fin n → ℂ) :
    ∃ D : Divisor ℂ (modularFunctionFieldOver N ℂ), Divisor.degree D = 0 ∧
      abelJacobiDiv N (fun i => (b i : Ω[modularFunctionFieldOver N ℂ⁄ℂ])) P₀ D - u ∈
        pathPeriodLattice N (fun i => (b i : Ω[modularFunctionFieldOver N ℂ⁄ℂ])) := by
  classical
  let bb : Fin n → Ω[modularFunctionFieldOver N ℂ⁄ℂ] := fun i => b i
  have hb : ∀ i, bb i ∈ regularDifferentials ℂ (modularFunctionFieldOver N ℂ) := fun i => (b i).2
  let v : Place ℂ (modularFunctionFieldOver N ℂ) → (Fin n → ℂ) :=
    fun P i => readDifferential N P (b i) 0
  obtain ⟨κ, a, -, hspan, hli⟩ := exists_linearIndependent' ℂ v
  haveI : Finite κ := hli.finite
  letI : Fintype κ := Fintype.ofFinite κ
  have htop : ⊤ ≤ Submodule.span ℂ (range (v ∘ a)) := by
    rw [hspan, show Submodule.span ℂ (range v) = ⊤ from span_readDifferential_center_eq_top N b]
  let β : Module.Basis κ ℂ (Fin n → ℂ) := Module.Basis.mk hli htop
  have hβ : ∀ k, β k = fun i => readDifferential N (a k) (bb i) 0 := by
    intro k
    simp only [β, Module.Basis.mk_apply]
    rfl
  let S := abelJacobiImage N bb P₀
  have hopen : IsOpen (S : Set (Fin n → ℂ)) :=
    S.isOpen_of_mem_nhds (abelJacobiImage_mem_nhds_of_frame N bb hb P₀ a β hβ)
  have hclosed : IsClosed (S : Set (Fin n → ℂ)) := S.isClosed_of_isOpen hopen
  have hS : (S : Set (Fin n → ℂ)) = univ := IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨0, S.zero_mem⟩
  have hu : u ∈ (S : Set (Fin n → ℂ)) := by
    rw [hS]
    exact mem_univ u
  exact hu

end
end Dubon2026.SourceFunctionField.OriginalChart
