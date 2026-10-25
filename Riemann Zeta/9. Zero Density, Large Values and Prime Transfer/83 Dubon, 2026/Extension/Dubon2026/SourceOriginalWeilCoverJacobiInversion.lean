import Dubon2026.SourceOriginalWeilCoverRegularEvaluationFrame
import Dubon2026.SourceOriginalWeilCoverAbelJacobiOpenImage

/-! DUB-17/18 -> auxiliary point division -> cover Jacobi inversion.
Adapt the native original-curve evaluation and inverse-function arguments
to the literal Kummer cover, using actual residue readings and Abel vectors.
Finite coordinate support replaces any numerical genus assumption.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_AlgebraicCurve_exists_degree_eq_zero_and_abelJacobiDiv_sub_mem_pathPeriodLattice.
-/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Set KaehlerDifferential
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
variable (r : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C r : Polynomial FF)
variable (A : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hr : r ≠ 0)
variable (hrA : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord r = (n : ℤ) * A v)
include A hr hrA

theorem cover_jacobi_inversion {kDim : ℕ}
    (b : Module.Basis (Fin kDim) ℂ (regularDifferentials ℂ (EE)))
    (P₀ : Place ℂ (EE)) (u : Fin kDim → ℂ) :
    ∃ D : Divisor ℂ (EE), Divisor.degree D = 0 ∧
      abelJacobiDiv N n r A hr hrA (fun i : Fin kDim => (b i : Ω[EE⁄ℂ])) P₀ D - u ∈
        pathPeriodLattice N n r A hr hrA (fun i : Fin kDim => (b i : Ω[EE⁄ℂ])) := by
  classical
  let bb : Fin kDim → Ω[EE⁄ℂ] := fun i => b i
  have hb : ∀ i, bb i ∈ regularDifferentials ℂ (EE) := fun i => (b i).2
  have hframe := exists_cover_evaluation_frame (N := N) (n := n) (r := r) (A := A)
    (hr := hr) (hrA := hrA) (kDim := kDim) b
  obtain ⟨κ, hκ, a, β, hβ⟩ := hframe
  letI : Fintype κ := hκ
  let S := abelJacobiImage N n r A hr hrA bb P₀
  have hopen : IsOpen (S : Set (Fin kDim → ℂ)) :=
    S.isOpen_of_mem_nhds (abelJacobiImage_mem_nhds_of_frame N n r A hr hrA bb hb P₀ a β hβ)
  have hclosed : IsClosed (S : Set (Fin kDim → ℂ)) := S.isClosed_of_isOpen hopen
  have hS : (S : Set (Fin kDim → ℂ)) = univ := IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨0, S.zero_mem⟩
  have hu : u ∈ (S : Set (Fin kDim → ℂ)) := by
    rw [hS]
    exact mem_univ u
  exact hu

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
