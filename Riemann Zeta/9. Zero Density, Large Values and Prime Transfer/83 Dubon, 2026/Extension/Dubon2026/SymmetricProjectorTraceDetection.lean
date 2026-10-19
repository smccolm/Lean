import Dubon2026.SymmetricProjectorConjugationSpan
import Dubon2026.FullMatrixTracePairing

/-! The original extremal-projector conjugates detect every nonzero
matrix under the native trace pairing. This is the linear-algebra
obligation connecting DUB-17's nonzero kernel values to regular
commuting residual tests. -/

namespace Dubon2026
noncomputable section
open Matrix
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K]
  (q n : ℕ) [Fact q.Prime] [CharP K q]
  (hsize : 2 * n < Nat.card K - 1) (hchar : n < q)

include hsize hchar

/-- Conjugates of the actual extremal projector under the original
finite symmetric SL2 representation span the entire matrix algebra. -/
theorem finiteSymmetric_projector_conjugates_span :
    Submodule.span K (Set.range (fun g : SL(2, K) =>
      matrixAdjointRepresentation ((homogeneousSymmetricGL n).comp SpecialLinearGroup.toGL) g
        (Matrix.single (0 : Fin (n + 1)) 0 1))) = ⊤ := by
  let ψ := (homogeneousSymmetricGL (R := K) n).comp SpecialLinearGroup.toGL
  let T := matrixAdjointRepresentation ψ
  let E := Matrix.single (0 : Fin (n + 1)) (0 : Fin (n + 1)) (1 : K)
  let S := Submodule.span K (Set.range (fun g : SL(2, K) => T g E))
  have hS : ∀ g X, X ∈ S → T g X ∈ S := by
    intro g X hX
    induction hX using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨h, rfl⟩ := hy
      have he : T g (T h E) = T (g * h) E := by rw [map_mul, Module.End.mul_apply]
      rw [he]
      exact Submodule.subset_span ⟨g * h, rfl⟩
    | zero => simpa only [map_zero] using S.zero_mem
    | add x y _ _ hx hy => simpa only [map_add] using S.add_mem hx hy
    | smul a x _ hx => simpa only [map_smul] using S.smul_mem a hx
  have hE : E ∈ S := by
    have h := Submodule.subset_span (R := K)
      (show T 1 E ∈ Set.range (fun g : SL(2, K) => T g E) from ⟨1, rfl⟩)
    simpa only [map_one, Module.End.one_apply] using h
  exact finiteSymmetric_projector_invariant_eq_top q n hsize hchar S hS hE

/-- A nonzero original matrix has nonzero trace against an actual
conjugate of the extremal symmetric projector. -/
theorem finiteSymmetric_exists_projector_trace_ne_zero
    (X : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (hX : X ≠ 0) :
    ∃ g : SL(2, K), Matrix.trace (X *
      matrixAdjointRepresentation ((homogeneousSymmetricGL n).comp SpecialLinearGroup.toGL) g
        (Matrix.single (0 : Fin (n + 1)) 0 1)) ≠ 0 := by
  by_contra hn
  push Not at hn
  let ℓ := fullMatrixTracePairing X
  have hle : Submodule.span K (Set.range (fun g : SL(2, K) =>
      matrixAdjointRepresentation ((homogeneousSymmetricGL n).comp SpecialLinearGroup.toGL) g
        (Matrix.single (0 : Fin (n + 1)) 0 1))) ≤ LinearMap.ker ℓ := by
    apply Submodule.span_le.mpr
    rintro Y ⟨g, rfl⟩
    exact hn g
  rw [finiteSymmetric_projector_conjugates_span q n hsize hchar] at hle
  have hz : ℓ = 0 := LinearMap.ker_eq_top.mp (top_unique hle)
  exact hX (fullMatrixTracePairing_bijective.injective (hz.trans (map_zero _).symm))

end
end Dubon2026
