import Dubon2026.SymmetricProjectorTraceDetection
import Mathlib.Data.Matrix.Basis

/-! DUB-17/18 -> original auxiliary-prime detection -> regular commuting
trace tests for a proper finite subfield. Extend the already proved finite
projector span by matrix units; no new projector-orbit argument is needed. -/
namespace Dubon2026
noncomputable section
open Matrix
open scoped MatrixGroups

/-- The existing finite-field projector conjugates still span after an
arbitrary field embedding. The ambient field need not equal the subfield. -/
theorem finiteSymmetric_projector_conjugates_span_extension
    {K L : Type} [Field K] [Finite K] [Field L]
    (p n : ℕ) [Fact p.Prime] [CharP K p] (θ : K →+* L)
    (hsize : 2 * n < Nat.card K - 1) (hchar : n < p) :
    Submodule.span L (Set.range (fun g : SL(2, K) =>
      (matrixAdjointRepresentation ((homogeneousSymmetricGL n).comp SpecialLinearGroup.toGL) g
        (Matrix.single (0 : Fin (n + 1)) 0 1)).map θ)) = ⊤ := by
  letI : Algebra K L := θ.toAlgebra
  let ψ := (homogeneousSymmetricGL (R := K) n).comp SpecialLinearGroup.toGL
  let E := Matrix.single (0 : Fin (n + 1)) (0 : Fin (n + 1)) (1 : K)
  let S := Submodule.span L (Set.range (fun g : SL(2, K) =>
    (matrixAdjointRepresentation ψ g E).map θ))
  let T := (S.restrictScalars K).comap (Algebra.linearMap K L).mapMatrix
  have ht : Submodule.span K (Set.range (fun g : SL(2, K) =>
      matrixAdjointRepresentation ψ g E)) ≤ T := by
    apply Submodule.span_le.mpr
    rintro M ⟨g, rfl⟩
    exact Submodule.subset_span ⟨g, rfl⟩
  have hm (M : Matrix (Fin (n + 1)) (Fin (n + 1)) K) : M.map θ ∈ S := by
    apply ht
    rw [finiteSymmetric_projector_conjugates_span p n hsize hchar]
    exact Submodule.mem_top
  have hu (i j : Fin (n + 1)) : Matrix.single i j (1 : L) ∈ S := by
    simpa only [Matrix.map_single, map_one] using hm (Matrix.single i j 1)
  apply top_unique
  intro M _
  rw [Matrix.matrix_eq_sum_single M]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.sum_mem
  intro j _
  have hx := S.smul_mem (M i j) (hu i j)
  simpa only [Matrix.smul_single, smul_eq_mul, mul_one] using hx

/-- Projectors from the actual finite subfield detect every nonzero matrix
over the ambient coefficient field under its native trace pairing. -/
theorem finiteSymmetric_exists_projector_trace_ne_zero_extension
    {K L : Type} [Field K] [Finite K] [Field L]
    (p n : ℕ) [Fact p.Prime] [CharP K p] (θ : K →+* L)
    (hsize : 2 * n < Nat.card K - 1) (hchar : n < p)
    (X : Matrix (Fin (n + 1)) (Fin (n + 1)) L) (hX : X ≠ 0) :
    ∃ g : SL(2, K), Matrix.trace (X *
      (matrixAdjointRepresentation ((homogeneousSymmetricGL n).comp SpecialLinearGroup.toGL) g
        (Matrix.single (0 : Fin (n + 1)) 0 1)).map θ) ≠ 0 := by
  by_contra hn
  push Not at hn
  let ℓ := fullMatrixTracePairing X
  have hle : Submodule.span L (Set.range (fun g : SL(2, K) =>
      (matrixAdjointRepresentation ((homogeneousSymmetricGL n).comp SpecialLinearGroup.toGL) g
        (Matrix.single (0 : Fin (n + 1)) 0 1)).map θ)) ≤ LinearMap.ker ℓ := by
    apply Submodule.span_le.mpr
    rintro Y ⟨g, rfl⟩
    exact hn g
  rw [finiteSymmetric_projector_conjugates_span_extension p n θ hsize hchar] at hle
  have hz : ℓ = 0 := LinearMap.ker_eq_top.mp (top_unique hle)
  exact hX (fullMatrixTracePairing_bijective.injective (hz.trans (map_zero _).symm))

end
end Dubon2026
