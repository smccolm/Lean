import Dubon2026.MatrixTraceGram
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-! # Descent of actual matrix-basis coordinates through the genuine trace Gram matrix -/

namespace Dubon2026
noncomputable section
open Matrix Module

variable {ι κ O R : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [CommRing O] [CommRing R] [Algebra O R]

/-- If the actual trace pairings with a full original matrix basis lie in a unit-reflecting coefficient subalgebra, the genuine basis coordinates lie in that same subalgebra. -/
theorem matrixBasisCoordinates_mem_of_trace
    (S : Subalgebra O R) [IsLocalHom S.val.toRingHom]
    (b : Basis κ R (Matrix ι ι R))
    (hb : ∀ i j, Matrix.trace (b i * b j) ∈ S)
    (X : Matrix ι ι R) (hX : ∀ j, Matrix.trace (X * b j) ∈ S) (i : κ) :
    b.repr X i ∈ S := by
  let T : Matrix κ κ S := fun j k => ⟨Matrix.trace (b j * b k), hb j k⟩
  have hmap : (RingHom.mapMatrix S.val.toRingHom) T = matrixTraceGram b := by
    ext j k
    rfl
  have hdet : IsUnit T.det := by
    apply isUnit_of_map_unit S.val.toRingHom
    rw [RingHom.map_det, hmap]
    exact matrixTraceGram_det_isUnit b
  let V : Matrix κ κ R := (RingHom.mapMatrix S.val.toRingHom) T⁻¹
  have hV : matrixTraceGram b * V = 1 := by
    rw [← hmap]
    change (RingHom.mapMatrix S.val.toRingHom) T *
      (RingHom.mapMatrix S.val.toRingHom) T⁻¹ = 1
    rw [← map_mul, Matrix.mul_nonsing_inv T hdet, map_one]
  let c : κ → R := fun j => b.repr X j
  let p : κ → R := fun j => Matrix.trace (X * b j)
  have hcp : c ᵥ* matrixTraceGram b = p := by
    ext j
    have hs := congrArg (fun Z : Matrix ι ι R => Matrix.trace (Z * b j)) (b.sum_repr X)
    simp only [Matrix.sum_mul, Matrix.trace_sum, Matrix.smul_mul, Matrix.trace_smul,
      smul_eq_mul] at hs
    exact hs
  have hpV : p ᵥ* V = c := by
    rw [← hcp, Matrix.vecMul_vecMul, hV, Matrix.vecMul_one]
  rw [← show (p ᵥ* V) i = b.repr X i from congrFun hpV i]
  change (∑ j, Matrix.trace (X * b j) * (↑(T⁻¹ j i) : R)) ∈ S
  exact S.sum_mem fun j _ => S.mul_mem (hX j) (T⁻¹ j i).property

/-- The original matrix itself belongs to the span over the actual coefficient subalgebra of the same original matrix basis, once its genuine trace pairings have descended. -/
theorem matrix_mem_subalgebra_span_of_trace
    (S : Subalgebra O R) [IsLocalHom S.val.toRingHom]
    (b : Basis κ R (Matrix ι ι R))
    (hb : ∀ i j, Matrix.trace (b i * b j) ∈ S)
    (X : Matrix ι ι R) (hX : ∀ j, Matrix.trace (X * b j) ∈ S) :
    X ∈ Submodule.span S (Set.range b) := by
  have hx : X = ∑ i, (⟨b.repr X i, matrixBasisCoordinates_mem_of_trace S b hb X hX i⟩ : S) • b i := by
    exact (b.sum_repr X).symm
  rw [hx]
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end
end Dubon2026
