import Dubon2026.IntegralWeightBlockTriangular

/-! Gaussian factorization on the required generic matrix open cell.
Nonvanishing of the actual leading principal minors suffices. These minors
will be certified by evaluation at the identity for the original generic
matrix, so this hypothesis will not survive the highest-line consumer.
-/

namespace Dubon2026
noncomputable section
open Matrix

variable {K : Type*} [Field K] {n : ℕ}

/-- A lower-upper factorization extends across one final coordinate by native Schur factorization. -/
theorem integralWeightLastBlock_exists_LU (A : Matrix (Fin n) (Fin n) K)
    (B : Matrix (Fin n) (Fin 1) K) (C : Matrix (Fin 1) (Fin n) K)
    (D : Matrix (Fin 1) (Fin 1) K) [Invertible A]
    (L U : Matrix (Fin n) (Fin n) K) (hA : A = L * U)
    (hL : L.BlockTriangular OrderDual.toDual) (hU : U.BlockTriangular id) :
    ∃ L' U' : Matrix (Fin (n + 1)) (Fin (n + 1)) K,
      integralWeightLastBlock A B C D = L' * U' ∧
        L'.BlockTriangular OrderDual.toDual ∧ U'.BlockTriangular id := by
  let S := D - C * ⅟A * B
  let L₀ := integralWeightLastBlock (1 : Matrix (Fin n) (Fin n) K) 0 (C * ⅟A) 1
  let L₁ := integralWeightLastBlock L 0 0 (1 : Matrix (Fin 1) (Fin 1) K)
  let U₁ := integralWeightLastBlock U 0 0 S
  let U₀ := integralWeightLastBlock (1 : Matrix (Fin n) (Fin n) K) (⅟A * B) 0 1
  have hdiag : integralWeightLastBlock A 0 0 S = L₁ * U₁ := by
    simp only [L₁, U₁, integralWeightLastBlock_mul, Matrix.mul_zero, Matrix.zero_mul,
      zero_add, add_zero, Matrix.one_mul, hA]
  refine ⟨L₀ * L₁, U₁ * U₀, ?_, ?_, ?_⟩
  · rw [integralWeightLastBlock_schur, hdiag]
    simp only [L₀, U₀, mul_assoc]
  · exact (integralWeightLastBlock_lower 1 (C * ⅟A) 1
      Matrix.blockTriangular_one).mul (integralWeightLastBlock_lower L 0 1 hL)
  · exact (integralWeightLastBlock_upper U 0 S hU).mul
      (integralWeightLastBlock_upper 1 (⅟A * B) 1 Matrix.blockTriangular_one)

/-- Every original finite matrix whose leading principal minors are nonzero has an actual lower-upper factorization. -/
theorem integralWeight_exists_LU_of_leading (n : ℕ)
    (M : Matrix (Fin n) (Fin n) K)
    (hM : ∀ (k : ℕ) (hk : k ≤ n),
      (M.submatrix (Fin.castLE hk) (Fin.castLE hk)).det ≠ 0) :
    ∃ L U : Matrix (Fin n) (Fin n) K,
      M = L * U ∧ L.BlockTriangular OrderDual.toDual ∧ U.BlockTriangular id := by
  induction n with
  | zero =>
    refine ⟨1, 1, ?_, Matrix.blockTriangular_one, Matrix.blockTriangular_one⟩
    ext i
    exact Fin.elim0 i
  | succ n ih =>
    let A := M.submatrix Fin.castSucc Fin.castSucc
    let B : Matrix (Fin n) (Fin 1) K := fun i _ => M i.castSucc (Fin.last n)
    let C : Matrix (Fin 1) (Fin n) K := fun _ j => M (Fin.last n) j.castSucc
    let D : Matrix (Fin 1) (Fin 1) K := fun _ _ => M (Fin.last n) (Fin.last n)
    have hA : ∀ (k : ℕ) (hk : k ≤ n),
        (A.submatrix (Fin.castLE hk) (Fin.castLE hk)).det ≠ 0 := by
      intro k hk
      exact hM k (hk.trans (Nat.le_succ n))
    obtain ⟨L, U, hLU, hL, hU⟩ := ih A hA
    have hdet : A.det ≠ 0 := hM n (Nat.le_succ n)
    letI : Invertible A.det := invertibleOfNonzero hdet
    letI : Invertible A := Matrix.invertibleOfDetInvertible A
    have hblocks : M = integralWeightLastBlock A B C D := by
      ext i j
      induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
        simp [integralWeightLastBlock, Matrix.reindex_apply, Matrix.submatrix,
          A, B, C, D]
    rw [hblocks]
    exact integralWeightLastBlock_exists_LU A B C D L U hLU hL hU

end
end Dubon2026
