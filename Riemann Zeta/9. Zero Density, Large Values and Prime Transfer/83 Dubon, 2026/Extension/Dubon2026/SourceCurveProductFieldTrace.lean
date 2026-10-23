import Mathlib.RingTheory.Trace.Basic

/-! Field trace under a finite product decomposition of a scalar extension.
The product matrix calculation is adapted from the selected Apache-2.0 FLT
archive's trace-decomposition proof. Native trace base change handles the
tensor step. These are the exact algebraic inputs for the DUB-17/18 sum of
local completion traces. -/

noncomputable section

namespace Dubon2026.SourceCurve

open scoped TensorProduct

/-- The trace on a finite product is the sum of the actual component traces. -/
theorem algebraTrace_pi (R : Type*) [CommRing R] {ι : Type*} [Fintype ι]
    (S : ι → Type*) [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)]
    [∀ i, Module.Free R (S i)] [∀ i, Module.Finite R (S i)] (x : ∀ i, S i) :
    Algebra.trace R (∀ i, S i) x = ∑ i, Algebra.trace R (S i) (x i) := by
  classical
  let b : ∀ i, Module.Basis (Module.Free.ChooseBasisIndex R (S i)) R (S i) :=
    fun i => Module.Free.chooseBasis R (S i)
  have key : Algebra.leftMulMatrix (Pi.basis b) x =
      Matrix.blockDiagonal' (fun i => Algebra.leftMulMatrix (b i) (x i)) := by
    refine Matrix.ext fun ji ji' => ?_
    obtain ⟨i, j⟩ := ji
    obtain ⟨i', j'⟩ := ji'
    rcases eq_or_ne i i' with rfl | hne
    · rw [Matrix.blockDiagonal'_apply_eq, Algebra.leftMulMatrix_eq_repr_mul,
        Algebra.leftMulMatrix_eq_repr_mul, Pi.basis_apply, Pi.basis_repr]
      have hx : (x * Pi.single i (b i j')) i = x i * b i j' := by simp
      rw [hx]
    · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hne,
        Algebra.leftMulMatrix_eq_repr_mul, Pi.basis_apply, Pi.basis_repr]
      have hx : (x * Pi.single i' (b i' j')) i = 0 := by
        simp [Pi.single_eq_of_ne hne]
      rw [hx]
      simp
  rw [Algebra.trace_eq_matrix_trace (Pi.basis b), key, Matrix.trace_blockDiagonal']
  exact Finset.sum_congr rfl fun i _ =>
    (Algebra.trace_eq_matrix_trace (b i) (x i)).symm

/-- Native trace base change for the literal scalar-extension algebra. -/
theorem algebraTrace_baseChange (R A B : Type*) [CommRing R] [CommRing A]
    [CommRing B] [Algebra R A] [Algebra R B] [Module.Free R B]
    [Module.Finite R B] (b : B) :
    Algebra.trace A (A ⊗[R] B) ((1 : A) ⊗ₜ[R] b) =
      algebraMap R A (Algebra.trace R B b) := by
  have h := LinearMap.trace_baseChange (Algebra.lmul R B b) A
  rw [Algebra.baseChange_lmul] at h
  exact h

/-- An actual product isomorphism decomposes the original field trace. -/
theorem algebraTrace_product_decomposition (R A B : Type*)
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    [Module.Free R B] [Module.Finite R B] {ι : Type*} [Fintype ι]
    (S : ι → Type*) [∀ i, CommRing (S i)] [∀ i, Algebra A (S i)]
    [∀ i, Module.Free A (S i)] [∀ i, Module.Finite A (S i)]
    (e : (A ⊗[R] B) ≃ₐ[A] ∀ i, S i) (b : B) :
    algebraMap R A (Algebra.trace R B b) =
      ∑ i, Algebra.trace A (S i) (e ((1 : A) ⊗ₜ[R] b) i) := by
  rw [← algebraTrace_baseChange R A B b,
    ← Algebra.trace_eq_of_algEquiv e ((1 : A) ⊗ₜ[R] b), algebraTrace_pi A S]

end Dubon2026.SourceCurve
