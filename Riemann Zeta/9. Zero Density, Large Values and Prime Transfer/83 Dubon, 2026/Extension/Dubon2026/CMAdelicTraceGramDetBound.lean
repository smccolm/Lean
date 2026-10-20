import Dubon2026.CMAdelicTraceDualBasis
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! # Uniform Gram determinant bounds for the original trace lattices

Coordinates of the fixed multiple of the original trace-dual basis give
an integer matrix whose product with the original integral Gram matrix
is a fixed scalar matrix. Its determinant proves divisibility by a fixed
power and hence the bound required for DUB-17's finite Gram-class theorem.
-/

namespace Dubon2026

noncomputable section

open NumberField Matrix Module LinearMap.BilinForm
open scoped ComplexOrder

variable (K : Type) [Field K] [NumberField K] [IsCMField K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- One fixed positive integer bounds the Gram determinant of every original attached integral trace lattice. -/
theorem cmAdelicTraceGramDet_uniform_bound (H : Matrix ι ι K)
    (hH : ∀ φ : K →+* ℂ, (φ.mapMatrix H).PosDef)
    (d : ℤ) (hd : 0 < d) (hIntegral : ∀ i j, IsIntegral ℤ (d • H i j)) :
    ∃ m : ℤ, 0 < m ∧ ∀ (g : cmFiniteAdelicUnitaryGroup K H)
      {κ : Type*} [Fintype κ] [DecidableEq κ]
      (b : Basis κ ℤ (numberFieldAdelicLattice K ι g.val)),
      (toMatrix b (cmAdelicLatticeIntegralTraceForm K H d hIntegral g)).det ≤
        m ^ Fintype.card κ := by
  obtain ⟨m, hm, hmem⟩ := cmAdelicTraceDual_uniform_containment K H hH d hd
  refine ⟨m, hm, ?_⟩
  intro g κ _ _ b
  let B := (d : ℚ) • cmHermitianRationalTraceForm K H
  let q := numberFieldAdelicLatticeRationalBasis K ι g.val b
  let qdual := B.dualBasis (cmHermitianScaledTraceForm_nondegenerate K H hH d hd) q
  let u (j : κ) : numberFieldAdelicLattice K ι g.val :=
    ⟨m • qdual j, cmAdelicTraceDualBasis_scaled_mem K H hH d hd m hmem g b j⟩
  let I := cmAdelicLatticeIntegralTraceForm K H d hIntegral g
  let A := toMatrix b I
  let C : Matrix κ κ ℤ := fun j i => b.repr (u j) i
  have hentry (j k : κ) : (C * A) j k = I (u j) (b k) := by
    simp only [Matrix.mul_apply, C, A, toMatrix_apply]
    conv_rhs => lhs; rw [← b.sum_repr (u j)]
    simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
  have hpair (j k : κ) : (I (u j) (b k) : ℚ) =
      (m : ℚ) * (if k = j then 1 else 0) := by
    rw [cmAdelicLatticeIntegralTraceForm_cast]
    rw [← numberFieldAdelicLatticeRationalBasis_apply K ι g.val b k]
    change B (m • qdual j) (q k) = _
    rw [map_zsmul, LinearMap.smul_apply]
    simp only [zsmul_eq_mul, qdual, LinearMap.BilinForm.apply_dualBasis_left]
  have hCA : C * A = m • (1 : Matrix κ κ ℤ) := by
    ext j k
    rw [hentry]
    apply Int.cast_injective (α := ℚ)
    simpa only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
      Int.cast_mul, Int.cast_ite, Int.cast_one, Int.cast_zero, eq_comm] using hpair j k
  have hdet : C.det * A.det = m ^ Fintype.card κ := by
    have h := congrArg Matrix.det hCA
    simpa only [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one] using h
  apply Int.le_of_dvd (pow_pos hm _)
  exact ⟨C.det, hdet.symm.trans (mul_comm _ _)⟩

end
end Dubon2026
