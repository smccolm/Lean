import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import RiemannZeta.GuthMaynard.LargeValuesDefinitions

open Complex Finset
open scoped BigOperators ComplexOrder Matrix

namespace RiemannZeta.GuthMaynard

/-!
# The Guth--Maynard sampling matrix

This file packages the finite matrix from Section 4 and proves its elementary
action and Gram identities.  The analytic trace estimates are downstream.
-/

/-- The finite smoothed sampling matrix with rows indexed by `W` and columns
indexed by `(N,2N]`. -/
noncomputable def gmMatrix (cutoff : GMSmoothCutoff) (N : ℕ) (W : Finset ℝ) :
    Matrix (GMRow W) (GMColumn N) ℂ := fun t n => gmMatrixEntry cutoff N t n

/-- Restriction of an ambient coefficient sequence to the matrix columns. -/
def gmCoefficientVector (N : ℕ) (b : ℕ → ℂ) : GMColumn N → ℂ := fun n => b n

theorem gmMatrix_mulVec_apply (cutoff : GMSmoothCutoff) (N : ℕ)
    (W : Finset ℝ) (b : ℕ → ℂ) (t : GMRow W) :
    (gmMatrix cutoff N W).mulVec (gmCoefficientVector N b) t =
      gmSmoothDirichletPoly cutoff N b t := by
  classical
  change (∑ n : GMColumn N, gmMatrixEntry cutoff N t n * b n) = _
  rw [gmSmoothDirichletPoly]
  conv_rhs => rw [← Finset.sum_attach]
  rw [Finset.univ_eq_attach (dyadicInterval N)]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [gmMatrixEntry]
  ring

/-- Squared sample energy forced by a pointwise large-value condition. -/
theorem gmMatrix_sample_energy_lower (cutoff : GMSmoothCutoff) (N : ℕ)
    (W : Finset ℝ) (b : ℕ → ℂ) (V : ℝ) (hV : 0 ≤ V)
    (hLarge : ∀ t ∈ W, V ≤ ‖gmSmoothDirichletPoly cutoff N b t‖) :
    (W.card : ℝ) * V ^ 2 ≤
      ∑ t : GMRow W, ‖(gmMatrix cutoff N W).mulVec (gmCoefficientVector N b) t‖ ^ 2 := by
  calc
    (W.card : ℝ) * V ^ 2 = ∑ _t : GMRow W, V ^ 2 := by simp
    _ ≤ ∑ t : GMRow W,
        ‖(gmMatrix cutoff N W).mulVec (gmCoefficientVector N b) t‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro t ht
      rw [gmMatrix_mulVec_apply]
      have htLarge := hLarge t t.property
      have htNorm : 0 ≤ ‖gmSmoothDirichletPoly cutoff N b t‖ := norm_nonneg _
      nlinarith

/-- A pointwise coefficient bound gives the source `O(N)` coefficient energy. -/
theorem gmCoefficient_energy_le (N : ℕ) (b : ℕ → ℂ)
    (hb : ∀ n ∈ dyadicInterval N, ‖b n‖ ≤ 1) :
    ∑ n : GMColumn N, ‖gmCoefficientVector N b n‖ ^ 2 ≤ N := by
  calc
    ∑ n : GMColumn N, ‖gmCoefficientVector N b n‖ ^ 2
        ≤ ∑ _n : GMColumn N, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      have hbn := hb n n.property
      have hnorm := norm_nonneg (b n)
      simp only [gmCoefficientVector]
      nlinarith
    _ = N := by simp [GMColumn, dyadicInterval]; omega

/-- Entrywise expansion of the row Gram matrix `M M*`. -/
theorem gmMatrix_mul_conjTranspose_apply (cutoff : GMSmoothCutoff) (N : ℕ)
    (W : Finset ℝ) (t u : GMRow W) :
    (gmMatrix cutoff N W * (gmMatrix cutoff N W).conjTranspose) t u =
      ∑ n : GMColumn N,
        gmMatrixEntry cutoff N t n * star (gmMatrixEntry cutoff N u n) := by
  simp [gmMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- Source equation for the row Gram kernel: its entry depends only on the
ordinate difference and uses the squared cutoff. -/
theorem gmMatrix_gram_apply_eq_phase_sum (cutoff : GMSmoothCutoff) (N : ℕ)
    (W : Finset ℝ) (t u : GMRow W) :
    (gmMatrix cutoff N W * (gmMatrix cutoff N W).conjTranspose) t u =
      ∑ n : GMColumn N,
        (cutoff ((n : ℝ) / N) ^ 2 : ℂ) *
          (n : ℂ) ^ ((((t : ℝ) - (u : ℝ)) : ℂ) * I) := by
  rw [gmMatrix_mul_conjTranspose_apply]
  apply Finset.sum_congr rfl
  intro n hn
  have hnPos : 0 < (n : ℕ) := by
    have hnMem : (n : ℕ) ∈ Finset.Ioc N (2 * N) := n.property
    rw [Finset.mem_Ioc] at hnMem
    omega
  have hnNe : (n : ℂ) ≠ 0 := by exact_mod_cast hnPos.ne'
  have hnArg : ((n : ℂ)).arg ≠ Real.pi := by
    change ((((n : ℝ) : ℂ)).arg ≠ Real.pi)
    rw [Complex.arg_ofReal_of_nonneg (by positivity : (0 : ℝ) ≤ n)]
    exact Real.pi_ne_zero.symm
  have hConj := Complex.cpow_conj (n : ℂ) (((u : ℝ) : ℂ) * I) hnArg
  have hstar : star ((n : ℂ) ^ (((u : ℝ) : ℂ) * I)) =
      (n : ℂ) ^ (-(((u : ℝ) : ℂ) * I)) := by
    simp only [map_mul, Complex.conj_natCast, Complex.conj_ofReal,
      Complex.conj_I] at hConj
    convert hConj.symm using 1
    ring_nf
  simp only [gmMatrixEntry, star_mul]
  rw [hstar]
  have hcut : star (((cutoff ((n : ℝ) / N)) : ℝ) : ℂ) =
      (((cutoff ((n : ℝ) / N)) : ℝ) : ℂ) := by simp
  rw [hcut]
  calc
    (((cutoff ((n : ℝ) / N)) : ℝ) : ℂ) *
          (n : ℂ) ^ (((t : ℝ) : ℂ) * I) *
          ((n : ℂ) ^ (-(((u : ℝ) : ℂ) * I)) *
            (((cutoff ((n : ℝ) / N)) : ℝ) : ℂ)) =
        ((((cutoff ((n : ℝ) / N)) : ℝ) : ℂ) ^ 2) *
          ((n : ℂ) ^ (((t : ℝ) : ℂ) * I) *
            (n : ℂ) ^ (-(((u : ℝ) : ℂ) * I))) := by ring
    _ = ((((cutoff ((n : ℝ) / N)) : ℝ) : ℂ) ^ 2) *
          (n : ℂ) ^
            ((((t : ℝ) : ℂ) * I) + (-(((u : ℝ) : ℂ) * I))) := by
      rw [Complex.cpow_add _ _ hnNe]
    _ = _ := by
      ring_nf

/-- The row Gram matrix is Hermitian. -/
theorem gmMatrix_gram_isHermitian (cutoff : GMSmoothCutoff) (N : ℕ)
    (W : Finset ℝ) :
    (gmMatrix cutoff N W * (gmMatrix cutoff N W).conjTranspose).IsHermitian := by
  exact Matrix.isHermitian_mul_conjTranspose_self _

/-- The row Gram matrix is positive semidefinite. -/
theorem gmMatrix_gram_posSemidef (cutoff : GMSmoothCutoff) (N : ℕ)
    (W : Finset ℝ) :
    (gmMatrix cutoff N W * (gmMatrix cutoff N W).conjTranspose).PosSemidef := by
  exact Matrix.posSemidef_self_mul_conjTranspose _

/-- Every eigenvalue of the row Gram matrix is nonnegative. -/
theorem gmMatrix_gram_eigenvalue_nonneg (cutoff : GMSmoothCutoff) (N : ℕ)
    (W : Finset ℝ) (i : GMRow W) :
    0 ≤ (gmMatrix_gram_isHermitian cutoff N W).eigenvalues i := by
  exact (gmMatrix_gram_posSemidef cutoff N W).eigenvalues_nonneg i

/-- Singular values of the sampling matrix, defined through the nonnegative
eigenvalues of its row Gram matrix. -/
noncomputable def gmMatrixSingularValue (cutoff : GMSmoothCutoff) (N : ℕ)
    (W : Finset ℝ) (i : GMRow W) : ℝ :=
  Real.sqrt ((gmMatrix_gram_isHermitian cutoff N W).eigenvalues i)

theorem gmMatrixSingularValue_nonneg (cutoff : GMSmoothCutoff) (N : ℕ)
    (W : Finset ℝ) (i : GMRow W) :
    0 ≤ gmMatrixSingularValue cutoff N W i := by
  exact Real.sqrt_nonneg _

theorem gmMatrixSingularValue_sq (cutoff : GMSmoothCutoff) (N : ℕ)
    (W : Finset ℝ) (i : GMRow W) :
    gmMatrixSingularValue cutoff N W i ^ 2 =
      (gmMatrix_gram_isHermitian cutoff N W).eigenvalues i := by
  exact Real.sq_sqrt (gmMatrix_gram_eigenvalue_nonneg cutoff N W i)

theorem gmMatrixSingularValue_sixth (cutoff : GMSmoothCutoff) (N : ℕ)
    (W : Finset ℝ) (i : GMRow W) :
    gmMatrixSingularValue cutoff N W i ^ 6 =
      (gmMatrix_gram_isHermitian cutoff N W).eigenvalues i ^ 3 := by
  rw [show gmMatrixSingularValue cutoff N W i ^ 6 =
      (gmMatrixSingularValue cutoff N W i ^ 2) ^ 3 by ring]
  rw [gmMatrixSingularValue_sq]

/-- First trace expansion for the row Gram matrix. -/
theorem gmMatrix_gram_trace_expand (cutoff : GMSmoothCutoff) (N : ℕ)
    (W : Finset ℝ) :
    Matrix.trace (gmMatrix cutoff N W * (gmMatrix cutoff N W).conjTranspose) =
      ∑ t : GMRow W, ∑ n : GMColumn N,
        gmMatrixEntry cutoff N t n * star (gmMatrixEntry cutoff N t n) := by
  simp [Matrix.trace, Matrix.mul_apply, gmMatrix, Matrix.conjTranspose_apply]

/-- Pure finite expansion of the cubic Gram trace. -/
theorem matrix_trace_cube_expand {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℂ) :
    Matrix.trace (G ^ 3) =
      ∑ t : ι, ∑ u : ι, ∑ v : ι, G t u * G u v * G v t := by
  have hcube : G ^ 3 = G * G * G := by noncomm_ring
  rw [hcube]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.sum_comm]

/-- Spectral expansion of the cubic trace of a Hermitian matrix.  This is the
finite-dimensional spectral bridge used in the sixth-moment singular-value
argument of Guth--Maynard Lemma 4.2. -/
theorem Matrix.IsHermitian.trace_cube_eq_sum_eigenvalues_cube
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    Matrix.trace (A ^ 3) = ∑ i, ((hA.eigenvalues i : ℂ) ^ 3) := by
  let U : Matrix ι ι ℂ := hA.eigenvectorUnitary
  let D : Matrix ι ι ℂ :=
    Matrix.diagonal (Complex.ofReal ∘ hA.eigenvalues)
  have hspec : A = U * (D * star U) := by
    simpa [Unitary.conjStarAlgAut_apply, mul_assoc] using hA.spectral_theorem
  have hunit : star U * U = 1 := by
    simp [U]
  have hpow : (U * (D * star U)) ^ 3 = U * (D ^ 3 * star U) := by
    rw [pow_succ, pow_succ]
    simp only [pow_one, mul_assoc]
    rw [← mul_assoc (star U) U, hunit, one_mul]
    rw [← mul_assoc (star U) U, hunit, one_mul]
    simp [pow_succ, mul_assoc]
  have hpowA : A ^ 3 = U * (D ^ 3 * star U) := by
    calc
      A ^ 3 = (U * (D * star U)) ^ 3 := congrArg (· ^ 3) hspec
      _ = U * (D ^ 3 * star U) := hpow
  rw [hpowA, Matrix.trace_mul_cycle']
  rw [← mul_assoc, hunit, one_mul]
  simp [D, pow_succ, Function.comp_def]

end RiemannZeta.GuthMaynard
