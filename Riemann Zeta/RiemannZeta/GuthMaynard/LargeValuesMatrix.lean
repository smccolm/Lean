import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import RiemannZeta.GuthMaynard.LargeValuesDefinitions

open Complex Finset
open scoped BigOperators ComplexOrder Matrix Matrix.Norms.L2Operator

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

/-- Euclidean operator norm of the rectangular sampling matrix.  This is the
largest singular value `s₁(M_W)` in Guth--Maynard Lemmas 4.1--4.2. -/
noncomputable def gmMatrixOperatorNorm (cutoff : GMSmoothCutoff) (N : ℕ)
    (W : Finset ℝ) : ℝ :=
  ‖gmMatrix cutoff N W‖

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

/-- The Euclidean operator norm controls the complete sampled energy. -/
theorem gmMatrix_energy_le_operatorNorm (cutoff : GMSmoothCutoff) (N : ℕ)
    (W : Finset ℝ) (b : ℕ → ℂ) :
    ∑ t : GMRow W,
        ‖(gmMatrix cutoff N W).mulVec (gmCoefficientVector N b) t‖ ^ 2 ≤
      gmMatrixOperatorNorm cutoff N W ^ 2 *
        ∑ n : GMColumn N, ‖gmCoefficientVector N b n‖ ^ 2 := by
  let x : EuclideanSpace ℂ (GMColumn N) :=
    EuclideanSpace.equiv (GMColumn N) ℂ |>.symm (gmCoefficientVector N b)
  let y : EuclideanSpace ℂ (GMRow W) :=
    EuclideanSpace.equiv (GMRow W) ℂ |>.symm
      ((gmMatrix cutoff N W).mulVec (gmCoefficientVector N b))
  have h := Matrix.l2_opNorm_mulVec (gmMatrix cutoff N W) x
  have hx : ‖x‖ ^ 2 =
      ∑ n : GMColumn N, ‖gmCoefficientVector N b n‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    rfl
  have hy : ‖y‖ ^ 2 =
      ∑ t : GMRow W,
        ‖(gmMatrix cutoff N W).mulVec (gmCoefficientVector N b) t‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    rfl
  change ‖y‖ ≤ ‖gmMatrix cutoff N W‖ * ‖x‖ at h
  have hsq := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [hy, mul_pow, hx] at hsq
  simpa only [gmMatrixOperatorNorm] using hsq

/-- Source-faithful quantitative conclusion of Guth--Maynard Lemma 4.1,
stated with an arbitrary positive threshold `V`. -/
theorem gm_largeValues_card_le_operatorNorm (cutoff : GMSmoothCutoff) (N : ℕ)
    (W : Finset ℝ) (b : ℕ → ℂ) (V : ℝ) (hV : 0 < V)
    (hb : ∀ n ∈ dyadicInterval N, ‖b n‖ ≤ 1)
    (hLarge : ∀ t ∈ W, V ≤ ‖gmSmoothDirichletPoly cutoff N b t‖) :
    (W.card : ℝ) ≤
      (N : ℝ) * gmMatrixOperatorNorm cutoff N W ^ 2 / V ^ 2 := by
  have hSample := gmMatrix_sample_energy_lower cutoff N W b V hV.le hLarge
  have hOperator := gmMatrix_energy_le_operatorNorm cutoff N W b
  have hCoeff := gmCoefficient_energy_le N b hb
  have hOpNonneg : 0 ≤ gmMatrixOperatorNorm cutoff N W ^ 2 := sq_nonneg _
  have hCombined : (W.card : ℝ) * V ^ 2 ≤
      gmMatrixOperatorNorm cutoff N W ^ 2 * N := by
    calc
      (W.card : ℝ) * V ^ 2 ≤
          ∑ t : GMRow W,
            ‖(gmMatrix cutoff N W).mulVec (gmCoefficientVector N b) t‖ ^ 2 :=
        hSample
      _ ≤ gmMatrixOperatorNorm cutoff N W ^ 2 *
          ∑ n : GMColumn N, ‖gmCoefficientVector N b n‖ ^ 2 := hOperator
      _ ≤ gmMatrixOperatorNorm cutoff N W ^ 2 * N :=
        mul_le_mul_of_nonneg_left hCoeff hOpNonneg
  apply (le_div_iff₀ (sq_pos_of_pos hV)).2
  calc
    (W.card : ℝ) * V ^ 2 ≤
        gmMatrixOperatorNorm cutoff N W ^ 2 * N := hCombined
    _ = (N : ℝ) * gmMatrixOperatorNorm cutoff N W ^ 2 := by ring

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

/-- A positive Hermitian matrix is bounded in Euclidean operator norm by any
eigenvalue which dominates its spectrum. -/
theorem Matrix.IsHermitian.l2_opNorm_le_eigenvalue {ι : Type*} [Fintype ι]
    [DecidableEq ι] [Nonempty ι] {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (hnonneg : ∀ i, 0 ≤ hA.eigenvalues i) (j : ι)
    (hj : ∀ i, hA.eigenvalues i ≤ hA.eigenvalues j) :
    ‖A‖ ≤ hA.eigenvalues j := by
  let U : Matrix ι ι ℂ := hA.eigenvectorUnitary
  let D : Matrix ι ι ℂ := Matrix.diagonal (Complex.ofReal ∘ hA.eigenvalues)
  have hspec : A = U * (D * star U) := by
    simpa [U, D, Unitary.conjStarAlgAut_apply, mul_assoc] using hA.spectral_theorem
  have hunit : star U * U = 1 := by simp [U]
  have hone : ‖(1 : Matrix ι ι ℂ)‖ = 1 := by
    rw [show (1 : Matrix ι ι ℂ) = Matrix.diagonal 1 by ext i k; simp]
    rw [Matrix.l2_opNorm_diagonal]
    apply le_antisymm
    · rw [pi_norm_le_iff_of_nonneg zero_le_one]
      simp
    · have h := norm_le_pi_norm (fun _ : ι => (1 : ℂ))
          (Classical.choice inferInstance)
      rw [norm_one] at h
      exact h
  have hnormsq : ‖U‖ * ‖U‖ = 1 := by
    have h := Matrix.l2_opNorm_conjTranspose_mul_self U
    rw [show U.conjTranspose = star U by rfl, hunit, hone] at h
    exact h.symm
  have hnormU : ‖U‖ = 1 := by nlinarith [norm_nonneg U]
  have hnormStarU : ‖star U‖ = 1 := by
    rw [← show U.conjTranspose = star U by rfl]
    rw [Matrix.l2_opNorm_conjTranspose, hnormU]
  have hD : ‖D‖ ≤ hA.eigenvalues j := by
    rw [Matrix.l2_opNorm_diagonal]
    rw [pi_norm_le_iff_of_nonneg (hnonneg j)]
    intro i
    change ‖(hA.eigenvalues i : ℂ)‖ ≤ hA.eigenvalues j
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hnonneg i)]
    exact hj i
  calc
    ‖A‖ = ‖U * (D * star U)‖ := congrArg norm hspec
    _ ≤ ‖U‖ * ‖D * star U‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ ‖U‖ * (‖D‖ * ‖star U‖) :=
      mul_le_mul_of_nonneg_left (Matrix.l2_opNorm_mul _ _) (norm_nonneg U)
    _ = ‖D‖ := by rw [hnormU, hnormStarU]; ring
    _ ≤ hA.eigenvalues j := hD

/-- The matrix operator norm is bounded by one of the row-Gram singular
values.  The selected index realizes the largest Gram eigenvalue. -/
theorem exists_gmMatrixOperatorNorm_le_singularValue (cutoff : GMSmoothCutoff)
    (N : ℕ) (W : Finset ℝ) (hW : W.Nonempty) :
    ∃ j : GMRow W,
      gmMatrixOperatorNorm cutoff N W ≤ gmMatrixSingularValue cutoff N W j := by
  let H := gmMatrix_gram_isHermitian cutoff N W
  haveI : Nonempty (GMRow W) := by
    rcases hW with ⟨t, ht⟩
    exact ⟨⟨t, ht⟩⟩
  obtain ⟨j, _hjMem, hj⟩ :=
    Finset.exists_mem_eq_sup'
      (Finset.univ_nonempty : (Finset.univ : Finset (GMRow W)).Nonempty)
      H.eigenvalues
  refine ⟨j, ?_⟩
  have hjMax : ∀ i, H.eigenvalues i ≤ H.eigenvalues j := by
    intro i
    rw [← hj]
    exact Finset.le_sup' H.eigenvalues (Finset.mem_univ i)
  have hGramNorm :
      ‖gmMatrix cutoff N W * (gmMatrix cutoff N W).conjTranspose‖ ≤
        H.eigenvalues j :=
    Matrix.IsHermitian.l2_opNorm_le_eigenvalue H
      (gmMatrix_gram_eigenvalue_nonneg cutoff N W) j hjMax
  have hGramEq :
      ‖gmMatrix cutoff N W * (gmMatrix cutoff N W).conjTranspose‖ =
        ‖gmMatrix cutoff N W‖ * ‖gmMatrix cutoff N W‖ := by
    have h := Matrix.l2_opNorm_conjTranspose_mul_self
      (gmMatrix cutoff N W).conjTranspose
    simpa [Matrix.l2_opNorm_conjTranspose] using h
  have hsq : gmMatrixOperatorNorm cutoff N W ^ 2 ≤
      gmMatrixSingularValue cutoff N W j ^ 2 := by
    rw [gmMatrixOperatorNorm, pow_two, gmMatrixSingularValue_sq]
    rw [← hGramEq]
    exact hGramNorm
  exact (sq_le_sq₀ (norm_nonneg _)
    (gmMatrixSingularValue_nonneg cutoff N W j)).mp hsq

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
