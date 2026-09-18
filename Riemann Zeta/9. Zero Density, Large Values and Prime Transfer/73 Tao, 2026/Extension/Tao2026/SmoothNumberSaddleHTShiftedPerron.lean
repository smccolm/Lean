import Tao2026.SmoothNumberSaddleHTSaddleComparisonSharp
import Tao2026.SmoothNumberSaddlePerronCutoff

/-!
# Source coordinates for the HT shifted-Perron estimate

This module identifies the finite Mangoldt transform and its main term with
the source expressions at `s = 1 - beta + i*t`.  It packages the remaining
analytic assertion in those coordinates, proves it equivalent to the exact
HT Lemma 6 contract, and records the finite Abel identity against
Chebyshev's psi function.  The contour/zero-free-region estimate itself
remains the analytic boundary.
-/

open Filter Topology MeasureTheory Set Complex Finset
open scoped ArithmeticFunction.vonMangoldt BigOperators Interval

namespace Tao2026

noncomputable section

noncomputable def smoothSaddleHTDirichletWeight
    (n : ℕ) (beta t : ℝ) : ℂ :=
  (((n : ℝ) ^ (beta - 1) : ℝ) : ℂ) *
    Complex.exp (-((t * Real.log n : ℝ) : ℂ) * Complex.I)

noncomputable def smoothSaddleHTSourceExponent (beta t : ℝ) : ℂ :=
  ((1 - beta : ℝ) : ℂ) + (t : ℂ) * Complex.I

noncomputable def smoothSaddleHTSourceDirichletSum (y : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 y, (((Λ n : ℝ)) : ℂ) / (n : ℂ) ^ s

noncomputable def smoothSaddleHTSourceMainTerm (y : ℕ) (s : ℂ) : ℂ :=
  (y : ℂ) ^ (1 - s) / (1 - s)

theorem smoothSaddleHTDirichletWeight_eq_cpow
    {n : ℕ} (hn : 0 < n) (beta t : ℝ) :
    smoothSaddleHTDirichletWeight n beta t =
      (n : ℂ) ^ (((beta - 1 : ℝ) : ℂ) - (t : ℂ) * Complex.I) := by
  rw [show (((beta - 1 : ℝ) : ℂ) - (t : ℂ) * Complex.I) =
      (((beta - 1 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I) by
        push_cast; ring]
  change smoothSaddleHTDirichletWeight n beta t =
    ((n : ℝ) : ℂ) ^
      (((beta - 1 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I)
  rw [ofReal_cpow_vertical_eq_rpow_mul_exp (by exact_mod_cast hn)]
  unfold smoothSaddleHTDirichletWeight
  congr 2
  push_cast
  ring

theorem smoothSaddleHTMangoldtTransform_eq_dirichletSum
    (y : ℕ) (beta t : ℝ) :
    smoothSaddleHTMangoldtTransform y beta t =
      ∑ n ∈ Finset.Icc 1 y,
        ((Λ n : ℝ) : ℂ) *
          (n : ℂ) ^ (((beta - 1 : ℝ) : ℂ) - (t : ℂ) * Complex.I) := by
  unfold smoothSaddleHTMangoldtTransform
  apply Finset.sum_congr rfl
  intro n hn
  rw [← smoothSaddleHTDirichletWeight_eq_cpow (Finset.mem_Icc.mp hn).1]
  unfold smoothSaddleHTDirichletWeight
  push_cast
  ring

theorem smoothSaddleHTMangoldtTransform_eq_sourceDirichletSum
    (y : ℕ) (beta t : ℝ) :
    smoothSaddleHTMangoldtTransform y beta t =
      smoothSaddleHTSourceDirichletSum y
        (smoothSaddleHTSourceExponent beta t) := by
  rw [smoothSaddleHTMangoldtTransform_eq_dirichletSum]
  unfold smoothSaddleHTSourceDirichletSum smoothSaddleHTSourceExponent
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : (n : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Finset.mem_Icc.mp hn).1)
  rw [div_eq_mul_inv, ← Complex.cpow_neg]
  congr 2
  push_cast
  ring

theorem smoothSaddleHTMangoldtMainTerm_eq_sourceMainTerm
    {y : ℕ} (hy : 0 < y) (beta t : ℝ) :
    smoothSaddleHTMangoldtMainTerm y beta t =
      smoothSaddleHTSourceMainTerm y
        (smoothSaddleHTSourceExponent beta t) := by
  unfold smoothSaddleHTMangoldtMainTerm smoothSaddleHTSourceMainTerm
    smoothSaddleHTSourceExponent
  have hpow := ofReal_cpow_vertical_eq_rpow_mul_exp
    (x := (y : ℝ)) (by exact_mod_cast hy) beta (-t)
  rw [show (1 : ℂ) - (↑(1 - beta) + ↑t * Complex.I) =
      (beta : ℂ) + ((-t : ℝ) : ℂ) * Complex.I by
        push_cast; ring]
  change (((y : ℝ) ^ beta : ℝ) : ℂ) *
      Complex.exp (-((t * Real.log y : ℝ) : ℂ) * Complex.I) /
        ((beta : ℂ) - (t : ℂ) * Complex.I) =
    ((y : ℝ) : ℂ) ^
        ((beta : ℂ) + ((-t : ℝ) : ℂ) * Complex.I) /
      ((beta : ℂ) + ((-t : ℝ) : ℂ) * Complex.I)
  rw [hpow]
  congr 2
  · congr 1
    push_cast
    ring
  · rw [Complex.ofReal_neg]
    ring

@[simp] theorem smoothSaddleHTSourceExponent_re (beta t : ℝ) :
    (smoothSaddleHTSourceExponent beta t).re = 1 - beta := by
  simp [smoothSaddleHTSourceExponent]

@[simp] theorem smoothSaddleHTSourceExponent_im (beta t : ℝ) :
    (smoothSaddleHTSourceExponent beta t).im = t := by
  simp [smoothSaddleHTSourceExponent]

theorem one_sub_smoothSaddleHTSourceExponent_ne_zero
    {beta : ℝ} (hbeta : 0 < beta) (t : ℝ) :
    (1 : ℂ) - smoothSaddleHTSourceExponent beta t ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simp [smoothSaddleHTSourceExponent] at hre
  linarith

/-- The source-coordinate shifted-Perron assertion at a fixed `epsilon` and
displayed `O_epsilon` constant. -/
def SmoothSaddleHTShiftedPerronEstimateAt (epsilon C : ℝ) : Prop :=
  0 < C ∧ ∀ (y : ℕ) (beta t : ℝ),
    2 ≤ y → 0 < beta → beta < 1 →
      |t| ≤ smoothSaddleHTFrequencyCeiling y epsilon →
        ‖smoothSaddleHTSourceDirichletSum y
              (smoothSaddleHTSourceExponent beta t) -
            smoothSaddleHTSourceMainTerm y
              (smoothSaddleHTSourceExponent beta t)‖ ≤
          C * smoothSaddleHTMangoldtError y beta epsilon

/-- The source-faithful shifted-Perron form of HT Lemma 6. -/
def SmoothSaddleHTShiftedPerronEstimate : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 →
    ∃ C : ℝ, SmoothSaddleHTShiftedPerronEstimateAt epsilon C

theorem smoothSaddleHTShiftedPerronEstimateAt_iff_mangoldtTransformEstimateAt
    (epsilon C : ℝ) :
    SmoothSaddleHTShiftedPerronEstimateAt epsilon C ↔
      SmoothSaddleHTMangoldtTransformEstimateAt epsilon C := by
  constructor
  · rintro ⟨hC, h⟩
    refine ⟨hC, ?_⟩
    intro y beta t hy hbeta hbetaOne ht
    rw [smoothSaddleHTMangoldtTransform_eq_sourceDirichletSum,
      smoothSaddleHTMangoldtMainTerm_eq_sourceMainTerm (by omega)]
    exact h y beta t hy hbeta hbetaOne ht
  · rintro ⟨hC, h⟩
    refine ⟨hC, ?_⟩
    intro y beta t hy hbeta hbetaOne ht
    rw [← smoothSaddleHTMangoldtTransform_eq_sourceDirichletSum,
      ← smoothSaddleHTMangoldtMainTerm_eq_sourceMainTerm (by omega)]
    exact h y beta t hy hbeta hbetaOne ht

theorem smoothSaddleHTShiftedPerronEstimate_iff_mangoldtTransformEstimate :
    SmoothSaddleHTShiftedPerronEstimate ↔
      SmoothSaddleHTMangoldtTransformEstimate := by
  constructor
  · intro h epsilon hepsilon hepsilonOne
    obtain ⟨C, hC⟩ := h epsilon hepsilon hepsilonOne
    exact ⟨C,
      (smoothSaddleHTShiftedPerronEstimateAt_iff_mangoldtTransformEstimateAt
        epsilon C).mp hC⟩
  · intro h epsilon hepsilon hepsilonOne
    obtain ⟨C, hC⟩ := h epsilon hepsilon hepsilonOne
    exact ⟨C,
      (smoothSaddleHTShiftedPerronEstimateAt_iff_mangoldtTransformEstimateAt
        epsilon C).mpr hC⟩

theorem sum_range_vonMangoldt_cast_eq_psi (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (((Λ k : ℝ)) : ℂ) =
      ((Chebyshev.psi n : ℝ) : ℂ) := by
  rw [← Complex.ofReal_sum]
  congr 1
  rw [Chebyshev.psi_eq_sum_Icc]
  have hfloor : ⌊((n : ℕ) : ℝ)⌋₊ = n := by norm_num
  rw [hfloor]
  congr 1
  ext k
  simp

theorem smoothSaddleHTMangoldtTransform_abel
    {y : ℕ} (hy : 0 < y) (beta t : ℝ) :
    smoothSaddleHTMangoldtTransform y beta t =
      smoothSaddleHTDirichletWeight y beta t *
          ((Chebyshev.psi y : ℝ) : ℂ) +
        ∑ n ∈ Finset.Ico 1 y,
          (smoothSaddleHTDirichletWeight n beta t -
              smoothSaddleHTDirichletWeight (n + 1) beta t) *
            ((Chebyshev.psi n : ℝ) : ℂ) := by
  have hsets : Finset.Icc 1 y = Finset.Ioc 0 y := by
    ext n
    simp
    omega
  have htransform :
      smoothSaddleHTMangoldtTransform y beta t =
        ∑ n ∈ Finset.Ioc 0 y,
          smoothSaddleHTDirichletWeight n beta t * (((Λ n : ℝ)) : ℂ) := by
    unfold smoothSaddleHTMangoldtTransform
    rw [hsets]
    apply Finset.sum_congr rfl
    intro n hn
    unfold smoothSaddleHTDirichletWeight
    push_cast
    ring
  rw [htransform]
  have hab := Finset.sum_Ioc_by_parts
    (f := fun n : ℕ ↦ smoothSaddleHTDirichletWeight n beta t)
    (g := fun n : ℕ ↦ (((Λ n : ℝ)) : ℂ)) hy
  simp only [smul_eq_mul, sum_range_vonMangoldt_cast_eq_psi] at hab
  rw [hab]
  have hpsiZero : Chebyshev.psi (0 : ℝ) = 0 := by
    rw [Chebyshev.psi_eq_sum_Icc]
    norm_num
  simp only [Nat.cast_zero, hpsiZero, Complex.ofReal_zero, mul_zero, sub_zero]
  have hsets' : Finset.Ioc 0 (y - 1) = Finset.Ico 1 y := by
    ext n
    simp
    omega
  rw [hsets', sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  ring

end

end Tao2026
