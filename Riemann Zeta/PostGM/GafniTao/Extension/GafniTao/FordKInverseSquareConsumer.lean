import GafniTao.FordCompleteInverseSquare
import GafniTao.FordKZeroSeries

/-!
# The far-zero part of Ford's `K` series

This file connects the complete multiplicity-weighted inverse-square estimate
to the literal zero terms in Ford's contour formula.  The centre is exactly
`1 + it`, and the cutoff is the same closed distance cutoff used in Ford's
`K(s)` lemma.
-/

open Complex Finset Set
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- The finite far-zero portion of Ford's literal zero sum. -/
noncomputable def fordFiniteKZeroOutside
    (F₀ : ℂ → ℂ) (t T v : ℝ) : ℂ :=
  ∑ rho ∈ (zeroSet 0 T).filter (fun rho =>
      v ≤ fordLocalDistance t rho),
    fordKZeroTerm F₀ ((1 : ℂ) + (t : ℂ) * I) rho

/-- The complementary strict local part.  Its fixed height contains every
zero at distance strictly less than `v` from `1 + it`. -/
noncomputable def fordKZeroInside
    (F₀ : ℂ → ℂ) (t v : ℝ) : ℂ :=
  ∑ rho ∈ (zeroSet 0 (|t| + v)).filter (fun rho =>
      fordLocalDistance t rho < v),
    fordKZeroTerm F₀ ((1 : ℂ) + (t : ℂ) * I) rho

theorem fordFiniteKZeroInside_eq_fixed
    {F₀ : ℂ → ℂ} {t T v : ℝ}
    (hheight : |t| + v ≤ T) :
    (∑ rho ∈ (zeroSet 0 T).filter (fun rho =>
        fordLocalDistance t rho < v),
      fordKZeroTerm F₀ ((1 : ℂ) + (t : ℂ) * I) rho) =
      fordKZeroInside F₀ t v := by
  classical
  unfold fordKZeroInside
  apply Finset.sum_congr
  · ext rho
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hrho, hdist⟩
      have himDist : |t - rho.im| ≤ fordLocalDistance t rho := by
        simpa [fordLocalDistance, mul_comm] using
          Complex.abs_im_le_norm ((1 : ℂ) + (t : ℂ) * I - rho)
      have himAbs : |rho.im| ≤ |t| + v := by
        calc
          |rho.im| = |t - (t - rho.im)| := by ring_nf
          _ ≤ |t| + |t - rho.im| := abs_sub _ _
          _ ≤ |t| + v := by linarith
      exact ⟨mem_zeroSet_of_abs_im_le hrho himAbs, hdist⟩
    · rintro ⟨hrho, hdist⟩
      exact ⟨zeroSet_mono_height hheight hrho, hdist⟩
  · intro rho _
    rfl

/-- Exact finite local/far partition of the zero term. -/
theorem sum_zeroSet_fordKZeroTerm_eq_inside_add_outside
    {F₀ : ℂ → ℂ} {t T v : ℝ}
    (hheight : |t| + v ≤ T) :
    (∑ rho ∈ zeroSet 0 T,
        fordKZeroTerm F₀ ((1 : ℂ) + (t : ℂ) * I) rho) =
      fordKZeroInside F₀ t v + fordFiniteKZeroOutside F₀ t T v := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (zeroSet 0 T) (fun rho => fordLocalDistance t rho < v)
    (fun rho => fordKZeroTerm F₀ ((1 : ℂ) + (t : ℂ) * I) rho)
  calc
    (∑ rho ∈ zeroSet 0 T,
        fordKZeroTerm F₀ ((1 : ℂ) + (t : ℂ) * I) rho) =
        (∑ rho ∈ (zeroSet 0 T).filter
            (fun rho => fordLocalDistance t rho < v),
          fordKZeroTerm F₀ ((1 : ℂ) + (t : ℂ) * I) rho) +
        ∑ rho ∈ (zeroSet 0 T).filter
            (fun rho => ¬ fordLocalDistance t rho < v),
          fordKZeroTerm F₀ ((1 : ℂ) + (t : ℂ) * I) rho :=
      hsplit.symm
    _ = fordKZeroInside F₀ t v +
        fordFiniteKZeroOutside F₀ t T v := by
      rw [fordFiniteKZeroInside_eq_fixed hheight]
      simp only [fordFiniteKZeroOutside, not_lt]

/-- The absolutely convergent far part of Ford's complete zero series. -/
noncomputable def fordKZeroOutside
    (F₀ : ℂ → ℂ) (t v : ℝ) : ℂ :=
  fordKZeroSeries F₀ ((1 : ℂ) + (t : ℂ) * I) -
    fordKZeroInside F₀ t v

theorem tendsto_fordFiniteKZeroOutside
    {F₀ : ℂ → ℂ} {D t v : ℝ} (hD : 0 ≤ D)
    (hF₀ : ∀ z : ℂ, 0 ≤ z.re → v ≤ ‖z‖ →
      ‖F₀ z‖ ≤ D / ‖z‖ ^ 2) :
    Filter.Tendsto
      (fun N : ℕ => fordFiniteKZeroOutside F₀ t N v)
      Filter.atTop (nhds (fordKZeroOutside F₀ t v)) := by
  have htotal := tendsto_sum_zeroSet_nat_fordKZeroTerm
    (s := (1 : ℂ) + (t : ℂ) * I) (by norm_num) hD hF₀
  have hinside : Filter.Tendsto
      (fun _ : ℕ => fordKZeroInside F₀ t v) Filter.atTop
      (nhds (fordKZeroInside F₀ t v)) := tendsto_const_nhds
  have hsub := htotal.sub hinside
  apply hsub.congr'
  filter_upwards [Filter.eventually_ge_atTop ⌈|t| + v⌉₊] with N hN
  have hheight : |t| + v ≤ (N : ℝ) :=
    (Nat.le_ceil (|t| + v)).trans (by exact_mod_cast hN)
  have hsplit := sum_zeroSet_fordKZeroTerm_eq_inside_add_outside
    (F₀ := F₀) hheight
  rw [hsplit]
  ring

theorem norm_fordFiniteKZeroOutside_le_inverseSquare
    {F₀ : ℂ → ℂ} {D t T v : ℝ}
    (hF₀ : ∀ z : ℂ, 0 ≤ z.re → v ≤ ‖z‖ →
      ‖F₀ z‖ ≤ D / ‖z‖ ^ 2) :
    ‖fordFiniteKZeroOutside F₀ t T v‖ ≤
      D * fordFiniteInverseSquareOutside t T v := by
  classical
  unfold fordFiniteKZeroOutside fordFiniteInverseSquareOutside
  calc
    ‖∑ rho ∈ (zeroSet 0 T).filter
        (fun rho => v ≤ fordLocalDistance t rho),
        fordKZeroTerm F₀ ((1 : ℂ) + (t : ℂ) * I) rho‖ ≤
        ∑ rho ∈ (zeroSet 0 T).filter
          (fun rho => v ≤ fordLocalDistance t rho),
          ‖fordKZeroTerm F₀ ((1 : ℂ) + (t : ℂ) * I) rho‖ :=
      norm_sum_le _ _
    _ ≤ ∑ rho ∈ (zeroSet 0 T).filter
          (fun rho => v ≤ fordLocalDistance t rho),
          (zeroMultiplicity rho : ℝ) *
            (D / fordLocalDistance t rho ^ 2) := by
      apply Finset.sum_le_sum
      intro rho hrho
      have hmem := Finset.mem_filter.mp hrho
      have hzero := mem_zeroSet_zero_data hmem.1
      have hre : 0 ≤
          (((1 : ℂ) + (t : ℂ) * I) - rho).re := by
        simp only [sub_re, add_re, one_re, mul_re, ofReal_re,
          I_re, ofReal_im, I_im]
        linarith [hzero.2.1]
      have hdist :
          fordLocalDistance t rho =
            ‖((1 : ℂ) + (t : ℂ) * I) - rho‖ := rfl
      have hF := hF₀ (((1 : ℂ) + (t : ℂ) * I) - rho)
        hre (by simpa [hdist] using hmem.2)
      rw [fordKZeroTerm, norm_mul, RCLike.norm_natCast]
      exact mul_le_mul_of_nonneg_left hF (by positivity)
    _ = D * ∑ rho ∈ (zeroSet 0 T).filter
          (fun rho => v ≤ fordLocalDistance t rho),
          (zeroMultiplicity rho : ℝ) /
            fordLocalDistance t rho ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro rho _
      ring

/-- The complete finite Ford far-zero estimate obtained by inserting the
native general zeta-growth bound into the exact zero terms. -/
theorem norm_fordFiniteKZeroOutside_le_general
    {F₀ : ℂ → ℂ} {A B D t T v : ℝ}
    (hFord : FordGeneralZetaGrowthBound A B)
    (hA : 1 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (ht : 100 ≤ t) (hv : 0 < v) (hvUpper : v ≤ 1 / 4)
    (hF₀ : ∀ z : ℂ, 0 ≤ z.re → v ≤ ‖z‖ →
      ‖F₀ z‖ ≤ D / ‖z‖ ^ 2) :
    ‖fordFiniteKZeroOutside F₀ t T v‖ ≤
      D * (fordGeneralLocalCountConstant *
          (fordGeneralLocalCountBase A t v / v ^ 2 +
            20 * B * Real.log t * v ^ (-1 / 2 : ℝ)) +
        225 * globalLocalZeroLogConstant *
          (Real.log (fordAdaptiveZeroBinHeight ⌊t⌋) *
              fordInverseSquareBinMass +
            fordInverseSquareBinLogMass)) := by
  calc
    ‖fordFiniteKZeroOutside F₀ t T v‖ ≤
        D * fordFiniteInverseSquareOutside t T v :=
      norm_fordFiniteKZeroOutside_le_inverseSquare hF₀
    _ ≤ D * (fordGeneralLocalCountConstant *
          (fordGeneralLocalCountBase A t v / v ^ 2 +
            20 * B * Real.log t * v ^ (-1 / 2 : ℝ)) +
        225 * globalLocalZeroLogConstant *
          (Real.log (fordAdaptiveZeroBinHeight ⌊t⌋) *
              fordInverseSquareBinMass +
            fordInverseSquareBinLogMass)) := by
      gcongr
      exact fordFiniteInverseSquareOutside_le_general
        hFord hA hB ht hv hvUpper

/-- Uniform complete far-series estimate.  Unlike a cutoff-dependent shell
bound, this is the literal infinite zero contribution in Ford's formula. -/
theorem norm_fordKZeroOutside_le_general
    {F₀ : ℂ → ℂ} {A B D t v : ℝ}
    (hFord : FordGeneralZetaGrowthBound A B)
    (hA : 1 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (ht : 100 ≤ t) (hv : 0 < v) (hvUpper : v ≤ 1 / 4)
    (hF₀ : ∀ z : ℂ, 0 ≤ z.re → v ≤ ‖z‖ →
      ‖F₀ z‖ ≤ D / ‖z‖ ^ 2) :
    ‖fordKZeroOutside F₀ t v‖ ≤
      D * (fordGeneralLocalCountConstant *
          (fordGeneralLocalCountBase A t v / v ^ 2 +
            20 * B * Real.log t * v ^ (-1 / 2 : ℝ)) +
        225 * globalLocalZeroLogConstant *
          (Real.log (fordAdaptiveZeroBinHeight ⌊t⌋) *
              fordInverseSquareBinMass +
            fordInverseSquareBinLogMass)) := by
  apply le_of_tendsto (tendsto_fordFiniteKZeroOutside hD hF₀).norm
  exact Filter.Eventually.of_forall fun N =>
    norm_fordFiniteKZeroOutside_le_general
      hFord hA hB hD ht hv hvUpper hF₀

#print axioms norm_fordFiniteKZeroOutside_le_inverseSquare
#print axioms norm_fordFiniteKZeroOutside_le_general
#print axioms fordFiniteKZeroInside_eq_fixed
#print axioms sum_zeroSet_fordKZeroTerm_eq_inside_add_outside
#print axioms tendsto_fordFiniteKZeroOutside
#print axioms norm_fordKZeroOutside_le_general

end

end GafniTao
