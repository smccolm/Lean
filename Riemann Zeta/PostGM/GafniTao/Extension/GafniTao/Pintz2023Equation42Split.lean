import GafniTao.Pintz2023Equation42Series

/-!
# Pintz (2023), equations (4.2)--(4.5): exact source cutoff

The complete `a_n` series is split at the literal source endpoint
`Y₁ = ceil (exp (lambda + 3))`.  This is an exact identity; estimates for the
discarded part are kept for the next module.
-/

open Complex MeasureTheory
open scoped BigOperators

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

/-- Pintz's literal endpoint `Y₁ = Y e³`, with `Y = exp lambda`. -/
noncomputable def pintz2023Cutoff (lambda : ℝ) : ℕ :=
  Nat.ceil (Real.exp (lambda + 3))

noncomputable def pintz2023WeightedTerm
    (X : ℕ) (rho : ℂ) (lambda : ℝ) (n : ℕ) : ℂ :=
  LSeries.term (pintz2023Coeff X) rho n *
    pintz2023GaussianWeight lambda n

noncomputable def pintz2023HeadTerm
    (X : ℕ) (rho : ℂ) (lambda : ℝ) (n : ℕ) : ℂ :=
  if n ≤ pintz2023Cutoff lambda then
    pintz2023WeightedTerm X rho lambda n
  else 0

noncomputable def pintz2023TailTerm
    (X : ℕ) (rho : ℂ) (lambda : ℝ) (n : ℕ) : ℂ :=
  if pintz2023Cutoff lambda < n then
    pintz2023WeightedTerm X rho lambda n
  else 0

theorem pintz2023WeightedTerm_eq_head_add_tail
    (X : ℕ) (rho : ℂ) (lambda : ℝ) (n : ℕ) :
    pintz2023WeightedTerm X rho lambda n =
      pintz2023HeadTerm X rho lambda n +
        pintz2023TailTerm X rho lambda n := by
  by_cases hn : n ≤ pintz2023Cutoff lambda
  · rw [pintz2023HeadTerm, if_pos hn, pintz2023TailTerm, if_neg]
    · simp
    · omega
  · rw [pintz2023HeadTerm, if_neg hn, pintz2023TailTerm, if_pos]
    · simp
    · omega

theorem summable_pintz2023WeightedTerm
    {X : ℕ} {rho : ℂ} {lambda : ℝ}
    (hrho : 1 / 2 ≤ rho.re) (hlambda : 0 < lambda) :
    Summable (pintz2023WeightedTerm X rho lambda) := by
  let D : ℝ := ‖(1 / (2 * Real.pi * I) : ℂ)‖
  have hbase := summable_integral_norm_pintz2023Equation42VerticalTerm
    (X := X) hrho hlambda
  apply summable_norm_iff.mp
  refine (hbase.mul_left D).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun n => ?_)
  unfold pintz2023WeightedTerm
  rw [← normalized_integral_pintz2023Equation42VerticalTerm_eq
    X rho lambda n]
  rw [norm_mul, norm_mul, norm_I]
  change D * 1 *
      ‖∫ t : ℝ, pintz2023Equation42VerticalTerm X rho lambda n t‖ ≤
    D * (∫ t : ℝ, ‖pintz2023Equation42VerticalTerm X rho lambda n t‖)
  rw [mul_one]
  exact mul_le_mul_of_nonneg_left
    (norm_integral_le_integral_norm _) (norm_nonneg _)

theorem summable_pintz2023HeadTerm
    (X : ℕ) (rho : ℂ) (lambda : ℝ) :
    Summable (pintz2023HeadTerm X rho lambda) := by
  apply summable_of_ne_finset_zero
    (s := Finset.range (pintz2023Cutoff lambda + 1))
  intro n hn
  rw [Finset.mem_range] at hn
  rw [pintz2023HeadTerm, if_neg]
  omega

theorem summable_pintz2023TailTerm
    {X : ℕ} {rho : ℂ} {lambda : ℝ}
    (hrho : 1 / 2 ≤ rho.re) (hlambda : 0 < lambda) :
    Summable (pintz2023TailTerm X rho lambda) := by
  have hall := summable_pintz2023WeightedTerm
    (X := X) hrho hlambda
  have hhead := summable_pintz2023HeadTerm X rho lambda
  have hdiff := hall.sub hhead
  exact hdiff.congr (fun n => by
    rw [pintz2023WeightedTerm_eq_head_add_tail X rho lambda n]
    ring)

/-- Exact finite-head plus infinite-tail decomposition of the true
finite-mollifier series. -/
theorem pintz2023_equation_4_5_exact
    {X : ℕ} {rho : ℂ} {lambda : ℝ}
    (hrho : 1 / 2 ≤ rho.re) (hlambda : 0 < lambda) :
    pintz2023Equation42Integral X rho lambda =
      (∑ n ∈ Finset.range (pintz2023Cutoff lambda + 1),
        pintz2023WeightedTerm X rho lambda n) +
      ∑' n : ℕ, pintz2023TailTerm X rho lambda n := by
  rw [pintz2023_equation_4_2_complete hrho hlambda]
  change (∑' n : ℕ, pintz2023WeightedTerm X rho lambda n) = _
  have hhead := summable_pintz2023HeadTerm X rho lambda
  have htail := summable_pintz2023TailTerm
    (X := X) hrho hlambda
  calc
    (∑' n : ℕ, pintz2023WeightedTerm X rho lambda n) =
        ∑' n : ℕ, (pintz2023HeadTerm X rho lambda n +
          pintz2023TailTerm X rho lambda n) := by
      apply tsum_congr
      intro n
      exact pintz2023WeightedTerm_eq_head_add_tail X rho lambda n
    _ = (∑' n : ℕ, pintz2023HeadTerm X rho lambda n) +
        ∑' n : ℕ, pintz2023TailTerm X rho lambda n :=
      hhead.tsum_add htail
    _ = (∑ n ∈ Finset.range (pintz2023Cutoff lambda + 1),
          pintz2023WeightedTerm X rho lambda n) +
        ∑' n : ℕ, pintz2023TailTerm X rho lambda n := by
      congr 1
      rw [tsum_eq_sum
        (s := Finset.range (pintz2023Cutoff lambda + 1))]
      · apply Finset.sum_congr rfl
        intro n hn
        rw [Finset.mem_range] at hn
        rw [pintz2023HeadTerm, if_pos]
        omega
      · intro n hn
        rw [Finset.mem_range] at hn
        rw [pintz2023HeadTerm, if_neg]
        omega

theorem pintz2023WeightedTerm_zero (X : ℕ) (rho : ℂ) (lambda : ℝ) :
    pintz2023WeightedTerm X rho lambda 0 = 0 := by
  simp [pintz2023WeightedTerm, LSeries.term_def]

theorem pintz2023WeightedTerm_eq_zero_of_middle
    {X n : ℕ} (rho : ℂ) (lambda : ℝ)
    (hn : 1 < n) (hnX : n ≤ X) :
    pintz2023WeightedTerm X rho lambda n = 0 := by
  rw [pintz2023WeightedTerm, LSeries.term_of_ne_zero (by omega)]
  rw [pintz2023Coeff_eq_zero hn hnX, zero_div, zero_mul]

theorem pintz2023GaussianWeight_one (lambda : ℝ) :
    pintz2023GaussianWeight lambda 1 =
      VerticalIntegral' (pintzGaussianKernel lambda) 3 := by
  unfold pintz2023GaussianWeight VerticalIntegral' VerticalIntegral
  congr 2
  apply integral_congr_ae
  filter_upwards [] with t
  simp

theorem pintz2023WeightedTerm_one
    {X : ℕ} (rho : ℂ) (lambda : ℝ) (hX : 1 ≤ X) :
    pintz2023WeightedTerm X rho lambda 1 =
      VerticalIntegral' (pintzGaussianKernel lambda) 3 := by
  unfold pintz2023WeightedTerm
  change LSeries.term (mollifiedZetaCoeff X) rho 1 *
      pintz2023GaussianWeight lambda 1 = _
  rw [LSeries.term_of_ne_zero (by omega)]
  rw [mollifiedZetaCoeff_eq_ite X 1 (by omega) hX]
  simp [pintz2023GaussianWeight_one]

/-- The finite part in (4.5) consists exactly of the residue-producing
`n=1` term and the source interval `(X,Y₁]`; all integers `1<n≤X`
vanish by Moebius inversion. -/
theorem pintz2023_head_eq_one_add_source_interval
    {X : ℕ} (rho : ℂ) (lambda : ℝ)
    (hX : 1 ≤ X) (hXC : X ≤ pintz2023Cutoff lambda) :
    (∑ n ∈ Finset.range (pintz2023Cutoff lambda + 1),
        pintz2023WeightedTerm X rho lambda n) =
      VerticalIntegral' (pintzGaussianKernel lambda) 3 +
        ∑ n ∈ Finset.Ioc X (pintz2023Cutoff lambda),
          pintz2023WeightedTerm X rho lambda n := by
  let f : ℕ → ℂ := pintz2023WeightedTerm X rho lambda
  let small : Finset ℕ :=
    insert 1 (Finset.Ioc X (pintz2023Cutoff lambda))
  have hsubset : small ⊆ Finset.range (pintz2023Cutoff lambda + 1) := by
    intro n hn
    rw [Finset.mem_insert] at hn
    rcases hn with rfl | hn
    · rw [Finset.mem_range]
      omega
    · rw [Finset.mem_range]
      have hnC := (Finset.mem_Ioc.mp hn).2
      omega
  have houtside : ∀ n ∈ Finset.range (pintz2023Cutoff lambda + 1),
      n ∉ small → f n = 0 := by
    intro n hnRange hnSmall
    have hnC : n ≤ pintz2023Cutoff lambda := by
      rw [Finset.mem_range] at hnRange
      omega
    by_cases hnZero : n = 0
    · subst n
      exact pintz2023WeightedTerm_zero X rho lambda
    have hnOne : n ≠ 1 := by
      intro hn
      subst n
      exact hnSmall (Finset.mem_insert_self 1 _)
    have hnGt : 1 < n := by omega
    have hnNotIoc : n ∉ Finset.Ioc X (pintz2023Cutoff lambda) := by
      intro hnIoc
      exact hnSmall (Finset.mem_insert_of_mem hnIoc)
    have hnX : n ≤ X := by
      have hnotLower : ¬ X < n := by
        intro hnLower
        exact hnNotIoc (Finset.mem_Ioc.mpr ⟨hnLower, hnC⟩)
      omega
    exact pintz2023WeightedTerm_eq_zero_of_middle rho lambda hnGt hnX
  have hsum :
      (∑ n ∈ small, f n) =
        ∑ n ∈ Finset.range (pintz2023Cutoff lambda + 1), f n :=
    Finset.sum_subset hsubset houtside
  have hOneNotMem : 1 ∉ Finset.Ioc X (pintz2023Cutoff lambda) := by
    rw [Finset.mem_Ioc]
    omega
  rw [← hsum]
  simp only [small, f, Finset.sum_insert hOneNotMem]
  rw [pintz2023WeightedTerm_one rho lambda hX]

/-- Pintz's equation (4.2), after the exact cutoff and Möbius
cancellation: the genuine finite-mollifier integral is the bare `n = 1`
Gaussian line, the literal source interval `X < n ≤ Y₁`, and the still
unestimated complete tail. -/
theorem pintz2023_equation_4_2_source_split
    {X : ℕ} {rho : ℂ} {lambda : ℝ}
    (hrho : 1 / 2 ≤ rho.re) (hlambda : 0 < lambda)
    (hX : 1 ≤ X) (hXC : X ≤ pintz2023Cutoff lambda) :
    pintz2023Equation42Integral X rho lambda =
      VerticalIntegral' (pintzGaussianKernel lambda) 3 +
        ∑ n ∈ Finset.Ioc X (pintz2023Cutoff lambda),
          pintz2023WeightedTerm X rho lambda n +
        ∑' n : ℕ, pintz2023TailTerm X rho lambda n := by
  rw [pintz2023_equation_4_5_exact hrho hlambda]
  rw [pintz2023_head_eq_one_add_source_interval rho lambda hX hXC]

#print axioms pintz2023_equation_4_5_exact
#print axioms pintz2023WeightedTerm_eq_zero_of_middle
#print axioms pintz2023_head_eq_one_add_source_interval
#print axioms pintz2023_equation_4_2_source_split

end

end GafniTao
