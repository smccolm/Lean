import RiemannZeta.GuthMaynard.HughesYoungBoundary

open Complex Finset MeasureTheory Set Topology
open scoped BigOperators ContDiff FourierTransform Interval Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Locally finite Hughes--Young dyadic partition

Hughes--Young equation (69) decomposes the absolutely convergent divisor-pair
series, rather than a sharp terminal rectangle.  Index zero below is the
isolated lower box and every successor index is one ordinary geometric box.
-/

/-- The complete list of physical dyadic scales.  Index zero is the lower
endpoint box centered at `1`; successor index `j+1` is the usual scale
`(sqrt 2)^j`. -/
noncomputable def hughesYoungFullDyadicScale : ℕ → ℝ
  | 0 => 1 / hughesYoungDyadicRatio
  | j + 1 => hughesYoungDyadicScale j

/-- The smooth cutoff at one scale of the complete dyadic partition. -/
noncomputable def hughesYoungFullDyadicCutoff (j : ℕ) (x : ℝ) : ℝ :=
  hughesYoungDyadicCutoffAt (hughesYoungFullDyadicScale j) x

theorem hughesYoungFullDyadicScale_pos (j : ℕ) :
    0 < hughesYoungFullDyadicScale j := by
  cases j with
  | zero =>
      simp only [hughesYoungFullDyadicScale]
      exact one_div_pos.mpr hughesYoungDyadicRatio_pos
  | succ j =>
      simp only [hughesYoungFullDyadicScale]
      exact hughesYoungDyadicScale_pos j

theorem hughesYoungFullDyadicCutoff_zero_nat {n : ℕ} (hn : 0 < n) :
    hughesYoungFullDyadicCutoff 0 (n : ℝ) =
      hughesYoungDyadicStep (n : ℝ) := by
  unfold hughesYoungFullDyadicCutoff hughesYoungFullDyadicScale
  exact hughesYoungDyadicStep_nat_eq_initialCutoff hn |>.symm

theorem hughesYoungFullDyadicCutoff_succ (j : ℕ) (x : ℝ) :
    hughesYoungFullDyadicCutoff (j + 1) x =
      hughesYoungDyadicCutoffAt (hughesYoungDyadicScale j) x := by
  rfl

/-- On the whole physical half-line `x ≥ 1`, the initial smooth box is
exactly the lower telescoping step. -/
theorem hughesYoungFullDyadicCutoff_zero_eq_step
    {x : ℝ} (hx : 1 ≤ x) :
    hughesYoungFullDyadicCutoff 0 x = hughesYoungDyadicStep x := by
  have hρ : hughesYoungDyadicRatio ≠ 0 :=
    hughesYoungDyadicRatio_pos.ne'
  have hdivide : x / (1 / hughesYoungDyadicRatio) =
      x * hughesYoungDyadicRatio := by
    field_simp [hρ]
  have hlarge : hughesYoungDyadicRatio ≤
      x / (1 / hughesYoungDyadicRatio) := by
    rw [hdivide]
    exact le_mul_of_one_le_left hughesYoungDyadicRatio_pos.le hx
  unfold hughesYoungFullDyadicCutoff hughesYoungFullDyadicScale
    hughesYoungDyadicCutoffAt hughesYoungDyadicCutoff
  have hcancel : x / (1 / hughesYoungDyadicRatio) /
      hughesYoungDyadicRatio = x := by
    field_simp [hρ]
  rw [hcancel, hughesYoungDyadicStep_eq_zero hlarge]
  ring

/-- Exact initial-box identity at an arbitrary real point. -/
theorem hughesYoungFullDyadicCutoff_zero_eq_step_sub_step
    (x : ℝ) :
    hughesYoungFullDyadicCutoff 0 x =
      hughesYoungDyadicStep x -
        hughesYoungDyadicStep (x * hughesYoungDyadicRatio) := by
  have hρ : hughesYoungDyadicRatio ≠ 0 :=
    hughesYoungDyadicRatio_pos.ne'
  have hdivide : x / (1 / hughesYoungDyadicRatio) =
      x * hughesYoungDyadicRatio := by
    field_simp [hρ]
  have hmulcancel : x * hughesYoungDyadicRatio /
      hughesYoungDyadicRatio = x := by
    field_simp [hρ]
  unfold hughesYoungFullDyadicCutoff hughesYoungFullDyadicScale
    hughesYoungDyadicCutoffAt hughesYoungDyadicCutoff
  rw [hdivide, hmulcancel]

theorem hughesYoungDyadicCutoffAt_eq_zero_of_le_scale
    {X x : ℝ} (hX : 0 < X) (hx : x ≤ X) :
    hughesYoungDyadicCutoffAt X x = 0 := by
  unfold hughesYoungDyadicCutoffAt
  apply hughesYoungDyadicCutoff_eq_zero_of_le_one
  exact (div_le_one hX).2 hx

/-- Once a positive integer lies below the terminal represented scale, every
later member of the geometric partition vanishes at that integer. -/
theorem hughesYoungFullDyadicCutoff_eq_zero_of_cover
    {n K j : ℕ} (hn : ((n : ℕ) : ℝ) ≤ hughesYoungDyadicRatio ^ (K + 1))
    (hj : K + 2 ≤ j) :
    hughesYoungFullDyadicCutoff j (n : ℝ) = 0 := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hj
  rw [show K + 2 + r = (K + 1 + r) + 1 by omega,
    hughesYoungFullDyadicCutoff_succ]
  apply hughesYoungDyadicCutoffAt_eq_zero_of_le_scale
    (hughesYoungDyadicScale_pos (K + 1 + r))
  exact hn.trans (by
    unfold hughesYoungDyadicScale
    apply pow_le_pow_right₀ one_lt_hughesYoungDyadicRatio.le
    omega)

/-- Real-variable local finiteness for the physical DFI integral. -/
theorem hughesYoungFullDyadicCutoff_eq_zero_of_real_cover
    {x : ℝ} {K j : ℕ}
    (hx : x ≤ hughesYoungDyadicRatio ^ (K + 1))
    (hj : K + 2 ≤ j) :
    hughesYoungFullDyadicCutoff j x = 0 := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hj
  rw [show K + 2 + r = (K + 1 + r) + 1 by omega,
    hughesYoungFullDyadicCutoff_succ]
  apply hughesYoungDyadicCutoffAt_eq_zero_of_le_scale
    (hughesYoungDyadicScale_pos (K + 1 + r))
  exact hx.trans (by
    unfold hughesYoungDyadicScale
    apply pow_le_pow_right₀ one_lt_hughesYoungDyadicRatio.le
    omega)

/-- Exact finite endpoint formula for the complete Hughes--Young dyadic
family.  The first term is the upper endpoint still represented at depth
`K`; the second is the genuine lower-boundary correction introduced by the
isolated zeroth box.  This identity does not require a support hypothesis. -/
theorem sum_range_hughesYoungFullDyadicCutoff_eq
    (K : ℕ) (x : ℝ) :
    (∑ j ∈ Finset.range (K + 2),
      hughesYoungFullDyadicCutoff j x) =
      hughesYoungDyadicStep
          (x / hughesYoungDyadicRatio ^ (K + 1)) -
        hughesYoungDyadicStep (x * hughesYoungDyadicRatio) := by
  rw [show K + 2 = (K + 1) + 1 by omega,
    Finset.sum_range_succ']
  rw [hughesYoungFullDyadicCutoff_zero_eq_step_sub_step]
  simp_rw [hughesYoungFullDyadicCutoff_succ]
  rw [sum_hughesYoungDyadicCutoff_eq]
  ring

/-- Complex-valued form of the exact finite endpoint formula. -/
theorem sum_range_hughesYoungFullDyadicCutoff_cast_eq
    (K : ℕ) (x : ℝ) :
    (∑ j ∈ Finset.range (K + 2),
      (hughesYoungFullDyadicCutoff j x : ℂ)) =
      ((hughesYoungDyadicStep
          (x / hughesYoungDyadicRatio ^ (K + 1)) -
        hughesYoungDyadicStep
          (x * hughesYoungDyadicRatio) : ℝ) : ℂ) := by
  push_cast
  exact_mod_cast sum_range_hughesYoungFullDyadicCutoff_eq K x

/-- The finite complete family is already a partition of unity on the
physical interval represented by its terminal scale. -/
theorem sum_range_hughesYoungFullDyadicCutoff_eq_one
    {K : ℕ} {x : ℝ} (hx : 1 ≤ x)
    (hxUpper : x ≤ hughesYoungDyadicRatio ^ (K + 1)) :
    (∑ j ∈ Finset.range (K + 2),
      hughesYoungFullDyadicCutoff j x) = 1 := by
  rw [sum_range_hughesYoungFullDyadicCutoff_eq]
  have hpow : 0 < hughesYoungDyadicRatio ^ (K + 1) :=
    pow_pos hughesYoungDyadicRatio_pos _
  rw [hughesYoungDyadicStep_eq_one ((div_le_one hpow).2 hxUpper),
    hughesYoungDyadicStep_eq_zero]
  · ring
  · exact le_mul_of_one_le_left hughesYoungDyadicRatio_pos.le hx

theorem sum_range_hughesYoungFullDyadicCutoff_cast_eq_one
    {K : ℕ} {x : ℝ} (hx : 1 ≤ x)
    (hxUpper : x ≤ hughesYoungDyadicRatio ^ (K + 1)) :
    (∑ j ∈ Finset.range (K + 2),
      (hughesYoungFullDyadicCutoff j x : ℂ)) = 1 := by
  rw [← Complex.ofReal_sum]
  norm_cast
  exact sum_range_hughesYoungFullDyadicCutoff_eq_one hx hxUpper

/-- The complete smooth dyadic family sums exactly to one at every real
physical coordinate `x ≥ 1`. -/
theorem tsum_hughesYoungFullDyadicCutoff_eq_one
    {x : ℝ} (hx : 1 ≤ x) :
    (∑' j : ℕ, hughesYoungFullDyadicCutoff j x) = 1 := by
  obtain ⟨K, hK⟩ := exists_hughesYoungDyadicCoverIndex x
  rw [tsum_eq_sum (s := Finset.range (K + 2))]
  · rw [show K + 2 = (K + 1) + 1 by omega,
      Finset.sum_range_succ']
    rw [hughesYoungFullDyadicCutoff_zero_eq_step hx]
    simp_rw [hughesYoungFullDyadicCutoff_succ]
    simpa only [add_comm] using
      hughesYoungDyadicStep_add_sum_cutoff_eq_one hK
  · intro j hj
    rw [Finset.mem_range, not_lt] at hj
    exact hughesYoungFullDyadicCutoff_eq_zero_of_real_cover hK hj

/-- Exact locally finite partition at every real point.  Below the physical
endpoint the full family equals the smooth lower cutoff
`1 - step (x * sqrt 2)`; it becomes one exactly for `x ≥ 1`. -/
theorem tsum_hughesYoungFullDyadicCutoff_eq_one_sub_step (x : ℝ) :
    (∑' j : ℕ, hughesYoungFullDyadicCutoff j x) =
      1 - hughesYoungDyadicStep (x * hughesYoungDyadicRatio) := by
  obtain ⟨K, hK⟩ := exists_hughesYoungDyadicCoverIndex x
  rw [tsum_eq_sum (s := Finset.range (K + 2))]
  · rw [show K + 2 = (K + 1) + 1 by omega,
      Finset.sum_range_succ']
    rw [hughesYoungFullDyadicCutoff_zero_eq_step_sub_step]
    simp_rw [hughesYoungFullDyadicCutoff_succ]
    have hpartition := hughesYoungDyadicStep_add_sum_cutoff_eq_one hK
    linarith
  · intro j hj
    rw [Finset.mem_range, not_lt] at hj
    exact hughesYoungFullDyadicCutoff_eq_zero_of_real_cover hK hj

theorem tsum_hughesYoungFullDyadicCutoff_cast_eq_one_sub_step (x : ℝ) :
    (∑' j : ℕ, (hughesYoungFullDyadicCutoff j x : ℂ)) =
      ((1 - hughesYoungDyadicStep
        (x * hughesYoungDyadicRatio) : ℝ) : ℂ) := by
  rw [← Complex.ofReal_tsum]
  norm_cast
  exact tsum_hughesYoungFullDyadicCutoff_eq_one_sub_step x

/-- The real-variable dyadic family is locally finite.  This is the
continuous counterpart of
`finite_support_hughesYoungFullDyadicCutoff_nat`; it is needed when the
DFI central integrals are reassembled before restricting their variables
to the divisor lattice. -/
theorem finite_support_hughesYoungFullDyadicCutoff (x : ℝ) :
    Set.Finite (Function.support fun j : ℕ =>
      hughesYoungFullDyadicCutoff j x) := by
  obtain ⟨K, hK⟩ := exists_hughesYoungDyadicCoverIndex x
  apply (Finset.finite_toSet (Finset.range (K + 2))).subset
  intro j hj
  by_contra hjRange
  have hjLower : K + 2 ≤ j := by
    apply Nat.le_of_not_gt
    intro hjLt
    exact hjRange (by simpa only [Finset.mem_coe, Finset.mem_range] using hjLt)
  exact hj (hughesYoungFullDyadicCutoff_eq_zero_of_real_cover hK hjLower)

/-- Consequently the full smooth dyadic family is summable at every real
physical coordinate, including the continuous variables in DFI equation
(27). -/
theorem summable_hughesYoungFullDyadicCutoff (x : ℝ) :
    Summable (fun j : ℕ => hughesYoungFullDyadicCutoff j x) :=
  summable_of_hasFiniteSupport
    (finite_support_hughesYoungFullDyadicCutoff x)

theorem tsum_hughesYoungFullDyadicCutoff_cast_eq_one
    {x : ℝ} (hx : 1 ≤ x) :
    (∑' j : ℕ, (hughesYoungFullDyadicCutoff j x : ℂ)) = 1 := by
  rw [← Complex.ofReal_tsum]
  norm_cast
  exact tsum_hughesYoungFullDyadicCutoff_eq_one hx

/-- The complete smooth family is locally finite and sums exactly to one at
every positive natural divisor coordinate.  This is the infinite-series
version of Hughes--Young's dyadic partition in equation (69). -/
theorem tsum_hughesYoungFullDyadicCutoff_nat_eq_one
    {n : ℕ} (hn : 0 < n) :
    (∑' j : ℕ, hughesYoungFullDyadicCutoff j (n : ℝ)) = 1 := by
  obtain ⟨K, hK⟩ := exists_hughesYoungDyadicCoverIndex (n : ℝ)
  rw [tsum_eq_sum (s := Finset.range (K + 2))]
  · rw [show K + 2 = (K + 1) + 1 by omega,
      Finset.sum_range_succ']
    rw [hughesYoungFullDyadicCutoff_zero_nat hn]
    simp_rw [hughesYoungFullDyadicCutoff_succ]
    simpa only [add_comm] using
      hughesYoungDyadicStep_add_sum_cutoff_eq_one hK
  · intro j hj
    rw [Finset.mem_range, not_lt] at hj
    exact hughesYoungFullDyadicCutoff_eq_zero_of_cover hK hj

/-- At a positive natural coordinate the complete partition has finite
support, a fact used to interchange it with the absolutely convergent AFE
series without introducing a limiting sharp boundary. -/
theorem finite_support_hughesYoungFullDyadicCutoff_nat
    (n : ℕ) :
    Set.Finite (Function.support fun j : ℕ =>
      hughesYoungFullDyadicCutoff j (n : ℝ)) := by
  obtain ⟨K, hK⟩ := exists_hughesYoungDyadicCoverIndex (n : ℝ)
  apply (Finset.finite_toSet (Finset.range (K + 2))).subset
  intro j hj
  by_contra hjRange
  have hjLower : K + 2 ≤ j := by
    apply Nat.le_of_not_gt
    intro hjLt
    exact hjRange (by simpa only [Finset.mem_coe, Finset.mem_range] using hjLt)
  exact hj (hughesYoungFullDyadicCutoff_eq_zero_of_cover hK hjLower)

theorem summable_hughesYoungFullDyadicCutoff_nat (n : ℕ) :
    Summable (fun j : ℕ => hughesYoungFullDyadicCutoff j (n : ℝ)) :=
  summable_of_hasFiniteSupport
    (finite_support_hughesYoungFullDyadicCutoff_nat n)

theorem tsum_hughesYoungFullDyadicCutoff_nat_cast_eq_one
    {n : ℕ} (hn : 0 < n) :
    (∑' j : ℕ, (hughesYoungFullDyadicCutoff j (n : ℝ) : ℂ)) = 1 := by
  rw [← Complex.ofReal_tsum]
  norm_cast
  exact tsum_hughesYoungFullDyadicCutoff_nat_eq_one hn

/-- One divisor-pair term localized to a complete pair of Hughes--Young
dyadic boxes in the gcd-reduced physical coordinates. -/
noncomputable def hughesYoungFullDyadicArithmeticTerm
    (T t c H : ℝ) (h k i j : ℕ) (p : ℕ × ℕ) : ℂ :=
  (hughesYoungFullDyadicCutoff i
      ((hughesYoungReducedLeft h k * p.1 : ℕ) : ℝ) : ℂ) *
    (hughesYoungFullDyadicCutoff j
      ((hughesYoungReducedRight h k * p.2 : ℕ) : ℝ) : ℂ) *
    hughesYoungFiniteArithmeticTerm T t c H h k p

theorem hughesYoungFiniteArithmeticTerm_eq_zero_of_left
    (T t c H : ℝ) (h k n : ℕ) :
    hughesYoungFiniteArithmeticTerm T t c H h k (0, n) = 0 := by
  unfold hughesYoungFiniteArithmeticTerm hughesYoungRightPairTerm
  simp_rw [divisorDirichletTerm_eq_divisorWeight_mul_cpow]
  simp [divisorWeight]

theorem hughesYoungFiniteArithmeticTerm_eq_zero_of_right
    (T t c H : ℝ) (h k m : ℕ) :
    hughesYoungFiniteArithmeticTerm T t c H h k (m, 0) = 0 := by
  unfold hughesYoungFiniteArithmeticTerm hughesYoungRightPairTerm
  simp_rw [divisorDirichletTerm_eq_divisorWeight_mul_cpow]
  simp [divisorWeight]

/-- Pointwise equation-(69) reconstruction: the complete double dyadic
partition reproduces each term of the opened AFE series exactly. -/
theorem tsum_hughesYoungFullDyadicArithmeticTerm_eq
    (T t c H : ℝ) {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    (p : ℕ × ℕ) :
    (∑' i : ℕ, ∑' j : ℕ,
      hughesYoungFullDyadicArithmeticTerm T t c H h k i j p) =
        hughesYoungFiniteArithmeticTerm T t c H h k p := by
  rcases p with ⟨m, n⟩
  by_cases hm : m = 0
  · subst m
    simp only [hughesYoungFullDyadicArithmeticTerm,
      hughesYoungFiniteArithmeticTerm_eq_zero_of_left, mul_zero,
      tsum_zero]
  by_cases hn : n = 0
  · subst n
    simp only [hughesYoungFullDyadicArithmeticTerm,
      hughesYoungFiniteArithmeticTerm_eq_zero_of_right, mul_zero,
      tsum_zero]
  have hmPos : 0 < hughesYoungReducedLeft h k * m :=
    Nat.mul_pos (hughesYoungReducedLeft_pos (k := k) hh) (Nat.pos_of_ne_zero hm)
  have hnPos : 0 < hughesYoungReducedRight h k * n :=
    Nat.mul_pos (hughesYoungReducedRight_pos hh hk) (Nat.pos_of_ne_zero hn)
  have hleft :
      (∑' i : ℕ, (hughesYoungFullDyadicCutoff i
        ((hughesYoungReducedLeft h k * m : ℕ) : ℝ) : ℂ)) = 1 :=
    tsum_hughesYoungFullDyadicCutoff_nat_cast_eq_one hmPos
  have hright :
      (∑' j : ℕ, (hughesYoungFullDyadicCutoff j
        ((hughesYoungReducedRight h k * n : ℕ) : ℝ) : ℂ)) = 1 :=
    tsum_hughesYoungFullDyadicCutoff_nat_cast_eq_one hnPos
  unfold hughesYoungFullDyadicArithmeticTerm
  calc
    (∑' i : ℕ, ∑' j : ℕ,
        (hughesYoungFullDyadicCutoff i
            ((hughesYoungReducedLeft h k * m : ℕ) : ℝ) : ℂ) *
          (hughesYoungFullDyadicCutoff j
            ((hughesYoungReducedRight h k * n : ℕ) : ℝ) : ℂ) *
          hughesYoungFiniteArithmeticTerm T t c H h k (m, n)) =
      (∑' i : ℕ, (hughesYoungFullDyadicCutoff i
          ((hughesYoungReducedLeft h k * m : ℕ) : ℝ) : ℂ)) *
        ((∑' j : ℕ, (hughesYoungFullDyadicCutoff j
            ((hughesYoungReducedRight h k * n : ℕ) : ℝ) : ℂ)) *
          hughesYoungFiniteArithmeticTerm T t c H h k (m, n)) := by
      simp_rw [tsum_mul_right, tsum_mul_left]
      rw [tsum_mul_right]
      rw [mul_assoc]
    _ = hughesYoungFiniteArithmeticTerm T t c H h k (m, n) := by
      rw [hleft, hright]
      ring

theorem summable_hughesYoungFiniteArithmeticTerm
    (T t H : ℝ) {c : ℝ} (hc : 1 / 2 < c) (h k : ℕ) :
    Summable (hughesYoungFiniteArithmeticTerm T t c H h k) := by
  have hpair : Summable (fun p : ℕ × ℕ =>
      ∫ u in -H..H, hughesYoungRightPairTerm t c u p) :=
    (intervalIntegral.hasSum_intervalIntegral_of_summable_norm
      (summable_hughesYoungRightPair_restrict_norm t H hc)).summable
  let A : ℂ :=
    shortMobiusSquareCoeff T h * (h : ℂ) ^ (-afeCriticalPoint t) *
      shortMobiusSquareCoeff T k * (k : ℂ) ^ (-afeCriticalPoint (-t)) *
      (1 / (Real.pi : ℂ))
  exact (hpair.mul_left A).congr (fun p => by
    unfold hughesYoungFiniteArithmeticTerm A
    ring)

theorem hughesYoungFullDyadicCutoff_nonneg_nat (j n : ℕ) :
    0 ≤ hughesYoungFullDyadicCutoff j (n : ℝ) :=
  (hughesYoungDyadicCutoffAt_mem_Icc
    (hughesYoungFullDyadicScale_pos j) (by positivity)).1

/-- Absolute mass is preserved term by term by the two nonnegative smooth
partitions.  This is the local Tonelli identity behind equation (69). -/
theorem tsum_norm_hughesYoungFullDyadicArithmeticTerm_eq
    (T t c H : ℝ) {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    (p : ℕ × ℕ) :
    (∑' i : ℕ, ∑' j : ℕ,
      ‖hughesYoungFullDyadicArithmeticTerm T t c H h k i j p‖) =
        ‖hughesYoungFiniteArithmeticTerm T t c H h k p‖ := by
  rcases p with ⟨m, n⟩
  by_cases hm : m = 0
  · subst m
    simp only [hughesYoungFullDyadicArithmeticTerm,
      hughesYoungFiniteArithmeticTerm_eq_zero_of_left, mul_zero,
      norm_zero, tsum_zero]
  by_cases hn : n = 0
  · subst n
    simp only [hughesYoungFullDyadicArithmeticTerm,
      hughesYoungFiniteArithmeticTerm_eq_zero_of_right, mul_zero,
      norm_zero, tsum_zero]
  have hmPos : 0 < hughesYoungReducedLeft h k * m :=
    Nat.mul_pos (hughesYoungReducedLeft_pos (k := k) hh) (Nat.pos_of_ne_zero hm)
  have hnPos : 0 < hughesYoungReducedRight h k * n :=
    Nat.mul_pos (hughesYoungReducedRight_pos hh hk) (Nat.pos_of_ne_zero hn)
  have hleft := tsum_hughesYoungFullDyadicCutoff_nat_eq_one hmPos
  have hright := tsum_hughesYoungFullDyadicCutoff_nat_eq_one hnPos
  unfold hughesYoungFullDyadicArithmeticTerm
  simp only [norm_mul, Complex.norm_real]
  simp_rw [Real.norm_eq_abs, abs_of_nonneg
    (hughesYoungFullDyadicCutoff_nonneg_nat _ _)]
  simp_rw [tsum_mul_right, tsum_mul_left]
  rw [tsum_mul_right, hleft, hright]
  ring

theorem summable_norm_hughesYoungFullDyadicArithmeticTerm
    (T t c H : ℝ) (h k : ℕ) (p : ℕ × ℕ) :
    Summable (fun ij : ℕ × ℕ =>
      ‖hughesYoungFullDyadicArithmeticTerm T t c H h k ij.1 ij.2 p‖) := by
  apply (summable_prod_of_nonneg (fun _ => norm_nonneg _)).2
  constructor
  · intro i
    apply summable_of_hasFiniteSupport
    apply (finite_support_hughesYoungFullDyadicCutoff_nat
      (hughesYoungReducedRight h k * p.2)).subset
    intro j hj
    by_contra hcut
    have hcutEq : hughesYoungFullDyadicCutoff j
        ((hughesYoungReducedRight h k * p.2 : ℕ) : ℝ) = 0 := by
      simpa only [Function.mem_support, not_ne_iff] using hcut
    exact hj (by
      unfold hughesYoungFullDyadicArithmeticTerm
      dsimp only
      rw [hcutEq]
      simp)
  · apply summable_of_hasFiniteSupport
    apply (finite_support_hughesYoungFullDyadicCutoff_nat
      (hughesYoungReducedLeft h k * p.1)).subset
    intro i hi
    by_contra hcut
    have hcutEq : hughesYoungFullDyadicCutoff i
        ((hughesYoungReducedLeft h k * p.1 : ℕ) : ℝ) = 0 := by
      simpa only [Function.mem_support, not_ne_iff] using hcut
    exact hi (by
      unfold hughesYoungFullDyadicArithmeticTerm
      dsimp only
      rw [hcutEq]
      simp)

theorem summable_hughesYoungFullDyadicArithmeticTerm
    (T t c H : ℝ) (h k : ℕ) (p : ℕ × ℕ) :
    Summable (fun ij : ℕ × ℕ =>
      hughesYoungFullDyadicArithmeticTerm T t c H h k ij.1 ij.2 p) :=
  summable_norm_iff.mp
    (summable_norm_hughesYoungFullDyadicArithmeticTerm T t c H h k p)

/-- Absolute summability of the full pair-by-box family.  This is the exact
Tonelli condition required before changing Hughes--Young's AFE pair order
into the dyadic-box order used by DFI. -/
theorem summable_hughesYoungPairDyadicFamily
    (T t H : ℝ) {c : ℝ} (hc : 1 / 2 < c)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) :
    Summable (fun z : (ℕ × ℕ) × (ℕ × ℕ) =>
      hughesYoungFullDyadicArithmeticTerm T t c H h k
        z.2.1 z.2.2 z.1) := by
  have hsource := summable_hughesYoungFiniteArithmeticTerm T t H hc h k
  have hnorm : Summable (fun z : (ℕ × ℕ) × (ℕ × ℕ) =>
      ‖hughesYoungFullDyadicArithmeticTerm T t c H h k
        z.2.1 z.2.2 z.1‖) := by
    apply (summable_prod_of_nonneg (fun _ => norm_nonneg _)).2
    constructor
    · intro p
      exact summable_norm_hughesYoungFullDyadicArithmeticTerm
        T t c H h k p
    · apply hsource.norm.congr
      intro p
      have hpairs := summable_norm_hughesYoungFullDyadicArithmeticTerm
        T t c H h k p
      calc
        ‖hughesYoungFiniteArithmeticTerm T t c H h k p‖ =
          ∑' i : ℕ, ∑' j : ℕ,
            ‖hughesYoungFullDyadicArithmeticTerm T t c H h k i j p‖ :=
          (tsum_norm_hughesYoungFullDyadicArithmeticTerm_eq
            T t c H hh hk p).symm
        _ = ∑' ij : ℕ × ℕ,
            ‖hughesYoungFullDyadicArithmeticTerm T t c H h k
              ij.1 ij.2 p‖ := hpairs.tsum_prod.symm
  exact summable_norm_iff.mp hnorm

/-- Exact Hughes--Young equation-(69) decomposition of the actual opened
AFE series.  The equality includes the legal Tonelli interchange: DFI may
therefore be applied box by box without a sharp terminal rectangle. -/
theorem tsum_hughesYoungFiniteArithmeticTerm_eq_dyadicBoxes
    (T t H : ℝ) {c : ℝ} (hc : 1 / 2 < c)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) :
    (∑' p : ℕ × ℕ, hughesYoungFiniteArithmeticTerm T t c H h k p) =
      ∑' i : ℕ, ∑' j : ℕ, ∑' p : ℕ × ℕ,
        hughesYoungFullDyadicArithmeticTerm T t c H h k i j p := by
  let F : (ℕ × ℕ) → (ℕ × ℕ) → ℂ := fun p ij =>
    hughesYoungFullDyadicArithmeticTerm T t c H h k ij.1 ij.2 p
  have hF : Summable (Function.uncurry F) := by
    simpa only [F, Function.uncurry_apply_pair] using
      summable_hughesYoungPairDyadicFamily T t H hc hh hk
  calc
    (∑' p : ℕ × ℕ, hughesYoungFiniteArithmeticTerm T t c H h k p) =
        ∑' p : ℕ × ℕ, ∑' ij : ℕ × ℕ, F p ij := by
      apply tsum_congr
      intro p
      have hpairs := summable_hughesYoungFullDyadicArithmeticTerm
        T t c H h k p
      rw [hpairs.tsum_prod]
      exact (tsum_hughesYoungFullDyadicArithmeticTerm_eq
        T t c H hh hk p).symm
    _ = ∑' ij : ℕ × ℕ, ∑' p : ℕ × ℕ, F p ij :=
      hF.tsum_comm.symm
    _ = ∑' i : ℕ, ∑' j : ℕ, ∑' p : ℕ × ℕ,
        hughesYoungFullDyadicArithmeticTerm T t c H h k i j p := by
      have hboxes : Summable (fun ij : ℕ × ℕ =>
          ∑' p : ℕ × ℕ, F p ij) := hF.prod_symm.prod
      rw [hboxes.tsum_prod]

end RiemannZeta.GuthMaynard
