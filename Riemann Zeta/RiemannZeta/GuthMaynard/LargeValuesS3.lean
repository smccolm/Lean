import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import RiemannZeta.GuthMaynard.LargeValuesS2

open Complex Finset MeasureTheory Real Set
open scoped BigOperators

namespace RiemannZeta.GuthMaynard

/-!
# Guth--Maynard Sections 7--10: the three-frequency term

This module starts from the literal `gmCubicS3` in the cubic Poisson trace.
The first layer records the exact finite exponential-sum algebra needed in
Sections 7, 8, and 11.  The later layers localize the three nonzero Fourier
frequencies and assemble Guth--Maynard Propositions 7.1, 7.2, 8.1, 9.1,
and 10.1.
-/

/-- The additive-coordinate form of the source exponential sum. -/
noncomputable def gmRPhase (W : Finset ℝ) (x : ℝ) : ℂ :=
  ∑ t ∈ W, Complex.exp (((t * x : ℝ) : ℂ) * I)

theorem gmR_eq_gmRPhase_log {W : Finset ℝ} {v : ℝ} (hv : v ≠ 0) :
    gmR W v = gmRPhase W (Real.log |v|) := by
  unfold gmR gmRPhase
  apply Finset.sum_congr rfl
  intro t ht
  have hvabs : 0 < |v| := abs_pos.mpr hv
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hvabs.ne')]
  rw [← Complex.ofReal_log hvabs.le]
  congr 1
  push_cast
  ring

theorem gmRPhase_neg (W : Finset ℝ) (x : ℝ) :
    gmRPhase W (-x) = star (gmRPhase W x) := by
  unfold gmRPhase
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro t ht
  let z : ℂ := (((t * x : ℝ) : ℂ) * I)
  calc
    Complex.exp (((t * -x : ℝ) : ℂ) * I) =
        Complex.exp (star z) := by
      congr 1
      dsimp only [z]
      push_cast
      rw [Complex.star_def, map_mul, map_mul, conj_ofReal, conj_I]
      have hxstar : (starRingEnd ℂ) (x : ℂ) = (x : ℂ) := by
        exact Complex.conj_ofReal x
      rw [hxstar]
      ring
    _ = star (Complex.exp z) := Complex.exp_conj z

theorem norm_gmRPhase_neg (W : Finset ℝ) (x : ℝ) :
    ‖gmRPhase W (-x)‖ = ‖gmRPhase W x‖ := by
  rw [gmRPhase_neg, norm_star]

theorem norm_gmRPhase_le_card (W : Finset ℝ) (x : ℝ) :
    ‖gmRPhase W x‖ ≤ W.card := by
  unfold gmRPhase
  calc
    ‖∑ t ∈ W, Complex.exp (((t * x : ℝ) : ℂ) * I)‖ ≤
        ∑ t ∈ W, ‖Complex.exp (((t * x : ℝ) : ℂ) * I)‖ :=
      norm_sum_le _ _
    _ = ∑ _t ∈ W, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [Complex.norm_exp]
      simp
    _ = W.card := by simp

theorem continuous_gmRPhase (W : Finset ℝ) :
    Continuous (gmRPhase W) := by
  unfold gmRPhase
  fun_prop

theorem continuous_norm_gmRPhase_pow (W : Finset ℝ) (k : ℕ) :
    Continuous (fun x : ℝ => ‖gmRPhase W x‖ ^ k) :=
  (continuous_gmRPhase W).norm.pow k

/-- The exact ordered-pair expansion of the second moment. -/
theorem norm_gmRPhase_sq_expand (W : Finset ℝ) (x : ℝ) :
    ((‖gmRPhase W x‖ ^ 2 : ℝ) : ℂ) =
      ∑ t ∈ W, ∑ u ∈ W,
        Complex.exp ((((t - u) * x : ℝ) : ℂ) * I) := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
  unfold gmRPhase
  simp only [map_sum, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  apply Finset.sum_congr rfl
  intro u hu
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, conj_ofReal, conj_I]
  push_cast
  ring

/-- The exact ordered-quadruple expansion of the fourth moment. -/
theorem norm_gmRPhase_fourth_expand (W : Finset ℝ) (x : ℝ) :
    ((‖gmRPhase W x‖ ^ 4 : ℝ) : ℂ) =
      ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W, ∑ t₄ ∈ W,
        Complex.exp ((((t₁ + t₂ - t₃ - t₄) * x : ℝ) : ℂ) * I) := by
  calc
    ((‖gmRPhase W x‖ ^ 4 : ℝ) : ℂ) =
        ((‖gmRPhase W x‖ ^ 2 : ℝ) : ℂ) *
          ((‖gmRPhase W x‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      ring
    _ =
        (∑ t₁ ∈ W, ∑ t₃ ∈ W,
          Complex.exp ((((t₁ - t₃) * x : ℝ) : ℂ) * I)) *
        (∑ t₂ ∈ W, ∑ t₄ ∈ W,
          Complex.exp ((((t₂ - t₄) * x : ℝ) : ℂ) * I)) := by
      exact congrArg₂ (fun z w : ℂ => z * w)
        (norm_gmRPhase_sq_expand W x) (norm_gmRPhase_sq_expand W x)
    _ = _ := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t₁ ht₁
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t₂ ht₂
      apply Finset.sum_congr rfl
      intro t₃ ht₃
      apply Finset.sum_congr rfl
      intro t₄ ht₄
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring

/-- The elementary oscillatory kernel on a finite additive interval. -/
noncomputable def gmPhaseIntervalKernel (a b xi : ℝ) : ℂ :=
  ∫ x in a..b, Complex.exp ((((xi * x : ℝ) : ℂ) * I))

theorem gmPhaseIntervalKernel_zero (a b : ℝ) :
    gmPhaseIntervalKernel a b 0 = (b - a : ℝ) := by
  simp [gmPhaseIntervalKernel]

theorem gmPhaseIntervalKernel_eq {a b xi : ℝ} (hxi : xi ≠ 0) :
    gmPhaseIntervalKernel a b xi =
      (Complex.exp (((xi * b : ℝ) : ℂ) * I) -
          Complex.exp (((xi * a : ℝ) : ℂ) * I)) /
        (((xi : ℝ) : ℂ) * I) := by
  unfold gmPhaseIntervalKernel
  have hc : (((xi : ℝ) : ℂ) * I) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hxi) I_ne_zero
  have hpoint : ∀ x : ℝ,
      Complex.exp ((((xi * x : ℝ) : ℂ) * I)) =
        Complex.exp (((xi : ℝ) : ℂ) * I * (x : ℂ)) := by
    intro x
    congr 1
    push_cast
    ring
  simp_rw [hpoint]
  exact integral_exp_mul_complex hc

theorem norm_gmPhaseIntervalKernel_le_two_div {a b xi : ℝ}
    (hxi : xi ≠ 0) :
    ‖gmPhaseIntervalKernel a b xi‖ ≤ 2 / |xi| := by
  rw [gmPhaseIntervalKernel_eq hxi, norm_div]
  have hnum :
      ‖Complex.exp (((xi * b : ℝ) : ℂ) * I) -
          Complex.exp (((xi * a : ℝ) : ℂ) * I)‖ ≤ 2 := by
    calc
      _ ≤ ‖Complex.exp (((xi * b : ℝ) : ℂ) * I)‖ +
          ‖Complex.exp (((xi * a : ℝ) : ℂ) * I)‖ := norm_sub_le _ _
      _ = 2 := by norm_num [Complex.norm_exp]
  have hden : ‖((xi : ℂ) * I)‖ = |xi| := by
    simp [Real.norm_eq_abs]
  rw [hden]
  exact div_le_div_of_nonneg_right hnum (abs_nonneg xi)

/-- Exact integrated second-moment expansion on an arbitrary finite
additive interval. -/
theorem ofReal_intervalIntegral_norm_gmRPhase_sq (W : Finset ℝ) (a b : ℝ) :
    (((∫ x in a..b, ‖gmRPhase W x‖ ^ 2) : ℝ) : ℂ) =
      ∑ t ∈ W, ∑ u ∈ W, gmPhaseIntervalKernel a b (t - u) := by
  rw [← intervalIntegral.integral_ofReal]
  simp_rw [norm_gmRPhase_sq_expand]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro t ht
    rw [intervalIntegral.integral_finsetSum]
    · rfl
    · intro u hu
      apply Continuous.intervalIntegrable
      fun_prop
  · intro t ht
    apply Continuous.intervalIntegrable
    fun_prop

/-- Exact integrated fourth-moment expansion on an arbitrary finite
additive interval. -/
theorem ofReal_intervalIntegral_norm_gmRPhase_fourth
    (W : Finset ℝ) (a b : ℝ) :
    (((∫ x in a..b, ‖gmRPhase W x‖ ^ 4) : ℝ) : ℂ) =
      ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W, ∑ t₄ ∈ W,
        gmPhaseIntervalKernel a b (t₁ + t₂ - t₃ - t₄) := by
  rw [← intervalIntegral.integral_ofReal]
  simp_rw [norm_gmRPhase_fourth_expand]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro t₁ ht₁
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro t₂ ht₂
      rw [intervalIntegral.integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro t₃ ht₃
        rw [intervalIntegral.integral_finsetSum]
        · rfl
        · intro t₄ ht₄
          apply Continuous.intervalIntegrable
          fun_prop
      · intro t₃ ht₃
        apply Continuous.intervalIntegrable
        fun_prop
    · intro t₂ ht₂
      apply Continuous.intervalIntegrable
      fun_prop
  · intro t₁ ht₁
    apply Continuous.intervalIntegrable
    fun_prop

/-- Ordered pairs of source ordinates. -/
noncomputable def gmOrdinatePairs (W : Finset ℝ) : Finset (ℝ × ℝ) :=
  W ×ˢ W

/-- The unit-bin label of an ordered pair sum. -/
noncomputable def gmPairSumFloor (p : ℝ × ℝ) : ℤ :=
  ⌊p.1 + p.2⌋

/-- The finite support of the pair-sum floor multiplicity function. -/
noncomputable def gmPairSumFloorSupport (W : Finset ℝ) : Finset ℤ :=
  (gmOrdinatePairs W).image gmPairSumFloor

/-- Number of ordered pairs whose sum lies in one unit floor bin. -/
noncomputable def gmPairSumFloorCount (W : Finset ℝ) (j : ℤ) : ℕ :=
  ((gmOrdinatePairs W).filter fun p => gmPairSumFloor p = j).card

/-- Pair-pairs lying in the same unit floor bin. -/
noncomputable def gmFloorMatchedPairSums (W : Finset ℝ) :
    Finset ((ℝ × ℝ) × (ℝ × ℝ)) :=
  ((gmOrdinatePairs W) ×ˢ (gmOrdinatePairs W)).filter fun q =>
    gmPairSumFloor q.1 = gmPairSumFloor q.2

/-- The exact floor-bin square sum is the cardinality of the matched
pair-pair set. -/
theorem sum_pairSumFloorCount_sq (W : Finset ℝ) :
    ∑ j ∈ gmPairSumFloorSupport W, gmPairSumFloorCount W j ^ 2 =
      (gmFloorMatchedPairSums W).card := by
  classical
  unfold gmPairSumFloorSupport gmPairSumFloorCount gmFloorMatchedPairSums
  simp_rw [pow_two, ← Finset.card_product]
  rw [← Finset.card_biUnion]
  · congr 1
    ext q
    simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_product,
      Finset.mem_filter]
    constructor
    · rintro ⟨j, ⟨p, hp, rfl⟩, hq⟩
      exact ⟨⟨hq.1.1, hq.2.1⟩, hq.1.2.trans hq.2.2.symm⟩
    · intro hq
      refine ⟨gmPairSumFloor q.1, ⟨q.1, hq.1.1, rfl⟩, ?_⟩
      exact ⟨⟨hq.1.1, rfl⟩, ⟨hq.1.2, hq.2.symm⟩⟩
  · intro i hi j hj hij
    change Disjoint
      (((gmOrdinatePairs W).filter fun p => gmPairSumFloor p = i) ×ˢ
        ((gmOrdinatePairs W).filter fun p => gmPairSumFloor p = i))
      (((gmOrdinatePairs W).filter fun p => gmPairSumFloor p = j) ×ˢ
        ((gmOrdinatePairs W).filter fun p => gmPairSumFloor p = j))
    rw [Finset.disjoint_left]
    intro q hqi hqj
    have hiq := Finset.mem_filter.mp (Finset.mem_product.mp hqi).1 |>.2
    have hjq := Finset.mem_filter.mp (Finset.mem_product.mp hqj).1 |>.2
    exact hij (hiq.symm.trans hjq)

/-- Equal pair-sum floors force additive defect strictly below one. -/
theorem abs_pairSum_defect_lt_one_of_floor_eq
    {p q : ℝ × ℝ} (h : gmPairSumFloor p = gmPairSumFloor q) :
    |p.1 + p.2 - q.1 - q.2| < 1 := by
  unfold gmPairSumFloor at h
  have hpLower := Int.floor_le (p.1 + p.2)
  have hpUpper := Int.lt_floor_add_one (p.1 + p.2)
  have hqLower := Int.floor_le (q.1 + q.2)
  have hqUpper := Int.lt_floor_add_one (q.1 + q.2)
  rw [h] at hpLower hpUpper
  rw [abs_lt]
  constructor <;> linarith

/-- The floor-bin square sum is bounded by the source tolerance-one
approximate additive energy. -/
theorem pairSumFloor_energy_le (W : Finset ℝ) :
    ∑ j ∈ gmPairSumFloorSupport W, gmPairSumFloorCount W j ^ 2 ≤
      ApproxAddEnergy 1 W := by
  rw [sum_pairSumFloorCount_sq]
  unfold gmFloorMatchedPairSums ApproxAddEnergy
  apply Finset.card_le_card
  intro q hq
  simp only [Finset.mem_filter, Finset.mem_product, gmOrdinatePairs,
    approximateAdditiveQuadruples] at hq ⊢
  exact ⟨hq.1, (abs_pairSum_defect_lt_one_of_floor_eq hq.2).le⟩

/-- Outside its image support, the pair-sum multiplicity vanishes. -/
theorem gmPairSumFloorCount_eq_zero_of_not_mem_support
    {W : Finset ℝ} {j : ℤ} (hj : j ∉ gmPairSumFloorSupport W) :
    gmPairSumFloorCount W j = 0 := by
  unfold gmPairSumFloorCount
  rw [Finset.card_eq_zero]
  rw [Finset.filter_eq_empty_iff]
  intro p hp hfloor
  apply hj
  exact Finset.mem_image.mpr ⟨p, hp, hfloor⟩

/-- A finite set containing the supports of both factors in the floor-bin
correlation at displacement `k`. -/
noncomputable def gmPairSumFloorCorrelationSupport
    (W : Finset ℝ) (k : ℤ) : Finset ℤ :=
  gmPairSumFloorSupport W ∪
    (gmPairSumFloorSupport W).image (fun j => j - k)

theorem sum_pairSumFloorCount_sq_correlationSupport
    (W : Finset ℝ) (k : ℤ) :
    ∑ j ∈ gmPairSumFloorCorrelationSupport W k,
        gmPairSumFloorCount W j ^ 2 =
      ∑ j ∈ gmPairSumFloorSupport W,
        gmPairSumFloorCount W j ^ 2 := by
  classical
  symm
  apply Finset.sum_subset (Finset.subset_union_left)
  intro j hjUnion hjSupport
  rw [gmPairSumFloorCount_eq_zero_of_not_mem_support hjSupport]
  simp

theorem sum_shifted_pairSumFloorCount_sq_correlationSupport
    (W : Finset ℝ) (k : ℤ) :
    ∑ j ∈ gmPairSumFloorCorrelationSupport W k,
        gmPairSumFloorCount W (j + k) ^ 2 =
      ∑ j ∈ gmPairSumFloorSupport W,
        gmPairSumFloorCount W j ^ 2 := by
  classical
  let S := gmPairSumFloorSupport W
  have himage :
      ∑ j ∈ S.image (fun j => j - k),
          gmPairSumFloorCount W (j + k) ^ 2 =
        ∑ j ∈ S, gmPairSumFloorCount W j ^ 2 := by
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro j hj
      congr 2
      omega
    · intro i hi j hj hij
      exact sub_left_injective hij
  calc
    ∑ j ∈ gmPairSumFloorCorrelationSupport W k,
        gmPairSumFloorCount W (j + k) ^ 2 =
        ∑ j ∈ S.image (fun j => j - k),
          gmPairSumFloorCount W (j + k) ^ 2 := by
      symm
      apply Finset.sum_subset (Finset.subset_union_right)
      intro j hjUnion hjImage
      have hjNot : j + k ∉ S := by
        intro hmem
        apply hjImage
        exact Finset.mem_image.mpr ⟨j + k, hmem, by omega⟩
      rw [gmPairSumFloorCount_eq_zero_of_not_mem_support hjNot]
      simp
    _ = _ := himage

/-- The exact floor-bin correlation at displacement `k`. -/
noncomputable def gmPairSumFloorCorrelation
    (W : Finset ℝ) (k : ℤ) : ℕ :=
  ∑ j ∈ gmPairSumFloorCorrelationSupport W k,
    gmPairSumFloorCount W (j + k) * gmPairSumFloorCount W j

/-- Every displaced floor-bin correlation is controlled by the same
tolerance-one additive energy.  This is the discrete Cauchy--Schwarz step
in Guth--Maynard Lemma 8.3. -/
theorem gmPairSumFloorCorrelation_le_energy
    (W : Finset ℝ) (k : ℤ) :
    gmPairSumFloorCorrelation W k ≤ ApproxAddEnergy 1 W := by
  let S := gmPairSumFloorCorrelationSupport W k
  let E := ∑ j ∈ gmPairSumFloorSupport W,
    gmPairSumFloorCount W j ^ 2
  have hcs : (gmPairSumFloorCorrelation W k) ^ 2 ≤ E * E := by
    unfold gmPairSumFloorCorrelation
    simpa [S, E, sum_pairSumFloorCount_sq_correlationSupport,
      sum_shifted_pairSumFloorCount_sq_correlationSupport] using
      (sum_mul_sq_le_sq_mul_sq (R := ℕ) S
        (fun j => gmPairSumFloorCount W (j + k))
        (fun j => gmPairSumFloorCount W j))
  have hcorrE : gmPairSumFloorCorrelation W k ≤ E := by
    nlinarith [Nat.zero_le (gmPairSumFloorCorrelation W k), Nat.zero_le E]
  exact hcorrE.trans (pairSumFloor_energy_le W)

end RiemannZeta.GuthMaynard
