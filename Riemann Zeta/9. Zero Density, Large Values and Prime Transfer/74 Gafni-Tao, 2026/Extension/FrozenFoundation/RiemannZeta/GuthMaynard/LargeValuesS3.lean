import Mathlib.Algebra.BigOperators.Group.Finset.Interval
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.NumberTheory.Harmonic.Bounds
import RiemannZeta.GuthMaynard.DFIDivisorEpsilon
import RiemannZeta.GuthMaynard.DFISourceCutoffs
import RiemannZeta.GuthMaynard.LargeValuesS2

open Complex Finset MeasureTheory Real Set
open scoped BigOperators ContDiff FourierTransform SchwartzMap

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

/-- Integer displacement between the unit bins of two ordered pair sums. -/
noncomputable def gmPairSumFloorDefect
    (q : (ℝ × ℝ) × (ℝ × ℝ)) : ℤ :=
  gmPairSumFloor q.1 - gmPairSumFloor q.2

/-- The finite support of pair-sum floor displacements. -/
noncomputable def gmPairSumFloorDefectSupport (W : Finset ℝ) : Finset ℤ :=
  ((gmOrdinatePairs W) ×ˢ (gmOrdinatePairs W)).image gmPairSumFloorDefect

/-- Number of ordered quadruples in one pair-sum floor-displacement bin. -/
noncomputable def gmPairSumFloorDefectCount
    (W : Finset ℝ) (k : ℤ) : ℕ :=
  (((gmOrdinatePairs W) ×ˢ (gmOrdinatePairs W)).filter fun q =>
    gmPairSumFloorDefect q = k).card

/-- The floor-displacement count is exactly the correlation of the two
pair-sum multiplicity sequences. -/
theorem gmPairSumFloorDefectCount_eq_correlation
    (W : Finset ℝ) (k : ℤ) :
    gmPairSumFloorDefectCount W k = gmPairSumFloorCorrelation W k := by
  classical
  let P := gmOrdinatePairs W
  let Q := (P ×ˢ P).filter fun q => gmPairSumFloorDefect q = k
  let S := gmPairSumFloorCorrelationSupport W k
  have hmaps : (Q : Set ((ℝ × ℝ) × (ℝ × ℝ))).MapsTo
      (fun q => gmPairSumFloor q.2) S := by
    intro q hq
    have hqFin : q ∈ Q := hq
    change q ∈ (P ×ˢ P).filter (fun q => gmPairSumFloorDefect q = k) at hqFin
    have hqmem : q.2 ∈ P :=
      (Finset.mem_product.mp (Finset.mem_filter.mp hqFin).1).2
    have hj : gmPairSumFloor q.2 ∈ gmPairSumFloorSupport W := by
      exact Finset.mem_image.mpr ⟨q.2, hqmem, rfl⟩
    exact Finset.mem_union_left _ hj
  have hfiber := Finset.card_eq_sum_card_fiberwise
    (s := Q) (t := S)
    (f := fun q : ((ℝ × ℝ) × (ℝ × ℝ)) => gmPairSumFloor q.2) hmaps
  change Q.card = ∑ b ∈ S,
    ((Q.filter fun a => gmPairSumFloor a.2 = b).card) at hfiber
  change Q.card = gmPairSumFloorCorrelation W k
  rw [hfiber]
  unfold gmPairSumFloorCorrelation
  apply Finset.sum_congr rfl
  intro j hj
  unfold gmPairSumFloorCount
  rw [← Finset.card_product]
  congr 1
  ext q
  simp only [Q, P, Finset.mem_filter, Finset.mem_product,
    gmPairSumFloorDefect]
  constructor
  · rintro ⟨⟨hqP, hdef⟩, hjq⟩
    have hfirst : gmPairSumFloor q.1 = j + k := by omega
    exact ⟨⟨hqP.1, hfirst⟩, hqP.2, hjq⟩
  · rintro ⟨⟨hq1, hfirst⟩, hq2, hsecond⟩
    exact ⟨⟨⟨hq1, hq2⟩, by omega⟩, hsecond⟩

theorem gmPairSumFloorDefectCount_le_energy
    (W : Finset ℝ) (k : ℤ) :
    gmPairSumFloorDefectCount W k ≤ ApproxAddEnergy 1 W := by
  rw [gmPairSumFloorDefectCount_eq_correlation]
  exact gmPairSumFloorCorrelation_le_energy W k

/-- A pair-sum floor displacement controls the real additive defect to
within one unit. -/
theorem abs_sub_pairSumFloorDefect_cast_lt_one
    (q : (ℝ × ℝ) × (ℝ × ℝ)) :
    |(q.1.1 + q.1.2 - q.2.1 - q.2.2) -
        (gmPairSumFloorDefect q : ℝ)| < 1 := by
  unfold gmPairSumFloorDefect gmPairSumFloor
  have h11 := Int.floor_le (q.1.1 + q.1.2)
  have h12 := Int.lt_floor_add_one (q.1.1 + q.1.2)
  have h21 := Int.floor_le (q.2.1 + q.2.2)
  have h22 := Int.lt_floor_add_one (q.2.1 + q.2.2)
  rw [abs_lt]
  constructor
  · push_cast
    linarith
  · push_cast
    linarith

theorem abs_additiveDefect_ge_intDefect_sub_one
    (q : (ℝ × ℝ) × (ℝ × ℝ)) :
    |(gmPairSumFloorDefect q : ℝ)| - 1 <
      |q.1.1 + q.1.2 - q.2.1 - q.2.2| := by
  have h := abs_sub_pairSumFloorDefect_cast_lt_one q
  calc
    |(gmPairSumFloorDefect q : ℝ)| - 1 <
        |(gmPairSumFloorDefect q : ℝ)| -
          |(q.1.1 + q.1.2 - q.2.1 - q.2.2) -
            (gmPairSumFloorDefect q : ℝ)| := by linarith
    _ ≤ |q.1.1 + q.1.2 - q.2.1 - q.2.2| := by
      have htri : |(gmPairSumFloorDefect q : ℝ)| ≤
          |q.1.1 + q.1.2 - q.2.1 - q.2.2| +
            |(q.1.1 + q.1.2 - q.2.1 - q.2.2) -
              (gmPairSumFloorDefect q : ℝ)| := by
        let x : ℝ := q.1.1 + q.1.2 - q.2.1 - q.2.2
        let d : ℝ := gmPairSumFloorDefect q
        have hlocal : |d| ≤ |x| + |x - d| := by
          calc
            |d| = |x + (d - x)| := by congr 1; ring
            _ ≤ |x| + |d - x| := abs_add_le _ _
            _ = |x| + |x - d| := by rw [abs_sub_comm d x]
        simpa [x, d] using hlocal
      linarith

theorem norm_gmPhaseIntervalKernel_le_length (a b xi : ℝ) :
    ‖gmPhaseIntervalKernel a b xi‖ ≤ |b - a| := by
  unfold gmPhaseIntervalKernel
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun x : ℝ => Complex.exp ((((xi * x : ℝ) : ℂ) * I)))
    (C := 1) (a := a) (b := b) (by
      intro x hx
      rw [Complex.norm_exp]
      simp)
  simpa using h

/-- Majorant for an interval kernel in one integer pair-sum displacement
bin.  The three central bins use the interval length; the remaining bins
use one integration by parts. -/
noncomputable def gmPhaseFloorDefectWeight (a b : ℝ) (k : ℤ) : ℝ :=
  if |(k : ℝ)| ≤ 1 then |b - a| else 2 / (|(k : ℝ)| - 1)

theorem gmPhaseFloorDefectWeight_nonneg (a b : ℝ) (k : ℤ) :
    0 ≤ gmPhaseFloorDefectWeight a b k := by
  unfold gmPhaseFloorDefectWeight
  split_ifs with hk
  · exact abs_nonneg _
  · exact div_nonneg (by norm_num) (sub_nonneg.mpr (le_of_not_ge hk))

/-- Pointwise interval-kernel bound by the weight of the quadruple's
integer displacement bin. -/
theorem norm_gmPhaseIntervalKernel_le_floorDefectWeight
    (a b : ℝ) (q : (ℝ × ℝ) × (ℝ × ℝ)) :
    ‖gmPhaseIntervalKernel a b
        (q.1.1 + q.1.2 - q.2.1 - q.2.2)‖ ≤
      gmPhaseFloorDefectWeight a b (gmPairSumFloorDefect q) := by
  unfold gmPhaseFloorDefectWeight
  split_ifs with hk
  · exact norm_gmPhaseIntervalKernel_le_length _ _ _
  · have hdk : 1 < |(gmPairSumFloorDefect q : ℝ)| := lt_of_not_ge hk
    have hxiLower := abs_additiveDefect_ge_intDefect_sub_one q
    have hdenPos : 0 < |(gmPairSumFloorDefect q : ℝ)| - 1 := by linarith
    have hxiPos : 0 < |q.1.1 + q.1.2 - q.2.1 - q.2.2| :=
      hdenPos.trans hxiLower
    have hxi : q.1.1 + q.1.2 - q.2.1 - q.2.2 ≠ 0 :=
      abs_pos.mp hxiPos
    exact (norm_gmPhaseIntervalKernel_le_two_div hxi).trans
      (div_le_div_of_nonneg_left (by norm_num) hdenPos hxiLower.le)

/-- The nested ordered-quadruple sum is the corresponding sum over the
pair-pair product. -/
theorem sum_gmPhaseIntervalKernel_eq_pairPairs
    (W : Finset ℝ) (a b : ℝ) :
    (∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W, ∑ t₄ ∈ W,
        gmPhaseIntervalKernel a b (t₁ + t₂ - t₃ - t₄)) =
      ∑ q ∈ (gmOrdinatePairs W) ×ˢ (gmOrdinatePairs W),
        gmPhaseIntervalKernel a b
          (q.1.1 + q.1.2 - q.2.1 - q.2.2) := by
  simp only [gmOrdinatePairs, Finset.sum_product]

/-- Summing a function of the floor displacement can be done fiberwise
over the finite displacement support. -/
theorem sum_pairPairs_comp_floorDefect
    (W : Finset ℝ) (F : ℤ → ℝ) :
    (∑ q ∈ (gmOrdinatePairs W) ×ˢ (gmOrdinatePairs W),
        F (gmPairSumFloorDefect q)) =
      ∑ k ∈ gmPairSumFloorDefectSupport W,
        gmPairSumFloorDefectCount W k * F k := by
  classical
  let Q := (gmOrdinatePairs W) ×ˢ (gmOrdinatePairs W)
  have hmaps : (Q : Set ((ℝ × ℝ) × (ℝ × ℝ))).MapsTo
      gmPairSumFloorDefect (gmPairSumFloorDefectSupport W) := by
    intro q hq
    exact Finset.mem_image.mpr ⟨q, hq, rfl⟩
  change (∑ q ∈ Q, F (gmPairSumFloorDefect q)) = _
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (fun q => F (gmPairSumFloorDefect q))]
  apply Finset.sum_congr rfl
  intro k hk
  calc
    (∑ q ∈ Q with gmPairSumFloorDefect q = k,
        F (gmPairSumFloorDefect q)) =
        ∑ _q ∈ Q with gmPairSumFloorDefect _q = k, F k := by
      apply Finset.sum_congr rfl
      intro q hq
      exact congrArg F (Finset.mem_filter.mp hq).2
    _ = ((Q.filter fun q => gmPairSumFloorDefect q = k).card : ℝ) * F k := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ = (gmPairSumFloorDefectCount W k : ℝ) * F k := rfl

/-- The total interval fourth moment is bounded by a sum of one energy
copy for each weighted floor-displacement bin. -/
theorem intervalIntegral_norm_gmRPhase_fourth_le_defectWeights
    (W : Finset ℝ) (a b : ℝ) (hab : a ≤ b) :
    (∫ x in a..b, ‖gmRPhase W x‖ ^ 4) ≤
      (ApproxAddEnergy 1 W : ℝ) *
        ∑ k ∈ gmPairSumFloorDefectSupport W,
          gmPhaseFloorDefectWeight a b k := by
  have hnonneg : 0 ≤ ∫ x in a..b, ‖gmRPhase W x‖ ^ 4 := by
    exact intervalIntegral.integral_nonneg hab (fun x hx => by positivity)
  have hexpand := ofReal_intervalIntegral_norm_gmRPhase_fourth W a b
  rw [sum_gmPhaseIntervalKernel_eq_pairPairs] at hexpand
  have hnorm : (∫ x in a..b, ‖gmRPhase W x‖ ^ 4) =
      ‖∑ q ∈ (gmOrdinatePairs W) ×ˢ (gmOrdinatePairs W),
        gmPhaseIntervalKernel a b
          (q.1.1 + q.1.2 - q.2.1 - q.2.2)‖ := by
    rw [← hexpand]
    simp [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  rw [hnorm]
  calc
    ‖∑ q ∈ (gmOrdinatePairs W) ×ˢ (gmOrdinatePairs W),
        gmPhaseIntervalKernel a b
          (q.1.1 + q.1.2 - q.2.1 - q.2.2)‖ ≤
        ∑ q ∈ (gmOrdinatePairs W) ×ˢ (gmOrdinatePairs W),
          ‖gmPhaseIntervalKernel a b
            (q.1.1 + q.1.2 - q.2.1 - q.2.2)‖ := norm_sum_le _ _
    _ ≤ ∑ q ∈ (gmOrdinatePairs W) ×ˢ (gmOrdinatePairs W),
          gmPhaseFloorDefectWeight a b (gmPairSumFloorDefect q) := by
      gcongr with q _hq
      exact norm_gmPhaseIntervalKernel_le_floorDefectWeight a b q
    _ = ∑ k ∈ gmPairSumFloorDefectSupport W,
          (gmPairSumFloorDefectCount W k : ℝ) *
            gmPhaseFloorDefectWeight a b k := by
      rw [sum_pairPairs_comp_floorDefect]
    _ ≤ ∑ k ∈ gmPairSumFloorDefectSupport W,
          (ApproxAddEnergy 1 W : ℝ) *
            gmPhaseFloorDefectWeight a b k := by
      gcongr with k hk
      · exact gmPhaseFloorDefectWeight_nonneg a b k
      · exact_mod_cast gmPairSumFloorDefectCount_le_energy W k
    _ = _ := by rw [Finset.mul_sum]

/-- A pair-sum floor lies between zero and the ceiling of twice the ambient
height. -/
theorem gmPairSumFloor_mem_Icc_of_inBaseInterval
    {T : ℝ} {W : Finset ℝ} (hW : InBaseInterval T W)
    {p : ℝ × ℝ} (hp : p ∈ gmOrdinatePairs W) :
    gmPairSumFloor p ∈ Finset.Icc (0 : ℤ) ⌈2 * T⌉ := by
  have hpW := Finset.mem_product.mp hp
  have hp1 := hW p.1 hpW.1
  have hp2 := hW p.2 hpW.2
  rw [Set.mem_Icc] at hp1 hp2
  rw [Finset.mem_Icc]
  constructor
  · unfold gmPairSumFloor
    exact Int.floor_nonneg.mpr (by linarith)
  · unfold gmPairSumFloor
    exact (Int.floor_le_floor (by linarith [hp1.2, hp2.2])).trans
      (Int.floor_le_ceil (2 * T))

/-- Every displacement occurring for ordinates in `[0,T]` is in the
symmetric integer interval of radius `ceil (2T)`. -/
theorem gmPairSumFloorDefectSupport_subset_Icc
    {T : ℝ} {W : Finset ℝ} (hW : InBaseInterval T W) :
    gmPairSumFloorDefectSupport W ⊆
      Finset.Icc (-⌈2 * T⌉) ⌈2 * T⌉ := by
  intro k hk
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hk
  have hqP := Finset.mem_product.mp hq
  have h1 := gmPairSumFloor_mem_Icc_of_inBaseInterval hW hqP.1
  have h2 := gmPairSumFloor_mem_Icc_of_inBaseInterval hW hqP.2
  rw [Finset.mem_Icc] at h1 h2 ⊢
  unfold gmPairSumFloorDefect
  constructor <;> omega

theorem gmPhaseFloorDefectWeight_neg (a b : ℝ) (k : ℤ) :
    gmPhaseFloorDefectWeight a b (-k) =
      gmPhaseFloorDefectWeight a b k := by
  simp [gmPhaseFloorDefectWeight]

theorem gmPhaseFloorDefectWeight_natCast_zero (a b : ℝ) :
    gmPhaseFloorDefectWeight a b (0 : ℤ) = |b - a| := by
  simp [gmPhaseFloorDefectWeight]

theorem gmPhaseFloorDefectWeight_natCast_one (a b : ℝ) :
    gmPhaseFloorDefectWeight a b (1 : ℤ) = |b - a| := by
  simp [gmPhaseFloorDefectWeight]

theorem gmPhaseFloorDefectWeight_natCast_of_two_le
    (a b : ℝ) {n : ℕ} (hn : 2 ≤ n) :
    gmPhaseFloorDefectWeight a b (n : ℤ) = 2 / ((n : ℝ) - 1) := by
  unfold gmPhaseFloorDefectWeight
  have hnReal : 1 < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  rw [if_neg (not_le.mpr (by simpa using hnReal))]
  simp [abs_of_nonneg (by positivity : (0 : ℝ) ≤ n)]

/-- One-sided weighted displacement mass.  The deliberately loose factor
four makes the induction uniform at the first noncentral bin. -/
theorem sum_range_gmPhaseFloorDefectWeight_le
    (a b : ℝ) (K : ℕ) :
    (∑ n ∈ Finset.range (K + 1),
        gmPhaseFloorDefectWeight a b (n : ℤ)) ≤
      2 * |b - a| +
        4 * (((harmonic K : ℚ) : ℝ)) := by
  induction K with
  | zero =>
      simp only [Nat.zero_add, Finset.sum_range_one, Nat.cast_zero,
        gmPhaseFloorDefectWeight_natCast_zero,
        harmonic_zero, Rat.cast_zero, mul_zero, add_zero]
      linarith [abs_nonneg (b - a)]
  | succ K ih =>
      by_cases hK : K = 0
      · subst K
        norm_num only [Nat.zero_add]
        rw [Finset.sum_range_succ, Finset.sum_range_succ,
          Finset.sum_range_zero, zero_add]
        change gmPhaseFloorDefectWeight a b (0 : ℤ) +
            gmPhaseFloorDefectWeight a b (1 : ℤ) ≤
          2 * |b - a| + 4 * (((harmonic 1 : ℚ) : ℝ))
        rw [gmPhaseFloorDefectWeight_natCast_zero,
          gmPhaseFloorDefectWeight_natCast_one]
        norm_num [harmonic_succ, harmonic_zero]
        linarith [abs_nonneg (b - a)]
      · have hKpos : 0 < K := Nat.pos_of_ne_zero hK
        have hKone : 1 ≤ K := hKpos
        have hweight :
            gmPhaseFloorDefectWeight a b ((K + 1 : ℕ) : ℤ) =
              2 / (K : ℝ) := by
          rw [gmPhaseFloorDefectWeight_natCast_of_two_le a b (by omega)]
          norm_num
        have hfrac : 2 / (K : ℝ) ≤ 4 / (K + 1 : ℝ) := by
          rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < K)
            (by positivity : (0 : ℝ) < K + 1)]
          exact_mod_cast (show 2 * (K + 1) ≤ 4 * K by omega)
        have hH : (((harmonic (K + 1) : ℚ) : ℝ)) =
            ((harmonic K : ℚ) : ℝ) + 1 / (K + 1 : ℝ) := by
          rw [harmonic_succ]
          push_cast
          norm_num
        rw [Finset.sum_range_succ, hweight, hH]
        calc
          (∑ n ∈ Finset.range (K + 1),
              gmPhaseFloorDefectWeight a b (n : ℤ)) + 2 / (K : ℝ) ≤
              (2 * |b - a| + 4 * ((harmonic K : ℚ) : ℝ)) +
                2 / (K : ℝ) := by linarith
          _ ≤ 2 * |b - a| + 4 *
                (((harmonic K : ℚ) : ℝ) + 1 / (K + 1 : ℝ)) := by
            calc
              (2 * |b - a| + 4 * ((harmonic K : ℚ) : ℝ)) +
                  2 / (K : ℝ) ≤
                (2 * |b - a| + 4 * ((harmonic K : ℚ) : ℝ)) +
                  4 / (K + 1 : ℝ) := by
                    simpa [add_comm, add_left_comm, add_assoc] using
                      add_le_add_left hfrac
                        (2 * |b - a| + 4 * ((harmonic K : ℚ) : ℝ))
              _ = _ := by ring

/-- Symmetric weighted displacement mass has only a harmonic loss. -/
theorem sum_Icc_gmPhaseFloorDefectWeight_le
    (a b : ℝ) (K : ℕ) :
    (∑ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
        gmPhaseFloorDefectWeight a b k) ≤
      4 * |b - a| + 8 * (((harmonic K : ℚ) : ℝ)) := by
  have heven : Function.Even (gmPhaseFloorDefectWeight a b) :=
    fun k => gmPhaseFloorDefectWeight_neg a b k
  rw [Finset.sum_Icc_of_even_eq_range heven K]
  simp only [nsmul_eq_mul]
  have hrange := sum_range_gmPhaseFloorDefectWeight_le a b K
  have hzero := gmPhaseFloorDefectWeight_nonneg a b 0
  change 2 * (∑ n ∈ Finset.range (K + 1),
      gmPhaseFloorDefectWeight a b (n : ℤ)) -
      gmPhaseFloorDefectWeight a b 0 ≤ _
  calc
    2 * (∑ n ∈ Finset.range (K + 1),
        gmPhaseFloorDefectWeight a b (n : ℤ)) -
        gmPhaseFloorDefectWeight a b 0 ≤
      2 * (∑ n ∈ Finset.range (K + 1),
        gmPhaseFloorDefectWeight a b (n : ℤ)) := sub_le_self _ hzero
    _ ≤ 2 * (2 * |b - a| + 4 * (((harmonic K : ℚ) : ℝ))) := by
      gcongr
    _ = _ := by ring

/-- Guth--Maynard Lemma 8.3 in additive coordinates, before the standard
harmonic-to-`T^epsilon` absorption. -/
theorem intervalIntegral_norm_gmRPhase_fourth_le_energy_harmonic
    {T : ℝ} {W : Finset ℝ} (hT : 0 ≤ T) (hW : InBaseInterval T W)
    (a b : ℝ) (hab : a ≤ b) :
    (∫ x in a..b, ‖gmRPhase W x‖ ^ 4) ≤
      (ApproxAddEnergy 1 W : ℝ) *
        (4 * |b - a| +
          8 * (((harmonic ⌈2 * T⌉₊ : ℚ) : ℝ))) := by
  have hceil : (0 : ℤ) ≤ ⌈2 * T⌉ := Int.ceil_nonneg (by positivity)
  have hceilCast : (⌈2 * T⌉₊ : ℤ) = ⌈2 * T⌉ := by
    exact Int.toNat_of_nonneg hceil
  calc
    (∫ x in a..b, ‖gmRPhase W x‖ ^ 4) ≤
        (ApproxAddEnergy 1 W : ℝ) *
          ∑ k ∈ gmPairSumFloorDefectSupport W,
            gmPhaseFloorDefectWeight a b k :=
      intervalIntegral_norm_gmRPhase_fourth_le_defectWeights W a b hab
    _ ≤ (ApproxAddEnergy 1 W : ℝ) *
          ∑ k ∈ Finset.Icc (-⌈2 * T⌉) ⌈2 * T⌉,
            gmPhaseFloorDefectWeight a b k := by
      gcongr
      intro k hk hnot
      exact gmPhaseFloorDefectWeight_nonneg a b k
      exact gmPairSumFloorDefectSupport_subset_Icc hW
    _ = (ApproxAddEnergy 1 W : ℝ) *
          ∑ k ∈ Finset.Icc (-(⌈2 * T⌉₊ : ℤ)) (⌈2 * T⌉₊ : ℤ),
            gmPhaseFloorDefectWeight a b k := by rw [hceilCast]
    _ ≤ _ := by
      gcongr
      exact sum_Icc_gmPhaseFloorDefectWeight_le a b ⌈2 * T⌉₊

/-- The harmonic loss at the physical displacement radius is absorbed by
an arbitrary positive power of the height. -/
theorem harmonic_ceil_two_mul_le_epsilon_rpow
    {ε T : ℝ} (hε : 0 < ε) (hT : 1 ≤ T) :
    (((harmonic ⌈2 * T⌉₊ : ℚ) : ℝ)) ≤
      (1 + ε⁻¹) * 3 ^ ε * T ^ ε := by
  let K := ⌈2 * T⌉₊
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hceilRaw : (K : ℝ) < 2 * T + 1 := by
    exact Nat.ceil_lt_add_one (by positivity : 0 ≤ 2 * T)
  have hKle : (K : ℝ) ≤ 3 * T := by linarith
  have hThreeT : (1 : ℝ) ≤ 3 * T := by nlinarith
  have hpowK : (K : ℝ) ^ ε ≤ (3 * T) ^ ε := by
    exact Real.rpow_le_rpow (by positivity) hKle hε.le
  have hpowOne : (1 : ℝ) ≤ (3 * T) ^ ε := by
    simpa using Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hThreeT hε.le
  have hmax : max 1 ((K : ℝ) ^ ε) ≤ (3 * T) ^ ε :=
    max_le hpowOne hpowK
  have hharm := harmonic_le_epsilon_rpow hε K
  calc
    (((harmonic K : ℚ) : ℝ)) ≤
        (1 + ε⁻¹) * max 1 ((K : ℝ) ^ ε) := hharm
    _ ≤ (1 + ε⁻¹) * (3 * T) ^ ε := by
      gcongr
    _ = (1 + ε⁻¹) * 3 ^ ε * T ^ ε := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) hTpos.le]
      ring

/-- Guth--Maynard Lemma 8.3 with its logarithm absorbed into `T^ε`.
The constant is explicit and depends only on `ε` and the fixed additive
integration interval. -/
theorem intervalIntegral_norm_gmRPhase_fourth_le_energy_epsilon
    {ε T : ℝ} {W : Finset ℝ} (hε : 0 < ε) (hT : 1 ≤ T)
    (hW : InBaseInterval T W) (a b : ℝ) (hab : a ≤ b) :
    (∫ x in a..b, ‖gmRPhase W x‖ ^ 4) ≤
      (4 * |b - a| + 8 * (1 + ε⁻¹) * 3 ^ ε) *
        T ^ ε * (ApproxAddEnergy 1 W : ℝ) := by
  have hraw := intervalIntegral_norm_gmRPhase_fourth_le_energy_harmonic
    (T := T) (W := W) (zero_le_one.trans hT) hW a b hab
  have hharm := harmonic_ceil_two_mul_le_epsilon_rpow hε hT
  have hTpow : (1 : ℝ) ≤ T ^ ε := by
    simpa using Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hT hε.le
  have hE : (0 : ℝ) ≤ ApproxAddEnergy 1 W := by positivity
  calc
    (∫ x in a..b, ‖gmRPhase W x‖ ^ 4) ≤
        (ApproxAddEnergy 1 W : ℝ) *
          (4 * |b - a| +
            8 * (((harmonic ⌈2 * T⌉₊ : ℚ) : ℝ))) := hraw
    _ ≤ (ApproxAddEnergy 1 W : ℝ) *
          (4 * |b - a| +
            8 * ((1 + ε⁻¹) * 3 ^ ε * T ^ ε)) := by
      gcongr
    _ ≤ (ApproxAddEnergy 1 W : ℝ) *
          ((4 * |b - a| + 8 * (1 + ε⁻¹) * 3 ^ ε) * T ^ ε) := by
      gcongr
      have hlen : 0 ≤ |b - a| := abs_nonneg _
      have haux : 4 * |b - a| ≤ 4 * |b - a| * T ^ ε := by
        nlinarith
      nlinarith
    _ = _ := by ring

/-! ## Exact three-frequency expansion of the source cubic term -/

/-- The nonzero part of one scaled Poisson mode.  Keeping the zero-frequency
exclusion in the summand makes the later triple series literally equal to
`gmCubicS3`, rather than a truncated surrogate. -/
noncomputable def gmNonzeroScaledTraceMode (cutoff : GMSmoothCutoff) (N : ℕ)
    (t : ℝ) (m : ℤ) : ℂ :=
  if m = 0 then 0 else gmScaledTraceMode cutoff N t m

theorem gmNonzeroScaledTraceMode_summable (cutoff : GMSmoothCutoff)
    (N : ℕ) (hN : 0 < N) (t : ℝ) :
    Summable (gmNonzeroScaledTraceMode cutoff N t) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le
      (fun m => norm_nonneg (gmNonzeroScaledTraceMode cutoff N t m))
      (fun m => ?_) (gmScaledTraceMode_summable cutoff N hN t).norm
  by_cases hm : m = 0
  · simp [gmNonzeroScaledTraceMode, hm]
  · simp [gmNonzeroScaledTraceMode, hm]

theorem gmTraceNonzeroTailAt_eq_tsum_nonzeroScaledTraceMode
    (cutoff : GMSmoothCutoff) (N : ℕ) (t : ℝ) :
    gmTraceNonzeroTailAt cutoff N t =
      ∑' m : ℤ, gmNonzeroScaledTraceMode cutoff N t m := by
  rfl

/-- The literal summand of the three-frequency series in Section 7. -/
noncomputable def gmCubicS3Mode (cutoff : GMSmoothCutoff) (N : ℕ)
    (W : Finset ℝ) (m : ℤ × (ℤ × ℤ)) : ℂ :=
  ∑ t : GMRow W, ∑ u : GMRow W, ∑ v : GMRow W,
    gmNonzeroScaledTraceMode cutoff N ((t : ℝ) - (u : ℝ)) m.1 *
      gmNonzeroScaledTraceMode cutoff N ((u : ℝ) - (v : ℝ)) m.2.1 *
        gmNonzeroScaledTraceMode cutoff N ((v : ℝ) - (t : ℝ)) m.2.2

theorem summable_norm_gmNonzeroScaledTraceMode (cutoff : GMSmoothCutoff)
    (N : ℕ) (hN : 0 < N) (t : ℝ) :
    Summable (fun m : ℤ => ‖gmNonzeroScaledTraceMode cutoff N t m‖) :=
  (gmNonzeroScaledTraceMode_summable cutoff N hN t).norm

theorem gmTraceNonzeroTailAt_mul_mul_eq_tsum_modes
    (cutoff : GMSmoothCutoff) (N : ℕ) (hN : 0 < N)
    (x y z : ℝ) :
    gmTraceNonzeroTailAt cutoff N x *
        gmTraceNonzeroTailAt cutoff N y *
          gmTraceNonzeroTailAt cutoff N z =
      ∑' m : ℤ × (ℤ × ℤ),
        gmNonzeroScaledTraceMode cutoff N x m.1 *
          gmNonzeroScaledTraceMode cutoff N y m.2.1 *
            gmNonzeroScaledTraceMode cutoff N z m.2.2 := by
  rw [gmTraceNonzeroTailAt_eq_tsum_nonzeroScaledTraceMode,
    gmTraceNonzeroTailAt_eq_tsum_nonzeroScaledTraceMode,
    gmTraceNonzeroTailAt_eq_tsum_nonzeroScaledTraceMode]
  rw [mul_assoc]
  rw [tsum_mul_tsum_of_summable_norm
    (summable_norm_gmNonzeroScaledTraceMode cutoff N hN y)
    (summable_norm_gmNonzeroScaledTraceMode cutoff N hN z)]
  rw [tsum_mul_tsum_of_summable_norm
    (summable_norm_gmNonzeroScaledTraceMode cutoff N hN x)
    ((summable_norm_gmNonzeroScaledTraceMode cutoff N hN y).mul_norm
      (summable_norm_gmNonzeroScaledTraceMode cutoff N hN z))]
  congr 1
  funext m
  ring

private theorem summable_fintype_sum
    {ι β : Type*} [Fintype ι] {f : ι → β → ℂ}
    (hf : ∀ i, Summable (f i)) :
    Summable (fun b => ∑ i, f i b) := by
  classical
  have hs : ∀ s : Finset ι,
      Summable (fun b => ∑ i ∈ s, f i b) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
        simp_rw [Finset.sum_insert hi]
        exact (hf i).add ih
  simpa using hs Finset.univ

private theorem tsum_fintype_sum
    {ι β : Type*} [Fintype ι] {f : ι → β → ℂ}
    (hf : ∀ i, Summable (f i)) :
    (∑' b, ∑ i, f i b) = ∑ i, ∑' b, f i b := by
  classical
  exact Summable.tsum_finsetSum (s := Finset.univ) (fun i hi => hf i)

/-- Absolute summability of the complete Section 7 triple-frequency series. -/
theorem gmCubicS3Mode_summable (cutoff : GMSmoothCutoff) (N : ℕ)
    (hN : 0 < N) (W : Finset ℝ) :
    Summable (gmCubicS3Mode cutoff N W) := by
  unfold gmCubicS3Mode
  apply summable_fintype_sum
  intro t
  apply summable_fintype_sum
  intro u
  apply summable_fintype_sum
  intro v
  have hx := summable_norm_gmNonzeroScaledTraceMode cutoff N hN
    ((t : ℝ) - (u : ℝ))
  have hy := summable_norm_gmNonzeroScaledTraceMode cutoff N hN
    ((u : ℝ) - (v : ℝ))
  have hz := summable_norm_gmNonzeroScaledTraceMode cutoff N hN
    ((v : ℝ) - (t : ℝ))
  simpa only [mul_assoc] using (hx.mul_norm (hy.mul_norm hz)).of_norm

/-- Exact expansion of the actual cubic `S₃` term into all three nonzero
integer Poisson frequencies.  This is the series-level entry to Section 7. -/
theorem gmCubicS3_eq_tsum_modes (cutoff : GMSmoothCutoff) (N : ℕ)
    (hN : 0 < N) (W : Finset ℝ) :
    gmCubicS3 cutoff N W = ∑' m, gmCubicS3Mode cutoff N W m := by
  unfold gmCubicS3 gmCubicS3Mode
  simp_rw [gmTraceNonzeroTailAt_mul_mul_eq_tsum_modes cutoff N hN]
  have htriple (t u v : GMRow W) :
      Summable (fun m : ℤ × (ℤ × ℤ) =>
        gmNonzeroScaledTraceMode cutoff N ((t : ℝ) - (u : ℝ)) m.1 *
          gmNonzeroScaledTraceMode cutoff N ((u : ℝ) - (v : ℝ)) m.2.1 *
            gmNonzeroScaledTraceMode cutoff N ((v : ℝ) - (t : ℝ)) m.2.2) := by
    have hx := summable_norm_gmNonzeroScaledTraceMode cutoff N hN
      ((t : ℝ) - (u : ℝ))
    have hy := summable_norm_gmNonzeroScaledTraceMode cutoff N hN
      ((u : ℝ) - (v : ℝ))
    have hz := summable_norm_gmNonzeroScaledTraceMode cutoff N hN
      ((v : ℝ) - (t : ℝ))
    simpa only [mul_assoc] using (hx.mul_norm (hy.mul_norm hz)).of_norm
  have huv (t u : GMRow W) :
      Summable (fun m : ℤ × (ℤ × ℤ) => ∑ v : GMRow W,
        gmNonzeroScaledTraceMode cutoff N ((t : ℝ) - (u : ℝ)) m.1 *
          gmNonzeroScaledTraceMode cutoff N ((u : ℝ) - (v : ℝ)) m.2.1 *
            gmNonzeroScaledTraceMode cutoff N ((v : ℝ) - (t : ℝ)) m.2.2) :=
    summable_fintype_sum (fun v => htriple t u v)
  have htu (t : GMRow W) :
      Summable (fun m : ℤ × (ℤ × ℤ) => ∑ u : GMRow W, ∑ v : GMRow W,
        gmNonzeroScaledTraceMode cutoff N ((t : ℝ) - (u : ℝ)) m.1 *
          gmNonzeroScaledTraceMode cutoff N ((u : ℝ) - (v : ℝ)) m.2.1 *
            gmNonzeroScaledTraceMode cutoff N ((v : ℝ) - (t : ℝ)) m.2.2) :=
    summable_fintype_sum (fun u => huv t u)
  symm
  rw [tsum_fintype_sum htu]
  congr 1
  funext t
  rw [tsum_fintype_sum (huv t)]
  congr 1
  funext u
  rw [tsum_fintype_sum (htriple t u)]

/-! ## Finite source frequency boxes -/

/-- The symmetric three-frequency box used in Guth--Maynard (7.1).  The
nesting agrees with the project's frequency type `ℤ × (ℤ × ℤ)`. -/
noncomputable def gmCubicFrequencyBox (H : ℕ) : Finset (ℤ × (ℤ × ℤ)) :=
  Finset.Icc (-(H : ℤ)) (H : ℤ) ×ˢ
    (Finset.Icc (-(H : ℤ)) (H : ℤ) ×ˢ
      Finset.Icc (-(H : ℤ)) (H : ℤ))

@[simp]
theorem mem_gmCubicFrequencyBox {H : ℕ} {m : ℤ × (ℤ × ℤ)} :
    m ∈ gmCubicFrequencyBox H ↔
      -(H : ℤ) ≤ m.1 ∧ m.1 ≤ (H : ℤ) ∧
      -(H : ℤ) ≤ m.2.1 ∧ m.2.1 ≤ (H : ℤ) ∧
      -(H : ℤ) ≤ m.2.2 ∧ m.2.2 ≤ (H : ℤ) := by
  simp [gmCubicFrequencyBox, and_assoc]

/-- The literal finite body of the Section 7 three-frequency expansion. -/
noncomputable def gmCubicS3Truncated (cutoff : GMSmoothCutoff) (N H : ℕ)
    (W : Finset ℝ) : ℂ :=
  ∑ m ∈ gmCubicFrequencyBox H, gmCubicS3Mode cutoff N W m

/-- The absolutely convergent complementary frequency tail. -/
noncomputable def gmCubicS3FrequencyTail (cutoff : GMSmoothCutoff) (N H : ℕ)
    (W : Finset ℝ) : ℂ :=
  ∑' m : {m : ℤ × (ℤ × ℤ) // m ∉ gmCubicFrequencyBox H},
    gmCubicS3Mode cutoff N W m

/-- Exact form of the first step of (7.1): the actual cubic `S₃` is its
finite symmetric frequency body plus the complete omitted-frequency tail. -/
theorem gmCubicS3_eq_truncated_add_frequencyTail
    (cutoff : GMSmoothCutoff) (N H : ℕ) (hN : 0 < N) (W : Finset ℝ) :
    gmCubicS3 cutoff N W =
      gmCubicS3Truncated cutoff N H W +
        gmCubicS3FrequencyTail cutoff N H W := by
  rw [gmCubicS3_eq_tsum_modes cutoff N hN W]
  unfold gmCubicS3Truncated gmCubicS3FrequencyTail
  symm
  simpa only [Finset.sum_filter] using
    (gmCubicS3Mode_summable cutoff N hN W).sum_add_tsum_subtype_compl
      (gmCubicFrequencyBox H)

/-- The even integer `p`-series profile, with the singular zero term removed. -/
noncomputable def gmIntDecayProfile (q : ℕ) (m : ℤ) : ℝ :=
  if m = 0 then 0 else 1 / |(m : ℝ)| ^ q

theorem summable_gmIntDecayProfile {q : ℕ} (hq : 2 ≤ q) :
    Summable (gmIntDecayProfile q) := by
  have hs : Summable (fun m : ℤ => |1 / (m : ℝ) ^ q|) := by
    rw [summable_abs_iff]
    exact Real.summable_one_div_int_pow.mpr (lt_of_lt_of_le (by norm_num) hq)
  apply Summable.of_nonneg_of_le (fun m => by
    simp only [gmIntDecayProfile]
    split_ifs
    · exact le_rfl
    · positivity) (fun m => ?_) hs
  by_cases hm : m = 0
  · simp [gmIntDecayProfile, hm]
  · simp only [gmIntDecayProfile, if_false, hm, abs_div, abs_one, abs_pow]
    exact le_rfl

/-- Pointwise arbitrary-order decay of one nonzero scaled Poisson mode.  This
is Lemma 4.3(1) in the normalization required by the Section 7 series. -/
theorem exists_gmNonzeroScaledTraceMode_decay (cutoff : GMSmoothCutoff)
    (q : ℕ) (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ), 0 < N → ∀ (t : ℝ) (m : ℤ),
      ‖gmNonzeroScaledTraceMode cutoff N t m‖ ≤
        (C * (1 + |t|) ^ q / (N : ℝ) ^ (q - 1)) *
          gmIntDecayProfile q m := by
  obtain ⟨C, hC, hDecay⟩ := gmTraceFourier_uniform_decay cutoff q
  refine ⟨C, hC, ?_⟩
  intro N hN t m
  by_cases hm : m = 0
  · simp [gmNonzeroScaledTraceMode, gmIntDecayProfile, hm]
  · have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
    have hmReal : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    have hmAbs : 0 < |(m : ℝ)| := abs_pos.mpr hmReal
    have hFreqAbs : |(N : ℝ) * (m : ℝ)| =
        (N : ℝ) * |(m : ℝ)| := by rw [abs_mul, abs_of_pos hNr]
    have hFreqPos : 0 < |(N : ℝ) * (m : ℝ)| := by positivity
    have hFourier :
        ‖gmTraceFourier cutoff t ((N : ℝ) * (m : ℝ))‖ ≤
          C * (1 + |t|) ^ q / |(N : ℝ) * (m : ℝ)| ^ q := by
      rw [le_div_iff₀ (pow_pos hFreqPos q)]
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        hDecay t ((N : ℝ) * (m : ℝ))
    simp only [gmNonzeroScaledTraceMode, if_false, hm, gmScaledTraceMode,
      norm_mul, Complex.norm_natCast, gmIntDecayProfile]
    have hqEq : q = (q - 1) + 1 := by omega
    have hNpow : (N : ℝ) ^ q = (N : ℝ) ^ (q - 1) * (N : ℝ) := by
      conv_lhs => rw [hqEq, pow_succ]
    calc
      (N : ℝ) * ‖gmTraceFourier cutoff t ((N : ℝ) * (m : ℝ))‖ ≤
          (N : ℝ) *
            (C * (1 + |t|) ^ q /
              |(N : ℝ) * (m : ℝ)| ^ q) := by
        gcongr
      _ = (N : ℝ) *
            (C * (1 + |t|) ^ q /
              ((N : ℝ) ^ q * |(m : ℝ)| ^ q)) := by
        rw [hFreqAbs, mul_pow]
      _ = (C * (1 + |t|) ^ q / (N : ℝ) ^ (q - 1)) *
          (1 / |(m : ℝ)| ^ q) := by
        rw [hNpow]
        field_simp

/-- Outside the symmetric radius `H`, arbitrary-order decay factors into a
fixed square-summable integer profile and an explicit `H⁻ʳ` gain. -/
theorem gmIntDecayProfile_add_two_le_of_outside
    {r H : ℕ} {m : ℤ} (hm : m ∉ Finset.Icc (-(H : ℤ)) (H : ℤ)) :
    gmIntDecayProfile (r + 2) m ≤
      (1 / ((H + 1 : ℕ) : ℝ) ^ r) * gmIntDecayProfile 2 m := by
  have hm0 : m ≠ 0 := by
    intro hzero
    subst m
    exact hm (by simp)
  have habsInt : ((H + 1 : ℕ) : ℤ) ≤ |m| := by
    simp only [Finset.mem_Icc, not_and_or] at hm
    by_cases hmnonneg : 0 ≤ m
    · rw [abs_of_nonneg hmnonneg]
      rcases hm with hm | hm <;> omega
    · rw [abs_of_nonpos (le_of_not_ge hmnonneg)]
      rcases hm with hm | hm <;> omega
  have habs : ((H + 1 : ℕ) : ℝ) ≤ |(m : ℝ)| := by
    exact_mod_cast habsInt
  have hH : 0 < ((H + 1 : ℕ) : ℝ) := by positivity
  have hmAbs : 0 < |(m : ℝ)| := abs_pos.mpr (by exact_mod_cast hm0)
  simp only [gmIntDecayProfile, if_false, hm0]
  rw [pow_add]
  have hpow : ((H + 1 : ℕ) : ℝ) ^ r ≤ |(m : ℝ)| ^ r :=
    pow_le_pow_left₀ hH.le habs r
  calc
    1 / (|(m : ℝ)| ^ r * |(m : ℝ)| ^ 2) =
        (1 / |(m : ℝ)| ^ r) * (1 / |(m : ℝ)| ^ 2) := by field_simp
    _ ≤ (1 / ((H + 1 : ℕ) : ℝ) ^ r) * (1 / |(m : ℝ)| ^ 2) := by
      gcongr

theorem gmIntDecayProfile_add_two_le (r : ℕ) (m : ℤ) :
    gmIntDecayProfile (r + 2) m ≤ gmIntDecayProfile 2 m := by
  by_cases hm : m = 0
  · simp [gmIntDecayProfile, hm]
  · have hout : m ∉ Finset.Icc (0 : ℤ) 0 := by simpa using hm
    simpa using
      (gmIntDecayProfile_add_two_le_of_outside (r := r) (H := 0) hout)

/-- Product majorant for a three-frequency mode. -/
noncomputable def gmTripleDecayProfile (q : ℕ)
    (m : ℤ × (ℤ × ℤ)) : ℝ :=
  gmIntDecayProfile q m.1 * gmIntDecayProfile q m.2.1 *
    gmIntDecayProfile q m.2.2

theorem gmTripleDecayProfile_nonneg (q : ℕ) (m : ℤ × (ℤ × ℤ)) :
    0 ≤ gmTripleDecayProfile q m := by
  unfold gmTripleDecayProfile gmIntDecayProfile
  split_ifs <;> positivity

theorem summable_gmTripleDecayProfile {q : ℕ} (hq : 2 ≤ q) :
    Summable (gmTripleDecayProfile q) := by
  have hs := summable_gmIntDecayProfile hq
  have hnonneg : ∀ z : ℤ, 0 ≤ gmIntDecayProfile q z := by
    intro z
    simp only [gmIntDecayProfile]
    split_ifs <;> positivity
  exact (hs.mul_of_nonneg (hs.mul_of_nonneg hs hnonneg hnonneg) hnonneg
    (fun z => mul_nonneg (hnonneg z.1) (hnonneg z.2))).congr
      (fun m => by simp [gmTripleDecayProfile, mul_assoc])

/-- If a triple lies outside the symmetric box, one coordinate supplies the
full `H⁻ʳ` gain while the other two are bounded by the fixed quadratic
profile. -/
theorem gmTripleDecayProfile_add_two_le_of_outside
    {r H : ℕ} {m : ℤ × (ℤ × ℤ)} (hm : m ∉ gmCubicFrequencyBox H) :
    gmTripleDecayProfile (r + 2) m ≤
      (1 / ((H + 1 : ℕ) : ℝ) ^ r) * gmTripleDecayProfile 2 m := by
  have hcases :
      m.1 ∉ Finset.Icc (-(H : ℤ)) (H : ℤ) ∨
      m.2.1 ∉ Finset.Icc (-(H : ℤ)) (H : ℤ) ∨
      m.2.2 ∉ Finset.Icc (-(H : ℤ)) (H : ℤ) := by
    by_cases h₁ : m.1 ∈ Finset.Icc (-(H : ℤ)) (H : ℤ)
    · by_cases h₂ : m.2.1 ∈ Finset.Icc (-(H : ℤ)) (H : ℤ)
      · by_cases h₃ : m.2.2 ∈ Finset.Icc (-(H : ℤ)) (H : ℤ)
        · exact False.elim (hm (by simp [gmCubicFrequencyBox, h₁, h₂, h₃]))
        · exact Or.inr (Or.inr h₃)
      · exact Or.inr (Or.inl h₂)
    · exact Or.inl h₁
  have hnonneg (q : ℕ) (z : ℤ) : 0 ≤ gmIntDecayProfile q z := by
    simp only [gmIntDecayProfile]
    split_ifs <;> positivity
  have hfactor : 0 ≤ (1 / ((H + 1 : ℕ) : ℝ) ^ r) := by positivity
  have hprod {a₁ a₂ a₃ b₁ b₂ b₃ : ℝ}
      (ha₂ : 0 ≤ a₂) (ha₃ : 0 ≤ a₃)
      (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂)
      (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂) (h₃ : a₃ ≤ b₃) :
      a₁ * a₂ * a₃ ≤ b₁ * b₂ * b₃ := by
    exact mul_le_mul (mul_le_mul h₁ h₂ ha₂ hb₁) h₃ ha₃
      (mul_nonneg hb₁ hb₂)
  rcases hcases with h₁ | h₂ | h₃
  · have hb₁ := gmIntDecayProfile_add_two_le_of_outside (r := r) h₁
    have hb₂ := gmIntDecayProfile_add_two_le r m.2.1
    have hb₃ := gmIntDecayProfile_add_two_le r m.2.2
    unfold gmTripleDecayProfile
    calc
      gmIntDecayProfile (r + 2) m.1 * gmIntDecayProfile (r + 2) m.2.1 *
          gmIntDecayProfile (r + 2) m.2.2 ≤
        ((1 / ((H + 1 : ℕ) : ℝ) ^ r) * gmIntDecayProfile 2 m.1) *
          gmIntDecayProfile 2 m.2.1 * gmIntDecayProfile 2 m.2.2 := by
        exact hprod (hnonneg _ _) (hnonneg _ _)
          (mul_nonneg hfactor (hnonneg _ _)) (hnonneg _ _) hb₁ hb₂ hb₃
      _ = (1 / ((H + 1 : ℕ) : ℝ) ^ r) *
          (gmIntDecayProfile 2 m.1 * gmIntDecayProfile 2 m.2.1 *
            gmIntDecayProfile 2 m.2.2) := by ring
  · have hb₁ := gmIntDecayProfile_add_two_le r m.1
    have hb₂ := gmIntDecayProfile_add_two_le_of_outside (r := r) h₂
    have hb₃ := gmIntDecayProfile_add_two_le r m.2.2
    unfold gmTripleDecayProfile
    calc
      gmIntDecayProfile (r + 2) m.1 * gmIntDecayProfile (r + 2) m.2.1 *
          gmIntDecayProfile (r + 2) m.2.2 ≤
        gmIntDecayProfile 2 m.1 *
          ((1 / ((H + 1 : ℕ) : ℝ) ^ r) * gmIntDecayProfile 2 m.2.1) *
            gmIntDecayProfile 2 m.2.2 := by
        exact hprod (hnonneg _ _) (hnonneg _ _) (hnonneg _ _)
          (mul_nonneg hfactor (hnonneg _ _)) hb₁ hb₂ hb₃
      _ = (1 / ((H + 1 : ℕ) : ℝ) ^ r) *
          (gmIntDecayProfile 2 m.1 * gmIntDecayProfile 2 m.2.1 *
            gmIntDecayProfile 2 m.2.2) := by ring
  · have hb₁ := gmIntDecayProfile_add_two_le r m.1
    have hb₂ := gmIntDecayProfile_add_two_le r m.2.1
    have hb₃ := gmIntDecayProfile_add_two_le_of_outside (r := r) h₃
    unfold gmTripleDecayProfile
    calc
      gmIntDecayProfile (r + 2) m.1 * gmIntDecayProfile (r + 2) m.2.1 *
          gmIntDecayProfile (r + 2) m.2.2 ≤
        gmIntDecayProfile 2 m.1 * gmIntDecayProfile 2 m.2.1 *
          ((1 / ((H + 1 : ℕ) : ℝ) ^ r) * gmIntDecayProfile 2 m.2.2) := by
        exact hprod (hnonneg _ _) (hnonneg _ _) (hnonneg _ _) (hnonneg _ _)
          hb₁ hb₂ hb₃
      _ = (1 / ((H + 1 : ℕ) : ℝ) ^ r) *
          (gmIntDecayProfile 2 m.1 * gmIntDecayProfile 2 m.2.1 *
            gmIntDecayProfile 2 m.2.2) := by ring

/-- Uniform norm majorant for one Section 7 frequency mode on ordinates in
`[0,T]`. -/
theorem exists_norm_gmCubicS3Mode_le_decay (cutoff : GMSmoothCutoff)
    (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ), 0 < N → ∀ {T : ℝ} {W : Finset ℝ},
      1 ≤ T → InBaseInterval T W → ∀ m : ℤ × (ℤ × ℤ),
      ‖gmCubicS3Mode cutoff N W m‖ ≤
        (W.card : ℝ) ^ 3 *
          (C * (1 + T) ^ (r + 2) / (N : ℝ) ^ (r + 1)) ^ 3 *
            gmTripleDecayProfile (r + 2) m := by
  obtain ⟨C, hC, hDecay⟩ :=
    exists_gmNonzeroScaledTraceMode_decay cutoff (r + 2) (by omega)
  refine ⟨C, hC, ?_⟩
  intro N hN T W hT hBase m
  let A : ℝ := C * (1 + T) ^ (r + 2) / (N : ℝ) ^ (r + 1)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hprofile (q : ℕ) (z : ℤ) : 0 ≤ gmIntDecayProfile q z := by
    simp only [gmIntDecayProfile]
    split_ifs <;> positivity
  have hTerm (t u v : GMRow W) :
      ‖gmNonzeroScaledTraceMode cutoff N ((t : ℝ) - (u : ℝ)) m.1 *
          gmNonzeroScaledTraceMode cutoff N ((u : ℝ) - (v : ℝ)) m.2.1 *
            gmNonzeroScaledTraceMode cutoff N ((v : ℝ) - (t : ℝ)) m.2.2‖ ≤
        A ^ 3 * gmTripleDecayProfile (r + 2) m := by
    have htu := abs_sub_le_height_of_mem_baseInterval hBase t.property u.property
    have huv := abs_sub_le_height_of_mem_baseInterval hBase u.property v.property
    have hvt := abs_sub_le_height_of_mem_baseInterval hBase v.property t.property
    have hOne (x y : GMRow W)
        (hxy : |(x : ℝ) - (y : ℝ)| ≤ T) :
        (1 + |(x : ℝ) - (y : ℝ)|) ^ (r + 2) ≤
          (1 + T) ^ (r + 2) := by
      exact pow_le_pow_left₀ (by positivity) (by linarith) (r + 2)
    have hMode (x y : GMRow W) (z : ℤ)
        (hxy : |(x : ℝ) - (y : ℝ)| ≤ T) :
        ‖gmNonzeroScaledTraceMode cutoff N ((x : ℝ) - (y : ℝ)) z‖ ≤
          A * gmIntDecayProfile (r + 2) z := by
      have hraw := hDecay N hN ((x : ℝ) - (y : ℝ)) z
      have hpow := hOne x y hxy
      have hden : (r + 2 - 1 : ℕ) = r + 1 := by omega
      calc
        ‖gmNonzeroScaledTraceMode cutoff N ((x : ℝ) - (y : ℝ)) z‖ ≤
            (C * (1 + |(x : ℝ) - (y : ℝ)|) ^ (r + 2) /
                (N : ℝ) ^ (r + 2 - 1)) *
              gmIntDecayProfile (r + 2) z := hraw
        _ ≤ (C * (1 + T) ^ (r + 2) / (N : ℝ) ^ (r + 2 - 1)) *
              gmIntDecayProfile (r + 2) z := by
          exact mul_le_mul_of_nonneg_right (by gcongr) (hprofile _ _)
        _ = A * gmIntDecayProfile (r + 2) z := by rw [hden]
    have h₁ := hMode t u m.1 htu
    have h₂ := hMode u v m.2.1 huv
    have h₃ := hMode v t m.2.2 hvt
    simp only [norm_mul]
    unfold gmTripleDecayProfile
    calc
      ‖gmNonzeroScaledTraceMode cutoff N ((t : ℝ) - (u : ℝ)) m.1‖ *
          ‖gmNonzeroScaledTraceMode cutoff N ((u : ℝ) - (v : ℝ)) m.2.1‖ *
            ‖gmNonzeroScaledTraceMode cutoff N ((v : ℝ) - (t : ℝ)) m.2.2‖ ≤
        (A * gmIntDecayProfile (r + 2) m.1) *
          (A * gmIntDecayProfile (r + 2) m.2.1) *
            (A * gmIntDecayProfile (r + 2) m.2.2) := by
        exact mul_le_mul
          (mul_le_mul h₁ h₂ (norm_nonneg _)
            (mul_nonneg hA (hprofile _ _))) h₃ (norm_nonneg _)
              (mul_nonneg (mul_nonneg hA (hprofile _ _))
                (mul_nonneg hA (hprofile _ _)))
      _ = A ^ 3 *
          (gmIntDecayProfile (r + 2) m.1 *
            gmIntDecayProfile (r + 2) m.2.1 *
              gmIntDecayProfile (r + 2) m.2.2) := by ring
  unfold gmCubicS3Mode
  calc
    ‖∑ t : GMRow W, ∑ u : GMRow W, ∑ v : GMRow W,
        gmNonzeroScaledTraceMode cutoff N ((t : ℝ) - (u : ℝ)) m.1 *
          gmNonzeroScaledTraceMode cutoff N ((u : ℝ) - (v : ℝ)) m.2.1 *
            gmNonzeroScaledTraceMode cutoff N ((v : ℝ) - (t : ℝ)) m.2.2‖ ≤
      ∑ t : GMRow W, ‖∑ u : GMRow W, ∑ v : GMRow W,
        gmNonzeroScaledTraceMode cutoff N ((t : ℝ) - (u : ℝ)) m.1 *
          gmNonzeroScaledTraceMode cutoff N ((u : ℝ) - (v : ℝ)) m.2.1 *
            gmNonzeroScaledTraceMode cutoff N ((v : ℝ) - (t : ℝ)) m.2.2‖ :=
        norm_sum_le _ _
    _ ≤ ∑ t : GMRow W, ∑ u : GMRow W, ‖∑ v : GMRow W,
        gmNonzeroScaledTraceMode cutoff N ((t : ℝ) - (u : ℝ)) m.1 *
          gmNonzeroScaledTraceMode cutoff N ((u : ℝ) - (v : ℝ)) m.2.1 *
            gmNonzeroScaledTraceMode cutoff N ((v : ℝ) - (t : ℝ)) m.2.2‖ := by
      gcongr with t ht
      exact norm_sum_le _ _
    _ ≤ ∑ t : GMRow W, ∑ u : GMRow W, ∑ v : GMRow W,
        ‖gmNonzeroScaledTraceMode cutoff N ((t : ℝ) - (u : ℝ)) m.1 *
          gmNonzeroScaledTraceMode cutoff N ((u : ℝ) - (v : ℝ)) m.2.1 *
            gmNonzeroScaledTraceMode cutoff N ((v : ℝ) - (t : ℝ)) m.2.2‖ := by
      gcongr with t ht u hu
      exact norm_sum_le _ _
    _ ≤ ∑ _t : GMRow W, ∑ _u : GMRow W, ∑ _v : GMRow W,
        A ^ 3 * gmTripleDecayProfile (r + 2) m := by
      gcongr with t ht u hu v hv
      exact hTerm t u v
    _ = (W.card : ℝ) ^ 3 * A ^ 3 * gmTripleDecayProfile (r + 2) m := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
      ring
    _ = _ := by rfl

/-- Quantitative omitted-frequency estimate for the complete complementary
triple series.  The constants are independent of `N`, `H`, `T`, and `W`;
the displayed `(H+1)⁻ʳ` is the gain used to obtain the `T⁻¹⁰⁰` remainder in
Guth--Maynard (7.1). -/
theorem exists_norm_gmCubicS3FrequencyTail_le
    (cutoff : GMSmoothCutoff) (r : ℕ) :
    ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ ∀ (N H : ℕ), 0 < N →
      ∀ {T : ℝ} {W : Finset ℝ}, 1 ≤ T → InBaseInterval T W →
      ‖gmCubicS3FrequencyTail cutoff N H W‖ ≤
        (W.card : ℝ) ^ 3 *
          (C * (1 + T) ^ (r + 2) / (N : ℝ) ^ (r + 1)) ^ 3 *
          (1 / ((H + 1 : ℕ) : ℝ) ^ r) * B := by
  obtain ⟨C, hC, hMode⟩ := exists_norm_gmCubicS3Mode_le_decay cutoff r
  let B : ℝ := ∑' m : ℤ × (ℤ × ℤ), gmTripleDecayProfile 2 m
  have hB : 0 ≤ B := tsum_nonneg (gmTripleDecayProfile_nonneg 2)
  refine ⟨C, B, hC, hB, ?_⟩
  intro N H hN T W hT hBase
  let K : ℝ := (W.card : ℝ) ^ 3 *
    (C * (1 + T) ^ (r + 2) / (N : ℝ) ^ (r + 1)) ^ 3
  let F : ℝ := 1 / ((H + 1 : ℕ) : ℝ) ^ r
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  have hModeNorm : Summable (fun m :
      {m : ℤ × (ℤ × ℤ) // m ∉ gmCubicFrequencyBox H} =>
      ‖gmCubicS3Mode cutoff N W m‖) :=
    (gmCubicS3Mode_summable cutoff N hN W).norm.subtype _
  have hProfile : Summable (fun m :
      {m : ℤ × (ℤ × ℤ) // m ∉ gmCubicFrequencyBox H} =>
      gmTripleDecayProfile 2 m) :=
    (summable_gmTripleDecayProfile (by norm_num)).subtype _
  have hMajor : Summable (fun m :
      {m : ℤ × (ℤ × ℤ) // m ∉ gmCubicFrequencyBox H} =>
      K * F * gmTripleDecayProfile 2 m) := hProfile.mul_left (K * F)
  have hPoint (m : {m : ℤ × (ℤ × ℤ) // m ∉ gmCubicFrequencyBox H}) :
      ‖gmCubicS3Mode cutoff N W m‖ ≤
        K * F * gmTripleDecayProfile 2 m := by
    have hm := hMode N hN hT hBase (m : ℤ × (ℤ × ℤ))
    have htail := gmTripleDecayProfile_add_two_le_of_outside
      (r := r) m.property
    calc
      ‖gmCubicS3Mode cutoff N W m‖ ≤
          K * gmTripleDecayProfile (r + 2) m := by simpa [K] using hm
      _ ≤ K * (F * gmTripleDecayProfile 2 m) := by
        exact mul_le_mul_of_nonneg_left (by simpa [F] using htail) hK
      _ = K * F * gmTripleDecayProfile 2 m := by ring
  unfold gmCubicS3FrequencyTail
  calc
    ‖∑' m : {m : ℤ × (ℤ × ℤ) // m ∉ gmCubicFrequencyBox H},
        gmCubicS3Mode cutoff N W m‖ ≤
      ∑' m : {m : ℤ × (ℤ × ℤ) // m ∉ gmCubicFrequencyBox H},
        ‖gmCubicS3Mode cutoff N W m‖ :=
      norm_tsum_le_tsum_norm hModeNorm
    _ ≤ ∑' m : {m : ℤ × (ℤ × ℤ) // m ∉ gmCubicFrequencyBox H},
        K * F * gmTripleDecayProfile 2 m :=
      hModeNorm.tsum_le_tsum hPoint hMajor
    _ = K * F *
        (∑' m : {m : ℤ × (ℤ × ℤ) // m ∉ gmCubicFrequencyBox H},
          gmTripleDecayProfile 2 m) := by rw [tsum_mul_left]
    _ ≤ K * F * B := by
      gcongr
      exact Summable.tsum_subtype_le (gmTripleDecayProfile 2) _
        (gmTripleDecayProfile_nonneg 2)
        (summable_gmTripleDecayProfile (by norm_num))
    _ = _ := by rfl

/-- Source-sharp mixed-order tail estimate.  Only the coordinate which leaves
the finite frequency box is charged the high derivative order; the other two
coordinates use the fixed quadratic summable bound.  This is the quantitative
form needed for the `T^η T/N` window in (7.1). -/
theorem exists_norm_gmCubicS3FrequencyTail_le_mixed
    (cutoff : GMSmoothCutoff) (r : ℕ) :
    ∃ C₂ Cᵣ B : ℝ, 0 ≤ C₂ ∧ 0 ≤ Cᵣ ∧ 0 ≤ B ∧
      ∀ (N H : ℕ), 0 < N → ∀ {T : ℝ} {W : Finset ℝ},
      1 ≤ T → InBaseInterval T W →
      ‖gmCubicS3FrequencyTail cutoff N H W‖ ≤
        (W.card : ℝ) ^ 3 *
          (Cᵣ * (1 + T) ^ (r + 2) / (N : ℝ) ^ (r + 1)) *
          (C₂ * (1 + T) ^ 2 / (N : ℝ)) ^ 2 *
          (1 / ((H + 1 : ℕ) : ℝ) ^ r) * B := by
  obtain ⟨C₂, hC₂, hDecay₂⟩ :=
    exists_gmNonzeroScaledTraceMode_decay cutoff 2 (by norm_num)
  obtain ⟨Cᵣ, hCᵣ, hDecayᵣ⟩ :=
    exists_gmNonzeroScaledTraceMode_decay cutoff (r + 2) (by omega)
  let B : ℝ := ∑' m : ℤ × (ℤ × ℤ), gmTripleDecayProfile 2 m
  have hB : 0 ≤ B := tsum_nonneg (gmTripleDecayProfile_nonneg 2)
  refine ⟨C₂, Cᵣ, B, hC₂, hCᵣ, hB, ?_⟩
  intro N H hN T W hT hBase
  let A₂ : ℝ := C₂ * (1 + T) ^ 2 / (N : ℝ)
  let Aᵣ : ℝ := Cᵣ * (1 + T) ^ (r + 2) / (N : ℝ) ^ (r + 1)
  let F : ℝ := 1 / ((H + 1 : ℕ) : ℝ) ^ r
  let K : ℝ := (W.card : ℝ) ^ 3 * Aᵣ * A₂ ^ 2 * F
  have hA₂ : 0 ≤ A₂ := by dsimp only [A₂]; positivity
  have hAᵣ : 0 ≤ Aᵣ := by dsimp only [Aᵣ]; positivity
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hprofile (q : ℕ) (z : ℤ) : 0 ≤ gmIntDecayProfile q z := by
    simp only [gmIntDecayProfile]
    split_ifs <;> positivity
  have hOne (x y : GMRow W)
      (hxy : |(x : ℝ) - (y : ℝ)| ≤ T) (q : ℕ) :
      (1 + |(x : ℝ) - (y : ℝ)|) ^ q ≤ (1 + T) ^ q :=
    pow_le_pow_left₀ (by positivity) (by linarith) q
  have hMode₂ (x y : GMRow W) (z : ℤ) :
      ‖gmNonzeroScaledTraceMode cutoff N ((x : ℝ) - (y : ℝ)) z‖ ≤
        A₂ * gmIntDecayProfile 2 z := by
    have hxy := abs_sub_le_height_of_mem_baseInterval hBase x.property y.property
    have hraw := hDecay₂ N hN ((x : ℝ) - (y : ℝ)) z
    calc
      _ ≤ (C₂ * (1 + |(x : ℝ) - (y : ℝ)|) ^ 2 / (N : ℝ) ^ (2 - 1)) *
          gmIntDecayProfile 2 z := hraw
      _ ≤ (C₂ * (1 + T) ^ 2 / (N : ℝ) ^ (2 - 1)) *
          gmIntDecayProfile 2 z := by
        exact mul_le_mul_of_nonneg_right (by gcongr)
          (hprofile _ _)
      _ = A₂ * gmIntDecayProfile 2 z := by norm_num [A₂]
  have hModeᵣ (x y : GMRow W) (z : ℤ) :
      ‖gmNonzeroScaledTraceMode cutoff N ((x : ℝ) - (y : ℝ)) z‖ ≤
        Aᵣ * gmIntDecayProfile (r + 2) z := by
    have hxy := abs_sub_le_height_of_mem_baseInterval hBase x.property y.property
    have hraw := hDecayᵣ N hN ((x : ℝ) - (y : ℝ)) z
    have hden : r + 2 - 1 = r + 1 := by omega
    calc
      _ ≤ (Cᵣ * (1 + |(x : ℝ) - (y : ℝ)|) ^ (r + 2) /
          (N : ℝ) ^ (r + 2 - 1)) * gmIntDecayProfile (r + 2) z := hraw
      _ ≤ (Cᵣ * (1 + T) ^ (r + 2) /
          (N : ℝ) ^ (r + 2 - 1)) * gmIntDecayProfile (r + 2) z := by
        exact mul_le_mul_of_nonneg_right
          (by gcongr) (hprofile _ _)
      _ = Aᵣ * gmIntDecayProfile (r + 2) z := by rw [hden]
  have hTerm (m : {m : ℤ × (ℤ × ℤ) // m ∉ gmCubicFrequencyBox H})
      (t u v : GMRow W) :
      ‖gmNonzeroScaledTraceMode cutoff N ((t : ℝ) - (u : ℝ)) m.val.1 *
          gmNonzeroScaledTraceMode cutoff N ((u : ℝ) - (v : ℝ)) m.val.2.1 *
            gmNonzeroScaledTraceMode cutoff N ((v : ℝ) - (t : ℝ)) m.val.2.2‖ ≤
        Aᵣ * A₂ ^ 2 * F * gmTripleDecayProfile 2 m := by
    have hcases :
        m.val.1 ∉ Finset.Icc (-(H : ℤ)) (H : ℤ) ∨
        m.val.2.1 ∉ Finset.Icc (-(H : ℤ)) (H : ℤ) ∨
        m.val.2.2 ∉ Finset.Icc (-(H : ℤ)) (H : ℤ) := by
      by_cases h₁ : m.val.1 ∈ Finset.Icc (-(H : ℤ)) (H : ℤ)
      · by_cases h₂ : m.val.2.1 ∈ Finset.Icc (-(H : ℤ)) (H : ℤ)
        · by_cases h₃ : m.val.2.2 ∈ Finset.Icc (-(H : ℤ)) (H : ℤ)
          · exact False.elim (m.property (by
              simp only [gmCubicFrequencyBox, Finset.mem_product]
              exact ⟨h₁, h₂, h₃⟩))
          · exact Or.inr (Or.inr h₃)
        · exact Or.inr (Or.inl h₂)
      · exact Or.inl h₁
    simp only [norm_mul]
    rcases hcases with hout | hout | hout
    · have h₁ := hModeᵣ t u m.val.1
      have h₂ := hMode₂ u v m.val.2.1
      have h₃ := hMode₂ v t m.val.2.2
      have hp := gmIntDecayProfile_add_two_le_of_outside (r := r) hout
      calc
        _ ≤ (Aᵣ * gmIntDecayProfile (r + 2) m.val.1) *
            (A₂ * gmIntDecayProfile 2 m.val.2.1) *
              (A₂ * gmIntDecayProfile 2 m.val.2.2) := by
          exact mul_le_mul (mul_le_mul h₁ h₂ (norm_nonneg _)
            (mul_nonneg hAᵣ (hprofile _ _))) h₃ (norm_nonneg _)
              (mul_nonneg (mul_nonneg hAᵣ (hprofile _ _))
                (mul_nonneg hA₂ (hprofile _ _)))
        _ ≤ (Aᵣ * (F * gmIntDecayProfile 2 m.val.1)) *
            (A₂ * gmIntDecayProfile 2 m.val.2.1) *
              (A₂ * gmIntDecayProfile 2 m.val.2.2) := by
          apply mul_le_mul_of_nonneg_right _ (mul_nonneg hA₂ (hprofile _ _))
          apply mul_le_mul_of_nonneg_right _ (mul_nonneg hA₂ (hprofile _ _))
          exact mul_le_mul_of_nonneg_left (by simpa [F] using hp) hAᵣ
        _ = Aᵣ * A₂ ^ 2 * F * gmTripleDecayProfile 2 m := by
          unfold gmTripleDecayProfile
          ring
    · have h₁ := hMode₂ t u m.val.1
      have h₂ := hModeᵣ u v m.val.2.1
      have h₃ := hMode₂ v t m.val.2.2
      have hp := gmIntDecayProfile_add_two_le_of_outside (r := r) hout
      calc
        _ ≤ (A₂ * gmIntDecayProfile 2 m.val.1) *
            (Aᵣ * gmIntDecayProfile (r + 2) m.val.2.1) *
              (A₂ * gmIntDecayProfile 2 m.val.2.2) := by
          exact mul_le_mul (mul_le_mul h₁ h₂ (norm_nonneg _)
            (mul_nonneg hA₂ (hprofile _ _))) h₃ (norm_nonneg _)
              (mul_nonneg (mul_nonneg hA₂ (hprofile _ _))
                (mul_nonneg hAᵣ (hprofile _ _)))
        _ ≤ (A₂ * gmIntDecayProfile 2 m.val.1) *
            (Aᵣ * (F * gmIntDecayProfile 2 m.val.2.1)) *
              (A₂ * gmIntDecayProfile 2 m.val.2.2) := by
          apply mul_le_mul_of_nonneg_right _ (mul_nonneg hA₂ (hprofile _ _))
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (by simpa [F] using hp) hAᵣ)
            (mul_nonneg hA₂ (hprofile _ _))
        _ = Aᵣ * A₂ ^ 2 * F * gmTripleDecayProfile 2 m := by
          unfold gmTripleDecayProfile
          ring
    · have h₁ := hMode₂ t u m.val.1
      have h₂ := hMode₂ u v m.val.2.1
      have h₃ := hModeᵣ v t m.val.2.2
      have hp := gmIntDecayProfile_add_two_le_of_outside (r := r) hout
      calc
        _ ≤ (A₂ * gmIntDecayProfile 2 m.val.1) *
            (A₂ * gmIntDecayProfile 2 m.val.2.1) *
              (Aᵣ * gmIntDecayProfile (r + 2) m.val.2.2) := by
          exact mul_le_mul (mul_le_mul h₁ h₂ (norm_nonneg _)
            (mul_nonneg hA₂ (hprofile _ _))) h₃ (norm_nonneg _)
              (mul_nonneg (mul_nonneg hA₂ (hprofile _ _))
                (mul_nonneg hA₂ (hprofile _ _)))
        _ ≤ (A₂ * gmIntDecayProfile 2 m.val.1) *
            (A₂ * gmIntDecayProfile 2 m.val.2.1) *
              (Aᵣ * (F * gmIntDecayProfile 2 m.val.2.2)) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (by simpa [F] using hp) hAᵣ)
            (mul_nonneg (mul_nonneg hA₂ (hprofile _ _))
              (mul_nonneg hA₂ (hprofile _ _)))
        _ = Aᵣ * A₂ ^ 2 * F * gmTripleDecayProfile 2 m := by
          unfold gmTripleDecayProfile
          ring
  have hModePoint (m : {m : ℤ × (ℤ × ℤ) // m ∉ gmCubicFrequencyBox H}) :
      ‖gmCubicS3Mode cutoff N W m‖ ≤ K * gmTripleDecayProfile 2 m := by
    unfold gmCubicS3Mode
    calc
      ‖∑ t : GMRow W, ∑ u : GMRow W, ∑ v : GMRow W, _‖ ≤
          ∑ t : GMRow W, ‖∑ u : GMRow W, ∑ v : GMRow W, _‖ := norm_sum_le _ _
      _ ≤ ∑ t : GMRow W, ∑ u : GMRow W, ‖∑ v : GMRow W, _‖ := by
        gcongr with t ht
        exact norm_sum_le _ _
      _ ≤ ∑ t : GMRow W, ∑ u : GMRow W, ∑ v : GMRow W, ‖_‖ := by
        gcongr with t ht u hu
        exact norm_sum_le _ _
      _ ≤ ∑ _t : GMRow W, ∑ _u : GMRow W, ∑ _v : GMRow W,
          Aᵣ * A₂ ^ 2 * F * gmTripleDecayProfile 2 m := by
        gcongr with t ht u hu v hv
        exact hTerm m t u v
      _ = K * gmTripleDecayProfile 2 m := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
        dsimp only [K]
        ring
  have hModeNorm : Summable (fun m :
      {m : ℤ × (ℤ × ℤ) // m ∉ gmCubicFrequencyBox H} =>
      ‖gmCubicS3Mode cutoff N W m‖) :=
    (gmCubicS3Mode_summable cutoff N hN W).norm.subtype _
  have hProfile : Summable (fun m :
      {m : ℤ × (ℤ × ℤ) // m ∉ gmCubicFrequencyBox H} =>
      gmTripleDecayProfile 2 m) :=
    (summable_gmTripleDecayProfile (by norm_num)).subtype _
  unfold gmCubicS3FrequencyTail
  calc
    ‖∑' m : {m : ℤ × (ℤ × ℤ) // m ∉ gmCubicFrequencyBox H},
        gmCubicS3Mode cutoff N W m‖ ≤
      ∑' m : {m : ℤ × (ℤ × ℤ) // m ∉ gmCubicFrequencyBox H},
        ‖gmCubicS3Mode cutoff N W m‖ :=
      norm_tsum_le_tsum_norm hModeNorm
    _ ≤ ∑' m : {m : ℤ × (ℤ × ℤ) // m ∉ gmCubicFrequencyBox H},
        K * gmTripleDecayProfile 2 m :=
      hModeNorm.tsum_le_tsum hModePoint (hProfile.mul_left K)
    _ = K * (∑' m : {m : ℤ × (ℤ × ℤ) // m ∉ gmCubicFrequencyBox H},
        gmTripleDecayProfile 2 m) := by rw [tsum_mul_left]
    _ ≤ K * B := by
      exact mul_le_mul_of_nonneg_left
        (Summable.tsum_subtype_le (gmTripleDecayProfile 2) _
          (gmTripleDecayProfile_nonneg 2)
          (summable_gmTripleDecayProfile (by norm_num))) hK
    _ = _ := by
      dsimp only [K, A₂, Aᵣ, F]

/-- The source truncation radius in Guth--Maynard (7.1).  Taking a natural
ceiling records the complete symmetric integer-frequency window without
silently discarding either endpoint. -/
noncomputable def gmCubicFrequencyRadius (η T : ℝ) (N : ℕ) : ℕ :=
  Nat.ceil (T ^ (1 + η) / (N : ℝ))

theorem ratio_le_gmCubicFrequencyRadius
    {η T : ℝ} {N : ℕ} :
    T ^ (1 + η) / (N : ℝ) ≤ (gmCubicFrequencyRadius η T N : ℝ) := by
  unfold gmCubicFrequencyRadius
  exact Nat.le_ceil _

theorem one_div_frequencyRadius_add_one_pow_le
    {η T : ℝ} {N r : ℕ} (hT : 0 < T) (hN : 0 < N) :
    1 / (((gmCubicFrequencyRadius η T N + 1 : ℕ) : ℝ) ^ r) ≤
      1 / ((T ^ (1 + η) / (N : ℝ)) ^ r) := by
  have hRatio : 0 < T ^ (1 + η) / (N : ℝ) := by positivity
  have hRadius : T ^ (1 + η) / (N : ℝ) ≤
      ((gmCubicFrequencyRadius η T N + 1 : ℕ) : ℝ) := by
    calc
      T ^ (1 + η) / (N : ℝ) ≤ (gmCubicFrequencyRadius η T N : ℝ) :=
        ratio_le_gmCubicFrequencyRadius
      _ ≤ ((gmCubicFrequencyRadius η T N + 1 : ℕ) : ℝ) := by
        norm_num
  exact one_div_le_one_div_of_le (pow_pos hRatio r)
    (pow_le_pow_left₀ hRatio.le hRadius r)

theorem gmCubicTail_scale_identity
    (η T C₂ Cᵣ B : ℝ) (N r : ℕ) (hT : 0 < T) (hN : 0 < N) :
    (8 * T ^ 3) *
          (Cᵣ * (2 * T) ^ (r + 2) / (N : ℝ) ^ (r + 1)) *
          (C₂ * (2 * T) ^ 2 / (N : ℝ)) ^ 2 *
          (1 / ((T ^ (1 + η) / (N : ℝ)) ^ r)) * B =
      (2 : ℝ) ^ (r + 9) * Cᵣ * C₂ ^ 2 * B *
        (T ^ (r + 9) /
          ((N : ℝ) ^ 3 * (T ^ (1 + η)) ^ r)) := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hScale : T ^ (1 + η) ≠ 0 := (Real.rpow_pos_of_pos hT _).ne'
  simp only [div_pow]
  field_simp
  simp only [mul_pow, pow_add]
  ring

theorem gmCubicTail_scale_ratio_le
    {η T : ℝ} {N r : ℕ} (hT : 1 ≤ T) (hN : 0 < N)
    (hr : 109 ≤ η * (r : ℝ)) :
    T ^ (r + 9) / ((N : ℝ) ^ 3 * (T ^ (1 + η)) ^ r) ≤
      1 / T ^ 100 := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hNOne : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNPow : (1 : ℝ) ≤ (N : ℝ) ^ 3 := by
    simpa using pow_le_pow_left₀ zero_le_one hNOne 3
  have hScalePos : 0 < (T ^ (1 + η)) ^ r := by positivity
  have hScalePower : T ^ (r + 109) ≤ (T ^ (1 + η)) ^ r := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast,
      ← Real.rpow_mul hTpos.le]
    apply Real.rpow_le_rpow_of_exponent_le hT
    push_cast
    nlinarith
  calc
    T ^ (r + 9) / ((N : ℝ) ^ 3 * (T ^ (1 + η)) ^ r) ≤
        T ^ (r + 9) / (T ^ (1 + η)) ^ r := by
      apply div_le_div_of_nonneg_left (by positivity) hScalePos
      nlinarith [mul_le_mul_of_nonneg_right hNPow hScalePos.le]
    _ ≤ T ^ (r + 9) / T ^ (r + 109) := by
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) hScalePower
    _ = 1 / T ^ 100 := by
      field_simp
      simp only [pow_add]
      ring

/-- Uniform `T⁻¹⁰⁰` control of the complete complementary frequency
series at the source radius `T^(1+η)/N`.  The proof selects a derivative
order depending only on `η`; all constants are uniform in `N`, `T`, and the
one-separated ordinate set. -/
theorem gmCubicS3_frequencyTail_pow_100
    (cutoff : GMSmoothCutoff) (η : ℝ) (hη : 0 < η) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ) (W : Finset ℝ) {T : ℝ},
      0 < N → 1 ≤ T → IsSeparated 1 W → InBaseInterval T W →
      ‖gmCubicS3FrequencyTail cutoff N
          (gmCubicFrequencyRadius η T N) W‖ ≤ K / T ^ 100 := by
  obtain ⟨r, hrRaw⟩ := exists_nat_gt (109 / η)
  have hr : 109 ≤ η * (r : ℝ) := by
    rw [div_lt_iff₀ hη] at hrRaw
    linarith
  obtain ⟨C₂, Cᵣ, B, hC₂, hCᵣ, hB, hTail⟩ :=
    exists_norm_gmCubicS3FrequencyTail_le_mixed cutoff r
  let K₀ : ℝ := (2 : ℝ) ^ (r + 9) * Cᵣ * C₂ ^ 2 * B
  refine ⟨K₀ + 1, by dsimp only [K₀]; positivity, ?_⟩
  intro N W T hN hT hSep hBase
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hCard := gmSeparated_card_le_two_height hT hSep hBase
  have hCardCube : (W.card : ℝ) ^ 3 ≤ 8 * T ^ 3 := by
    calc
      (W.card : ℝ) ^ 3 ≤ (2 * T) ^ 3 :=
        pow_le_pow_left₀ (by positivity) hCard 3
      _ = 8 * T ^ 3 := by ring
  have hTwoT : 1 + T ≤ 2 * T := by linarith
  have hRadius := one_div_frequencyRadius_add_one_pow_le
    (η := η) (T := T) (N := N) (r := r) hTpos hN
  have hRaw := hTail N (gmCubicFrequencyRadius η T N) hN hT hBase
  calc
    ‖gmCubicS3FrequencyTail cutoff N
        (gmCubicFrequencyRadius η T N) W‖ ≤
      (W.card : ℝ) ^ 3 *
        (Cᵣ * (1 + T) ^ (r + 2) / (N : ℝ) ^ (r + 1)) *
        (C₂ * (1 + T) ^ 2 / (N : ℝ)) ^ 2 *
        (1 / (((gmCubicFrequencyRadius η T N + 1 : ℕ) : ℝ) ^ r)) * B :=
      hRaw
    _ ≤ (8 * T ^ 3) *
        (Cᵣ * (2 * T) ^ (r + 2) / (N : ℝ) ^ (r + 1)) *
        (C₂ * (2 * T) ^ 2 / (N : ℝ)) ^ 2 *
        (1 / ((T ^ (1 + η) / (N : ℝ)) ^ r)) * B := by
      gcongr
    _ = K₀ *
        (T ^ (r + 9) / ((N : ℝ) ^ 3 * (T ^ (1 + η)) ^ r)) := by
      exact gmCubicTail_scale_identity η T C₂ Cᵣ B N r hTpos hN
    _ ≤ K₀ * (1 / T ^ 100) :=
      mul_le_mul_of_nonneg_left (gmCubicTail_scale_ratio_le hT hN hr)
        (by dsimp only [K₀]; positivity)
    _ ≤ (K₀ + 1) / T ^ 100 := by
      rw [mul_one_div]
      exact div_le_div_of_nonneg_right (by linarith)
        (pow_nonneg hTpos.le 100)

/-- Exact quantitative form of Guth--Maynard (7.1): the complete cubic
trace differs from the finite source-frequency box by `O_η(T⁻¹⁰⁰)`.
This theorem combines the exact Poisson partition with the full complementary
integer-frequency sum; it is not a finite-sum surrogate. -/
theorem gmCubicS3_source_truncation_pow_100
    (cutoff : GMSmoothCutoff) (η : ℝ) (hη : 0 < η) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ) (W : Finset ℝ) {T : ℝ},
      0 < N → 1 ≤ T → IsSeparated 1 W → InBaseInterval T W →
      ‖gmCubicS3 cutoff N W -
          gmCubicS3Truncated cutoff N
            (gmCubicFrequencyRadius η T N) W‖ ≤ K / T ^ 100 := by
  obtain ⟨K, hK, hTail⟩ := gmCubicS3_frequencyTail_pow_100 cutoff η hη
  refine ⟨K, hK, ?_⟩
  intro N W T hN hT hSep hBase
  rw [gmCubicS3_eq_truncated_add_frequencyTail cutoff N
    (gmCubicFrequencyRadius η T N) hN W, add_sub_cancel_left]
  exact hTail N W hN hT hSep hBase

/-! ## The exact Section 7 integral before localization -/

/-- Fourier oscillation in the normalization used by Mathlib and by the
Guth--Maynard Poisson formula. -/
noncomputable def gmTraceOscillation (ξ x : ℝ) : ℂ :=
  Complex.exp (((-2 * Real.pi * (x * ξ) : ℝ) : ℂ) * I)

@[simp]
theorem norm_gmTraceOscillation (ξ x : ℝ) :
    ‖gmTraceOscillation ξ x‖ = 1 := by
  simp [gmTraceOscillation, Complex.norm_exp]

theorem continuous_gmTraceOscillation (ξ : ℝ) :
    Continuous (gmTraceOscillation ξ) := by
  unfold gmTraceOscillation
  fun_prop

/-- Multiplication by the unit Fourier phase preserves integrability of the
compactly supported trace kernel. -/
theorem integrable_gmTraceOscillation_mul_kernel
    (cutoff : GMSmoothCutoff) (ξ t : ℝ) :
    Integrable (fun x : ℝ =>
      gmTraceOscillation ξ x * gmTraceKernel cutoff t x) := by
  have hk : Integrable (gmTraceKernel cutoff t) :=
    (gmTraceKernelSchwartz cutoff t).integrable
  apply hk.norm.mono'
  · exact ((continuous_gmTraceOscillation ξ).mul
      (contDiff_gmTraceKernel cutoff t).continuous).aestronglyMeasurable
  · filter_upwards with x
    simp

/-- Every scaled Poisson mode is the source oscillatory integral, with no
frequency truncation. -/
theorem gmScaledTraceMode_eq_integral (cutoff : GMSmoothCutoff) (N : ℕ)
    (t : ℝ) (m : ℤ) :
    gmScaledTraceMode cutoff N t m =
      (N : ℂ) * ∫ x : ℝ,
        gmTraceOscillation ((N : ℝ) * (m : ℝ)) x *
          gmTraceKernel cutoff t x := by
  unfold gmScaledTraceMode gmTraceFourier gmTraceOscillation
  rw [SchwartzMap.fourier_coe, Real.fourier_eq']
  simp only [Real.inner_apply, gmTraceKernelSchwartz_apply]
  congr 2

/-- The row-subtype version of the source exponential sum. -/
noncomputable def gmRPhaseRows (W : Finset ℝ) (x : ℝ) : ℂ :=
  ∑ t : GMRow W, Complex.exp ((((t : ℝ) * x : ℝ) : ℂ) * I)

theorem gmRPhaseRows_eq_gmRPhase (W : Finset ℝ) (x : ℝ) :
    gmRPhaseRows W x = gmRPhase W x := by
  unfold gmRPhaseRows gmRPhase
  conv_rhs => rw [← Finset.sum_attach]
  rw [Finset.univ_eq_attach W]

/-- The exact product of the three Mellin phases, regrouped by the three
ordinates.  This is the finite algebra behind equation (7.3). -/
theorem gmTraceKernel_cyclic_phase
    (cutoff : GMSmoothCutoff) (x y z : ℝ) (t u v : ℝ) :
    gmTraceKernel cutoff (t - u) x *
        gmTraceKernel cutoff (u - v) y *
          gmTraceKernel cutoff (v - t) z =
      ((cutoff x : ℂ) ^ 2 * (cutoff y : ℂ) ^ 2 * (cutoff z : ℂ) ^ 2) *
        Complex.exp (((t * (Real.log x - Real.log z) : ℝ) : ℂ) * I) *
        Complex.exp (((u * (Real.log y - Real.log x) : ℝ) : ℂ) * I) *
        Complex.exp (((v * (Real.log z - Real.log y) : ℝ) : ℂ) * I) := by
  have hphase :
      Complex.exp (((((t - u) * Real.log x : ℝ) : ℂ) * I)) *
          Complex.exp (((((u - v) * Real.log y : ℝ) : ℂ) * I)) *
            Complex.exp (((((v - t) * Real.log z : ℝ) : ℂ) * I)) =
        Complex.exp ((((t * (Real.log x - Real.log z) : ℝ) : ℂ) * I)) *
          Complex.exp ((((u * (Real.log y - Real.log x) : ℝ) : ℂ) * I)) *
            Complex.exp ((((v * (Real.log z - Real.log y) : ℝ) : ℂ) * I)) := by
    calc
      _ = Complex.exp (
          ((((t - u) * Real.log x : ℝ) : ℂ) * I) +
          ((((u - v) * Real.log y : ℝ) : ℂ) * I) +
          ((((v - t) * Real.log z : ℝ) : ℂ) * I)) := by
            rw [Complex.exp_add, Complex.exp_add]
      _ = Complex.exp (
          (((t * (Real.log x - Real.log z) : ℝ) : ℂ) * I) +
          (((u * (Real.log y - Real.log x) : ℝ) : ℂ) * I) +
          (((v * (Real.log z - Real.log y) : ℝ) : ℂ) * I)) := by
            congr 1
            push_cast
            ring
      _ = _ := by rw [Complex.exp_add, Complex.exp_add]
  calc
    gmTraceKernel cutoff (t - u) x *
          gmTraceKernel cutoff (u - v) y *
            gmTraceKernel cutoff (v - t) z =
        ((cutoff x : ℂ) ^ 2 * (cutoff y : ℂ) ^ 2 * (cutoff z : ℂ) ^ 2) *
          (Complex.exp (((((t - u) * Real.log x : ℝ) : ℂ) * I)) *
            Complex.exp (((((u - v) * Real.log y : ℝ) : ℂ) * I)) *
              Complex.exp (((((v - t) * Real.log z : ℝ) : ℂ) * I))) := by
            unfold gmTraceKernel
            ring
    _ = _ := by
      rw [hphase]
      ring

/-- The cyclic sum of the three physical trace kernels. -/
noncomputable def gmCubicTraceKernelSum (cutoff : GMSmoothCutoff)
    (W : Finset ℝ) (x y z : ℝ) : ℂ :=
  ∑ t : GMRow W, ∑ u : GMRow W, ∑ v : GMRow W,
    gmTraceKernel cutoff ((t : ℝ) - (u : ℝ)) x *
      gmTraceKernel cutoff ((u : ℝ) - (v : ℝ)) y *
        gmTraceKernel cutoff ((v : ℝ) - (t : ℝ)) z

/-- Equation (7.3), pointwise in the three source variables: the complete
ordinate sum is exactly the product of the three `R`-sums. -/
theorem gmCubicTraceKernelSum_eq (cutoff : GMSmoothCutoff)
    (W : Finset ℝ) (x y z : ℝ) :
    gmCubicTraceKernelSum cutoff W x y z =
      ((cutoff x : ℂ) ^ 2 * (cutoff y : ℂ) ^ 2 * (cutoff z : ℂ) ^ 2) *
        gmRPhase W (Real.log x - Real.log z) *
        gmRPhase W (Real.log y - Real.log x) *
        gmRPhase W (Real.log z - Real.log y) := by
  unfold gmCubicTraceKernelSum
  simp_rw [gmTraceKernel_cyclic_phase]
  rw [← gmRPhaseRows_eq_gmRPhase W (Real.log x - Real.log z),
    ← gmRPhaseRows_eq_gmRPhase W (Real.log y - Real.log x),
    ← gmRPhaseRows_eq_gmRPhase W (Real.log z - Real.log y)]
  unfold gmRPhaseRows
  calc
    (∑ t : GMRow W, ∑ u : GMRow W, ∑ v : GMRow W,
        ((cutoff x : ℂ) ^ 2 * (cutoff y : ℂ) ^ 2 * (cutoff z : ℂ) ^ 2) *
          Complex.exp ((((t : ℝ) * (Real.log x - Real.log z) : ℝ) : ℂ) * I) *
          Complex.exp ((((u : ℝ) * (Real.log y - Real.log x) : ℝ) : ℂ) * I) *
          Complex.exp ((((v : ℝ) * (Real.log z - Real.log y) : ℝ) : ℂ) * I)) =
      ((cutoff x : ℂ) ^ 2 * (cutoff y : ℂ) ^ 2 * (cutoff z : ℂ) ^ 2) *
        (∑ v : GMRow W,
          Complex.exp ((((v : ℝ) * (Real.log z - Real.log y) : ℝ) : ℂ) * I)) *
        (∑ u : GMRow W,
          Complex.exp ((((u : ℝ) * (Real.log y - Real.log x) : ℝ) : ℂ) * I)) *
        (∑ t : GMRow W,
          Complex.exp ((((t : ℝ) * (Real.log x - Real.log z) : ℝ) : ℂ) * I)) := by
            simp only [Finset.mul_sum, Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro t ht
            apply Finset.sum_congr rfl
            intro u hu
            apply Finset.sum_congr rfl
            intro v hv
            ring
    _ = _ := by ring

/-- The physical integrand attached to one ordered ordinate triple and one
ordered triple of nonzero Poisson frequencies. -/
noncomputable def gmCubicS3ModeIntegrand (cutoff : GMSmoothCutoff) (N : ℕ)
    (m : ℤ × (ℤ × ℤ)) (t u v : ℝ) (p : (ℝ × ℝ) × ℝ) : ℂ :=
  (gmTraceOscillation ((N : ℝ) * (m.1 : ℝ)) p.1.1 *
      gmTraceKernel cutoff (t - u) p.1.1) *
    (gmTraceOscillation ((N : ℝ) * (m.2.1 : ℝ)) p.1.2 *
      gmTraceKernel cutoff (u - v) p.1.2) *
    (gmTraceOscillation ((N : ℝ) * (m.2.2 : ℝ)) p.2 *
      gmTraceKernel cutoff (v - t) p.2)

theorem integrable_gmCubicS3ModeIntegrand (cutoff : GMSmoothCutoff)
    (N : ℕ) (m : ℤ × (ℤ × ℤ)) (t u v : ℝ) :
    Integrable (gmCubicS3ModeIntegrand cutoff N m t u v)
      ((volume.prod volume).prod volume) := by
  have h1 := integrable_gmTraceOscillation_mul_kernel cutoff
    ((N : ℝ) * (m.1 : ℝ)) (t - u)
  have h2 := integrable_gmTraceOscillation_mul_kernel cutoff
    ((N : ℝ) * (m.2.1 : ℝ)) (u - v)
  have h3 := integrable_gmTraceOscillation_mul_kernel cutoff
    ((N : ℝ) * (m.2.2 : ℝ)) (v - t)
  refine ((h1.mul_prod h2).mul_prod h3).congr ?_
  filter_upwards with p
  unfold gmCubicS3ModeIntegrand
  ring

/-- The three separate Fourier integrals are exactly the integral on
`ℝ³`; this is the Fubini/product-measure step in equation (7.3). -/
theorem gmScaledTraceMode_cyclic_product_eq_integral
    (cutoff : GMSmoothCutoff) (N : ℕ) (m : ℤ × (ℤ × ℤ))
    (t u v : ℝ) :
    gmScaledTraceMode cutoff N (t - u) m.1 *
        gmScaledTraceMode cutoff N (u - v) m.2.1 *
          gmScaledTraceMode cutoff N (v - t) m.2.2 =
      (N : ℂ) ^ 3 * ∫ p : (ℝ × ℝ) × ℝ,
        gmCubicS3ModeIntegrand cutoff N m t u v p := by
  rw [gmScaledTraceMode_eq_integral, gmScaledTraceMode_eq_integral,
    gmScaledTraceMode_eq_integral]
  unfold gmCubicS3ModeIntegrand
  let f : ℝ → ℂ := fun x =>
    gmTraceOscillation ((N : ℝ) * (m.1 : ℝ)) x *
      gmTraceKernel cutoff (t - u) x
  let g : ℝ → ℂ := fun x =>
    gmTraceOscillation ((N : ℝ) * (m.2.1 : ℝ)) x *
      gmTraceKernel cutoff (u - v) x
  let h : ℝ → ℂ := fun x =>
    gmTraceOscillation ((N : ℝ) * (m.2.2 : ℝ)) x *
      gmTraceKernel cutoff (v - t) x
  have hfg := MeasureTheory.integral_prod_mul (μ := volume) (ν := volume) f g
  have hfgh := MeasureTheory.integral_prod_mul
    (μ := volume.prod volume) (ν := volume)
    (fun q : ℝ × ℝ => f q.1 * g q.2) h
  change ((N : ℂ) * ∫ x, f x) * ((N : ℂ) * ∫ x, g x) *
      ((N : ℂ) * ∫ x, h x) =
    (N : ℂ) ^ 3 * ∫ p : (ℝ × ℝ) × ℝ,
      (f p.1.1 * g p.1.2) * h p.2
  simp only [Measure.volume_eq_prod]
  calc
    ((N : ℂ) * ∫ x, f x) * ((N : ℂ) * ∫ x, g x) *
        ((N : ℂ) * ∫ x, h x) =
      (N : ℂ) ^ 3 * (((∫ x, f x) * ∫ x, g x) * ∫ x, h x) := by ring
    _ = (N : ℂ) ^ 3 *
        ((∫ q : ℝ × ℝ, f q.1 * g q.2 ∂volume.prod volume) * ∫ x, h x) := by
      rw [← hfg]
    _ = (N : ℂ) ^ 3 *
        ∫ p : (ℝ × ℝ) × ℝ, (f p.1.1 * g p.1.2) * h p.2
          ∂(volume.prod volume).prod volume := by rw [← hfgh]

/-- Source product-integral presentation of one nonzero triple mode. -/
noncomputable def gmCubicS3ModeIntegral (cutoff : GMSmoothCutoff) (N : ℕ)
    (W : Finset ℝ) (m : ℤ × (ℤ × ℤ)) : ℂ :=
  (N : ℂ) ^ 3 * ∑ t : GMRow W, ∑ u : GMRow W, ∑ v : GMRow W,
    ∫ p : (ℝ × ℝ) × ℝ,
      gmCubicS3ModeIntegrand cutoff N m (t : ℝ) (u : ℝ) (v : ℝ) p

/-- Every genuinely nonzero frequency term in `gmCubicS3Mode` is exactly
its physical triple integral. -/
theorem gmCubicS3Mode_eq_integral (cutoff : GMSmoothCutoff) (N : ℕ)
    (W : Finset ℝ) (m : ℤ × (ℤ × ℤ))
    (hm1 : m.1 ≠ 0) (hm2 : m.2.1 ≠ 0) (hm3 : m.2.2 ≠ 0) :
    gmCubicS3Mode cutoff N W m = gmCubicS3ModeIntegral cutoff N W m := by
  unfold gmCubicS3Mode gmCubicS3ModeIntegral gmNonzeroScaledTraceMode
  simp only [if_neg hm1, if_neg hm2, if_neg hm3]
  simp_rw [gmScaledTraceMode_cyclic_product_eq_integral cutoff N m]
  simp only [Finset.mul_sum]

/-- The finite ordinate sum inside one physical three-frequency integral. -/
noncomputable def gmCubicS3ModeSummedIntegrand (cutoff : GMSmoothCutoff)
    (N : ℕ) (W : Finset ℝ) (m : ℤ × (ℤ × ℤ))
    (p : (ℝ × ℝ) × ℝ) : ℂ :=
  ∑ t : GMRow W, ∑ u : GMRow W, ∑ v : GMRow W,
    gmCubicS3ModeIntegrand cutoff N m (t : ℝ) (u : ℝ) (v : ℝ) p

private theorem integral_fintype_sum
    {ι α : Type*} [Fintype ι] [MeasurableSpace α]
    {μ : Measure α} {f : ι → α → ℂ}
    (hf : ∀ i, Integrable (f i) μ) :
    (∫ x, ∑ i, f i x ∂μ) = ∑ i, ∫ x, f i x ∂μ := by
  classical
  exact MeasureTheory.integral_finsetSum Finset.univ
    (fun i hi => hf i)

private theorem integrable_fintype_sum
    {ι α : Type*} [Fintype ι] [MeasurableSpace α]
    {μ : Measure α} {f : ι → α → ℂ}
    (hf : ∀ i, Integrable (f i) μ) :
    Integrable (fun x => ∑ i, f i x) μ := by
  classical
  have hs : ∀ s : Finset ι,
      Integrable (fun x => ∑ i ∈ s, f i x) μ := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
        simp_rw [Finset.sum_insert hi]
        exact (hf i).add ih
  simpa using hs Finset.univ

theorem integrable_gmCubicS3ModeSummedIntegrand
    (cutoff : GMSmoothCutoff) (N : ℕ) (W : Finset ℝ)
    (m : ℤ × (ℤ × ℤ)) :
    Integrable (gmCubicS3ModeSummedIntegrand cutoff N W m)
      ((volume.prod volume).prod volume) := by
  unfold gmCubicS3ModeSummedIntegrand
  apply integrable_fintype_sum
  intro t
  apply integrable_fintype_sum
  intro u
  apply integrable_fintype_sum
  intro v
  exact integrable_gmCubicS3ModeIntegrand cutoff N m (t : ℝ) (u : ℝ) (v : ℝ)

/-- All finite ordinate sums in `gmCubicS3ModeIntegral` pass through the
physical integral. -/
theorem gmCubicS3ModeIntegral_eq_integral_sum
    (cutoff : GMSmoothCutoff) (N : ℕ) (W : Finset ℝ)
    (m : ℤ × (ℤ × ℤ)) :
    gmCubicS3ModeIntegral cutoff N W m =
      (N : ℂ) ^ 3 * ∫ p : (ℝ × ℝ) × ℝ,
        gmCubicS3ModeSummedIntegrand cutoff N W m p := by
  unfold gmCubicS3ModeIntegral gmCubicS3ModeSummedIntegrand
  congr 1
  rw [integral_fintype_sum]
  · congr 1
    funext t
    rw [integral_fintype_sum]
    · congr 1
      funext u
      rw [integral_fintype_sum]
      intro v
      exact integrable_gmCubicS3ModeIntegrand cutoff N m
        (t : ℝ) (u : ℝ) (v : ℝ)
    · intro u
      apply integrable_fintype_sum
      intro v
      simpa only [Measure.volume_eq_prod] using
        integrable_gmCubicS3ModeIntegrand cutoff N m
          (t : ℝ) (u : ℝ) (v : ℝ)
  · intro t
    apply integrable_fintype_sum
    intro u
    apply integrable_fintype_sum
    intro v
    simpa only [Measure.volume_eq_prod] using
      integrable_gmCubicS3ModeIntegrand cutoff N m
        (t : ℝ) (u : ℝ) (v : ℝ)

/-- The product Fourier phase belonging to a triple integer frequency. -/
noncomputable def gmCubicFrequencyOscillation (N : ℕ)
    (m : ℤ × (ℤ × ℤ)) (p : (ℝ × ℝ) × ℝ) : ℂ :=
  gmTraceOscillation ((N : ℝ) * (m.1 : ℝ)) p.1.1 *
    gmTraceOscillation ((N : ℝ) * (m.2.1 : ℝ)) p.1.2 *
    gmTraceOscillation ((N : ℝ) * (m.2.2 : ℝ)) p.2

@[simp]
theorem norm_gmCubicFrequencyOscillation (N : ℕ)
    (m : ℤ × (ℤ × ℤ)) (p : (ℝ × ℝ) × ℝ) :
    ‖gmCubicFrequencyOscillation N m p‖ = 1 := by
  simp [gmCubicFrequencyOscillation]

/-- Before changing variables, the finite sum inside a triple mode is the
common Fourier phase times the cyclic trace-kernel sum. -/
theorem gmCubicS3ModeSummedIntegrand_eq_kernelSum
    (cutoff : GMSmoothCutoff) (N : ℕ) (W : Finset ℝ)
    (m : ℤ × (ℤ × ℤ)) (p : (ℝ × ℝ) × ℝ) :
    gmCubicS3ModeSummedIntegrand cutoff N W m p =
      gmCubicFrequencyOscillation N m p *
        gmCubicTraceKernelSum cutoff W p.1.1 p.1.2 p.2 := by
  unfold gmCubicS3ModeSummedIntegrand gmCubicFrequencyOscillation
  unfold gmCubicS3ModeIntegrand gmCubicTraceKernelSum
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  ring

/-- Exact equation (7.3) in the original three source variables, including
the cutoff, all three `R`-factors, and the complete Fourier phase. -/
theorem gmCubicS3ModeSummedIntegrand_eq_RPhase
    (cutoff : GMSmoothCutoff) (N : ℕ) (W : Finset ℝ)
    (m : ℤ × (ℤ × ℤ)) (p : (ℝ × ℝ) × ℝ) :
    gmCubicS3ModeSummedIntegrand cutoff N W m p =
      gmCubicFrequencyOscillation N m p *
        ((cutoff p.1.1 : ℂ) ^ 2 * (cutoff p.1.2 : ℂ) ^ 2 *
          (cutoff p.2 : ℂ) ^ 2) *
        gmRPhase W (Real.log p.1.1 - Real.log p.2) *
        gmRPhase W (Real.log p.1.2 - Real.log p.1.1) *
        gmRPhase W (Real.log p.2 - Real.log p.1.2) := by
  rw [gmCubicS3ModeSummedIntegrand_eq_kernelSum,
    gmCubicTraceKernelSum_eq]
  ring

/-- The compact physical cube forced by the three source cutoffs. -/
def gmCubicSourceCube : Set ((ℝ × ℝ) × ℝ) :=
  (Set.Ioc (1 : ℝ) 2 ×ˢ Set.Ioc (1 : ℝ) 2) ×ˢ Set.Ioc (1 : ℝ) 2

theorem measurableSet_gmCubicSourceCube : MeasurableSet gmCubicSourceCube :=
  (measurableSet_Ioc.prod measurableSet_Ioc).prod measurableSet_Ioc

/-- The Section 7 integrand vanishes identically outside the physical
cutoff cube. -/
theorem gmCubicS3ModeSummedIntegrand_eq_zero_of_not_mem_sourceCube
    (cutoff : GMSmoothCutoff) (N : ℕ) (W : Finset ℝ)
    (m : ℤ × (ℤ × ℤ)) {p : (ℝ × ℝ) × ℝ}
    (hp : p ∉ gmCubicSourceCube) :
    gmCubicS3ModeSummedIntegrand cutoff N W m p = 0 := by
  rw [gmCubicS3ModeSummedIntegrand_eq_RPhase]
  simp only [gmCubicSourceCube, Set.mem_prod, Set.mem_Ioc, not_and_or] at hp
  rcases hp with hp | hp
  · rcases hp with hp | hp
    · have hx : cutoff p.1.1 = 0 := by
        rcases hp with hp | hp
        · exact gmSmoothCutoff_eq_zero_of_le_one cutoff (not_lt.mp hp)
        · exact gmSmoothCutoff_eq_zero_of_two_le cutoff
            (le_of_lt (lt_of_not_ge hp))
      simp [hx]
    · have hy : cutoff p.1.2 = 0 := by
        rcases hp with hp | hp
        · exact gmSmoothCutoff_eq_zero_of_le_one cutoff (not_lt.mp hp)
        · exact gmSmoothCutoff_eq_zero_of_two_le cutoff
            (le_of_lt (lt_of_not_ge hp))
      simp [hy]
  · have hz : cutoff p.2 = 0 := by
      rcases hp with hp | hp
      · exact gmSmoothCutoff_eq_zero_of_le_one cutoff (not_lt.mp hp)
      · exact gmSmoothCutoff_eq_zero_of_two_le cutoff
          (le_of_lt (lt_of_not_ge hp))
    simp [hz]

/-- The whole-space triple integral is exactly the integral over the source
cube; no tail estimate is used here. -/
theorem integral_gmCubicS3ModeSummedIntegrand_eq_sourceCube
    (cutoff : GMSmoothCutoff) (N : ℕ) (W : Finset ℝ)
    (m : ℤ × (ℤ × ℤ)) :
    (∫ p : (ℝ × ℝ) × ℝ,
        gmCubicS3ModeSummedIntegrand cutoff N W m p) =
      ∫ p in gmCubicSourceCube,
        gmCubicS3ModeSummedIntegrand cutoff N W m p := by
  rw [← MeasureTheory.integral_indicator measurableSet_gmCubicSourceCube]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with p
  by_cases hp : p ∈ gmCubicSourceCube
  · simp [Set.indicator_of_mem hp]
  · rw [gmCubicS3ModeSummedIntegrand_eq_zero_of_not_mem_sourceCube
      cutoff N W m hp]
    simp [hp]

/-! ## Ratio coordinates for Proposition 7.1 -/

/-- The source substitution `(u₁,u₂,u₃)=(v₁z,v₂z,z)`. -/
def gmCubicRatioMap (q : (ℝ × ℝ) × ℝ) : (ℝ × ℝ) × ℝ :=
  ((q.1.1 * q.2, q.1.2 * q.2), q.2)

/-- The three Fourier phases combine into the single linear phase used in
the Section 7 slab. -/
theorem gmCubicFrequencyOscillation_ratioMap
    (N : ℕ) (m : ℤ × (ℤ × ℤ)) (v₁ v₂ z : ℝ) :
    gmCubicFrequencyOscillation N m ((v₁ * z, v₂ * z), z) =
      gmTraceOscillation
        ((N : ℝ) * ((m.1 : ℝ) * v₁ + (m.2.1 : ℝ) * v₂ +
          (m.2.2 : ℝ))) z := by
  unfold gmCubicFrequencyOscillation gmTraceOscillation
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Exact Jacobian-weighted integrand in ratio coordinates. -/
noncomputable def gmCubicRatioIntegrand (cutoff : GMSmoothCutoff)
    (N : ℕ) (W : Finset ℝ) (m : ℤ × (ℤ × ℤ))
    (q : (ℝ × ℝ) × ℝ) : ℂ :=
  (q.2 ^ 2 : ℝ) *
    gmTraceOscillation
      ((N : ℝ) * ((m.1 : ℝ) * q.1.1 + (m.2.1 : ℝ) * q.1.2 +
        (m.2.2 : ℝ))) q.2 *
    ((cutoff (q.1.1 * q.2) : ℂ) ^ 2 *
      (cutoff (q.1.2 * q.2) : ℂ) ^ 2 * (cutoff q.2 : ℂ) ^ 2) *
    gmR W q.1.1 * gmR W (q.1.2 / q.1.1) * gmR W (1 / q.1.2)

/-- Pointwise form of equation (7.3) after the source substitution. -/
theorem gmCubicS3ModeSummedIntegrand_ratioMap
    (cutoff : GMSmoothCutoff) (N : ℕ) (W : Finset ℝ)
    (m : ℤ × (ℤ × ℤ)) {v₁ v₂ z : ℝ}
    (hv₁ : 0 < v₁) (hv₂ : 0 < v₂) (hz : 0 < z) :
    ((z ^ 2 : ℝ) : ℂ) *
        gmCubicS3ModeSummedIntegrand cutoff N W m
          (gmCubicRatioMap ((v₁, v₂), z)) =
      gmCubicRatioIntegrand cutoff N W m ((v₁, v₂), z) := by
  rw [gmCubicS3ModeSummedIntegrand_eq_RPhase]
  unfold gmCubicRatioMap gmCubicRatioIntegrand
  simp only
  rw [gmCubicFrequencyOscillation_ratioMap]
  have hz0 : z ≠ 0 := hz.ne'
  have hv10 : v₁ ≠ 0 := hv₁.ne'
  have hv20 : v₂ ≠ 0 := hv₂.ne'
  rw [Real.log_mul hv10 hz0, Real.log_mul hv20 hz0]
  rw [show Real.log v₁ + Real.log z - Real.log z = Real.log v₁ by ring]
  rw [show Real.log v₂ + Real.log z - (Real.log v₁ + Real.log z) =
      Real.log v₂ - Real.log v₁ by ring]
  rw [show Real.log z - (Real.log v₂ + Real.log z) = -Real.log v₂ by ring]
  rw [← Real.log_div hv20 hv10]
  rw [show -Real.log v₂ = Real.log (1 / v₂) by
    rw [Real.log_div one_ne_zero hv20, Real.log_one]; ring]
  have hR1 : gmR W v₁ = gmRPhase W (Real.log v₁) := by
    simpa [abs_of_pos hv₁] using gmR_eq_gmRPhase_log (W := W) hv10
  have hR2 : gmR W (v₂ / v₁) = gmRPhase W (Real.log (v₂ / v₁)) := by
    simpa [abs_of_pos (div_pos hv₂ hv₁)] using
      gmR_eq_gmRPhase_log (W := W) (div_ne_zero hv20 hv10)
  have hR3 : gmR W (1 / v₂) = gmRPhase W (Real.log (1 / v₂)) := by
    simpa [abs_of_pos (div_pos zero_lt_one hv₂)] using
      gmR_eq_gmRPhase_log (W := W) (div_ne_zero one_ne_zero hv20)
  rw [← hR1, ← hR2, ← hR3]
  push_cast
  ring

/-- One-dimensional positive scaling, written in the direction used twice
in the ratio-coordinate substitution. -/
theorem complex_mul_integral_comp_mul_left
    (F : ℝ → ℂ) {z : ℝ} (hz : 0 < z) :
    (z : ℂ) * (∫ v : ℝ, F (z * v)) = ∫ x : ℝ, F x := by
  rw [Measure.integral_comp_mul_left F z]
  rw [abs_of_pos (inv_pos.mpr hz)]
  change (z : ℂ) * ((z⁻¹ : ℝ) • (∫ x : ℝ, F x)) = ∫ x : ℝ, F x
  simp [hz.ne']

/-- Applying the positive scaling in two coordinates produces the exact
`z²` Jacobian. -/
theorem complex_sq_mul_integral_integral_comp_mul_left
    (F : ℝ → ℝ → ℂ) {z : ℝ} (hz : 0 < z) :
    ((z ^ 2 : ℝ) : ℂ) * (∫ v₁ : ℝ, ∫ v₂ : ℝ, F (z * v₁) (z * v₂)) =
      ∫ x : ℝ, ∫ y : ℝ, F x y := by
  have hy (x : ℝ) := complex_mul_integral_comp_mul_left (F x) hz
  have hx := complex_mul_integral_comp_mul_left
    (fun x : ℝ => ∫ y : ℝ, F x y) hz
  calc
    ((z ^ 2 : ℝ) : ℂ) * (∫ v₁ : ℝ, ∫ v₂ : ℝ, F (z * v₁) (z * v₂)) =
      (z : ℂ) * (∫ v₁ : ℝ, (z : ℂ) * ∫ v₂ : ℝ,
        F (z * v₁) (z * v₂)) := by
          rw [MeasureTheory.integral_const_mul]
          push_cast
          ring
    _ = (z : ℂ) * (∫ v₁ : ℝ, ∫ y : ℝ, F (z * v₁) y) := by
      congr 1
      apply MeasureTheory.integral_congr_ae
      filter_upwards with v₁
      exact hy (z * v₁)
    _ = _ := hx

/-- The ratio-map identity holds for every pair of ratio variables once the
outer scale is positive; outside the positive quadrant both sides vanish by
cutoff support. -/
theorem gmCubicS3ModeSummedIntegrand_ratioMap_all
    (cutoff : GMSmoothCutoff) (N : ℕ) (W : Finset ℝ)
    (m : ℤ × (ℤ × ℤ)) (v₁ v₂ : ℝ) {z : ℝ} (hz : 0 < z) :
    ((z ^ 2 : ℝ) : ℂ) *
        gmCubicS3ModeSummedIntegrand cutoff N W m
          (gmCubicRatioMap ((v₁, v₂), z)) =
      gmCubicRatioIntegrand cutoff N W m ((v₁, v₂), z) := by
  by_cases hv₁ : 0 < v₁
  · by_cases hv₂ : 0 < v₂
    · exact gmCubicS3ModeSummedIntegrand_ratioMap cutoff N W m hv₁ hv₂ hz
    · have hcut : cutoff (v₂ * z) = 0 :=
        gmSmoothCutoff_eq_zero_of_le_one cutoff
          (by have := not_lt.mp hv₂; nlinarith)
      rw [gmCubicS3ModeSummedIntegrand_eq_RPhase]
      simp [gmCubicRatioMap, gmCubicRatioIntegrand, hcut]
  · have hcut : cutoff (v₁ * z) = 0 :=
      gmSmoothCutoff_eq_zero_of_le_one cutoff
        (by have := not_lt.mp hv₁; nlinarith)
    rw [gmCubicS3ModeSummedIntegrand_eq_RPhase]
    simp [gmCubicRatioMap, gmCubicRatioIntegrand, hcut]

theorem integrable_gmCubicS3ModeSummedIntegrand_slice
    (cutoff : GMSmoothCutoff) (N : ℕ) (W : Finset ℝ)
    (m : ℤ × (ℤ × ℤ)) (z : ℝ) :
    Integrable (fun q : ℝ × ℝ =>
      gmCubicS3ModeSummedIntegrand cutoff N W m (q, z))
      (volume.prod volume) := by
  unfold gmCubicS3ModeSummedIntegrand
  apply integrable_fintype_sum
  intro t
  apply integrable_fintype_sum
  intro u
  apply integrable_fintype_sum
  intro v
  have h1 := integrable_gmTraceOscillation_mul_kernel cutoff
    ((N : ℝ) * (m.1 : ℝ)) ((t : ℝ) - (u : ℝ))
  have h2 := integrable_gmTraceOscillation_mul_kernel cutoff
    ((N : ℝ) * (m.2.1 : ℝ)) ((u : ℝ) - (v : ℝ))
  let c : ℂ := gmTraceOscillation ((N : ℝ) * (m.2.2 : ℝ)) z *
    gmTraceKernel cutoff ((v : ℝ) - (t : ℝ)) z
  refine ((h1.mul_prod h2).mul_const c).congr ?_
  filter_upwards with q
  unfold gmCubicS3ModeIntegrand c
  ring

theorem continuous_gmCubicS3ModeIntegrand (cutoff : GMSmoothCutoff)
    (N : ℕ) (m : ℤ × (ℤ × ℤ)) (t u v : ℝ) :
    Continuous (gmCubicS3ModeIntegrand cutoff N m t u v) := by
  unfold gmCubicS3ModeIntegrand
  have hx : Continuous (fun p : (ℝ × ℝ) × ℝ => p.1.1) :=
    continuous_fst.comp continuous_fst
  have hy : Continuous (fun p : (ℝ × ℝ) × ℝ => p.1.2) :=
    continuous_snd.comp continuous_fst
  have hz : Continuous (fun p : (ℝ × ℝ) × ℝ => p.2) := continuous_snd
  exact ((((continuous_gmTraceOscillation _).comp hx).mul
      ((contDiff_gmTraceKernel cutoff (t - u)).continuous.comp hx)).mul
    (((continuous_gmTraceOscillation _).comp hy).mul
      ((contDiff_gmTraceKernel cutoff (u - v)).continuous.comp hy))).mul
    (((continuous_gmTraceOscillation _).comp hz).mul
      ((contDiff_gmTraceKernel cutoff (v - t)).continuous.comp hz))

private theorem continuous_fintype_sum
    {ι α : Type*} [Fintype ι] [TopologicalSpace α]
    {f : ι → α → ℂ} (hf : ∀ i, Continuous (f i)) :
    Continuous (fun x => ∑ i, f i x) := by
  classical
  fun_prop

theorem continuous_gmCubicS3ModeSummedIntegrand
    (cutoff : GMSmoothCutoff) (N : ℕ) (W : Finset ℝ)
    (m : ℤ × (ℤ × ℤ)) :
    Continuous (gmCubicS3ModeSummedIntegrand cutoff N W m) := by
  unfold gmCubicS3ModeSummedIntegrand
  apply continuous_fintype_sum
  intro t
  apply continuous_fintype_sum
  intro u
  apply continuous_fintype_sum
  intro v
  exact continuous_gmCubicS3ModeIntegrand cutoff N m (t : ℝ) (u : ℝ) (v : ℝ)

/-- The two positive rescalings convert the source slice exactly into the
ratio-coordinate slice. -/
theorem integral_integral_gmCubicS3ModeSummedIntegrand_eq_ratio
    (cutoff : GMSmoothCutoff) (N : ℕ) (W : Finset ℝ)
    (m : ℤ × (ℤ × ℤ)) {z : ℝ} (hz : 0 < z) :
    (∫ x : ℝ, ∫ y : ℝ,
        gmCubicS3ModeSummedIntegrand cutoff N W m ((x, y), z)) =
      ∫ v₁ : ℝ, ∫ v₂ : ℝ,
        gmCubicRatioIntegrand cutoff N W m ((v₁, v₂), z) := by
  let F : ℝ → ℝ → ℂ := fun x y =>
    gmCubicS3ModeSummedIntegrand cutoff N W m ((x, y), z)
  have hscale := complex_sq_mul_integral_integral_comp_mul_left F hz
  calc
    (∫ x : ℝ, ∫ y : ℝ,
        gmCubicS3ModeSummedIntegrand cutoff N W m ((x, y), z)) =
      ((z ^ 2 : ℝ) : ℂ) *
        (∫ v₁ : ℝ, ∫ v₂ : ℝ,
          gmCubicS3ModeSummedIntegrand cutoff N W m
            ((z * v₁, z * v₂), z)) := hscale.symm
    _ = ∫ v₁ : ℝ, ((z ^ 2 : ℝ) : ℂ) *
        (∫ v₂ : ℝ, gmCubicS3ModeSummedIntegrand cutoff N W m
          ((z * v₁, z * v₂), z)) := by
            rw [MeasureTheory.integral_const_mul]
    _ = ∫ v₁ : ℝ, ∫ v₂ : ℝ, ((z ^ 2 : ℝ) : ℂ) *
        gmCubicS3ModeSummedIntegrand cutoff N W m
          ((z * v₁, z * v₂), z) := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with v₁
            rw [MeasureTheory.integral_const_mul]
    _ = _ := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with v₁
      apply MeasureTheory.integral_congr_ae
      filter_upwards with v₂
      convert gmCubicS3ModeSummedIntegrand_ratioMap_all
        cutoff N W m v₁ v₂ hz using 1
      all_goals simp [gmCubicRatioMap, mul_comm]

theorem integral_integral_gmCubicS3ModeSummedIntegrand_eq_ratio_all
    (cutoff : GMSmoothCutoff) (N : ℕ) (W : Finset ℝ)
    (m : ℤ × (ℤ × ℤ)) (z : ℝ) :
    (∫ x : ℝ, ∫ y : ℝ,
        gmCubicS3ModeSummedIntegrand cutoff N W m ((x, y), z)) =
      ∫ v₁ : ℝ, ∫ v₂ : ℝ,
        gmCubicRatioIntegrand cutoff N W m ((v₁, v₂), z) := by
  by_cases hz : 0 < z
  · exact integral_integral_gmCubicS3ModeSummedIntegrand_eq_ratio
      cutoff N W m hz
  · have hcut : cutoff z = 0 :=
      gmSmoothCutoff_eq_zero_of_le_one cutoff
        (by have := not_lt.mp hz; linarith)
    have hs (x y : ℝ) :
        gmCubicS3ModeSummedIntegrand cutoff N W m ((x, y), z) = 0 := by
      rw [gmCubicS3ModeSummedIntegrand_eq_RPhase]
      simp [hcut]
    have hr (v₁ v₂ : ℝ) :
        gmCubicRatioIntegrand cutoff N W m ((v₁, v₂), z) = 0 := by
      simp [gmCubicRatioIntegrand, hcut]
    simp_rw [hs, hr]

/-- The exact ratio-coordinate integral representing one nonzero frequency
triple after equation (7.3). -/
noncomputable def gmCubicS3RatioIntegral (cutoff : GMSmoothCutoff)
    (N : ℕ) (W : Finset ℝ) (m : ℤ × (ℤ × ℤ)) : ℂ :=
  (N : ℂ) ^ 3 * ∫ z : ℝ, ∫ v₁ : ℝ, ∫ v₂ : ℝ,
    gmCubicRatioIntegrand cutoff N W m ((v₁, v₂), z)

/-- Exact source-to-ratio change of variables for one nonzero cubic mode. -/
theorem gmCubicS3ModeIntegral_eq_ratioIntegral
    (cutoff : GMSmoothCutoff) (N : ℕ) (W : Finset ℝ)
    (m : ℤ × (ℤ × ℤ)) :
    gmCubicS3ModeIntegral cutoff N W m =
      gmCubicS3RatioIntegral cutoff N W m := by
  rw [gmCubicS3ModeIntegral_eq_integral_sum]
  unfold gmCubicS3RatioIntegral
  congr 1
  have hall := integrable_gmCubicS3ModeSummedIntegrand cutoff N W m
  change (∫ p : (ℝ × ℝ) × ℝ,
      gmCubicS3ModeSummedIntegrand cutoff N W m p
        ∂(volume.prod volume).prod volume) = _
  rw [MeasureTheory.integral_prod_symm _ hall]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with z
  rw [MeasureTheory.integral_prod _
    (integrable_gmCubicS3ModeSummedIntegrand_slice cutoff N W m z)]
  exact integral_integral_gmCubicS3ModeSummedIntegrand_eq_ratio_all
    cutoff N W m z

/-! ## The one-dimensional stationary slab -/

/-- Compact smooth amplitude in the remaining scale variable `z`. -/
noncomputable def gmCubicZWeight (cutoff : GMSmoothCutoff)
    (v₁ v₂ z : ℝ) : ℂ :=
  ((z ^ 2 : ℝ) : ℂ) * (cutoff (v₁ * z) : ℂ) ^ 2 *
    (cutoff (v₂ * z) : ℂ) ^ 2 * (cutoff z : ℂ) ^ 2

theorem contDiff_gmCubicZWeight (cutoff : GMSmoothCutoff) (v₁ v₂ : ℝ) :
    ContDiff ℝ ∞ (gmCubicZWeight cutoff v₁ v₂) := by
  have hzReal : ContDiff ℝ ∞ (fun z : ℝ => z ^ 2) := contDiff_id.pow 2
  have hz : ContDiff ℝ ∞ (fun z : ℝ => ((z ^ 2 : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hzReal
  have h1r : ContDiff ℝ ∞ (fun z : ℝ => cutoff (v₁ * z)) :=
    cutoff.smooth.comp (contDiff_const.mul contDiff_id)
  have h2r : ContDiff ℝ ∞ (fun z : ℝ => cutoff (v₂ * z)) :=
    cutoff.smooth.comp (contDiff_const.mul contDiff_id)
  have h0r : ContDiff ℝ ∞ cutoff := cutoff.smooth
  have h1 : ContDiff ℝ ∞ (fun z : ℝ => (cutoff (v₁ * z) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp h1r
  have h2 : ContDiff ℝ ∞ (fun z : ℝ => (cutoff (v₂ * z) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp h2r
  have h0 : ContDiff ℝ ∞ (fun z : ℝ => (cutoff z : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp h0r
  exact ((hz.mul (h1.pow 2)).mul (h2.pow 2)).mul (h0.pow 2)

theorem hasCompactSupport_gmCubicZWeight (cutoff : GMSmoothCutoff)
    (v₁ v₂ : ℝ) : HasCompactSupport (gmCubicZWeight cutoff v₁ v₂) := by
  apply HasCompactSupport.intro isCompact_Icc
  intro z hz
  have hcut : cutoff z = 0 := by
    by_contra hne
    exact hz (cutoff.support hne)
  simp [gmCubicZWeight, hcut]

/-- The scale amplitude as an actual Schwartz function. -/
noncomputable def gmCubicZWeightSchwartz (cutoff : GMSmoothCutoff)
    (v₁ v₂ : ℝ) : 𝓢(ℝ, ℂ) :=
  (hasCompactSupport_gmCubicZWeight cutoff v₁ v₂).toSchwartzMap
    (contDiff_gmCubicZWeight cutoff v₁ v₂)

@[simp]
theorem gmCubicZWeightSchwartz_apply (cutoff : GMSmoothCutoff)
    (v₁ v₂ z : ℝ) :
    gmCubicZWeightSchwartz cutoff v₁ v₂ z =
      gmCubicZWeight cutoff v₁ v₂ z := rfl

/-- Fourier transform of the remaining compact scale amplitude. -/
noncomputable def gmCubicZFourier (cutoff : GMSmoothCutoff)
    (v₁ v₂ ξ : ℝ) : ℂ :=
  𝓕 (gmCubicZWeightSchwartz cutoff v₁ v₂) ξ

theorem gmCubicZFourier_eq_integral (cutoff : GMSmoothCutoff)
    (v₁ v₂ ξ : ℝ) :
    gmCubicZFourier cutoff v₁ v₂ ξ =
      ∫ z : ℝ, gmTraceOscillation ξ z *
        gmCubicZWeight cutoff v₁ v₂ z := by
  unfold gmCubicZFourier gmTraceOscillation
  rw [SchwartzMap.fourier_coe, Real.fourier_eq']
  simp only [Real.inner_apply, gmCubicZWeightSchwartz_apply]
  congr 2

/-! ### Uniform Fourier decay in the cancellation variable -/

/-- The squared cutoff, separated out so its scaled derivatives can be
bounded uniformly over the compact ratio box. -/
noncomputable def gmCubicCutoffSq (cutoff : GMSmoothCutoff) (z : ℝ) : ℂ :=
  (cutoff z : ℂ) ^ 2

theorem contDiff_gmCubicCutoffSq (cutoff : GMSmoothCutoff) :
    ContDiff ℝ ∞ (gmCubicCutoffSq cutoff) :=
  (Complex.ofRealCLM.contDiff.comp cutoff.smooth).pow 2

theorem hasCompactSupport_gmCubicCutoffSq (cutoff : GMSmoothCutoff) :
    HasCompactSupport (gmCubicCutoffSq cutoff) := by
  apply HasCompactSupport.intro isCompact_Icc
  intro z hz
  have hcut : cutoff z = 0 := by
    by_contra hne
    exact hz (cutoff.support hne)
  simp [gmCubicCutoffSq, hcut]

/-- The `gmCubicCutoffSqSchwartz` definition used by the source-facing construction in `LargeValuesS3`. -/
noncomputable def gmCubicCutoffSqSchwartz (cutoff : GMSmoothCutoff) :
    𝓢(ℝ, ℂ) :=
  (hasCompactSupport_gmCubicCutoffSq cutoff).toSchwartzMap
    (contDiff_gmCubicCutoffSq cutoff)

@[simp]
theorem gmCubicCutoffSqSchwartz_apply (cutoff : GMSmoothCutoff) (z : ℝ) :
    gmCubicCutoffSqSchwartz cutoff z = gmCubicCutoffSq cutoff z := rfl

/-- The unscaled compact factor `z² w(z)²`. -/
noncomputable def gmCubicBaseWeight (cutoff : GMSmoothCutoff) (z : ℝ) : ℂ :=
  ((z ^ 2 : ℝ) : ℂ) * gmCubicCutoffSq cutoff z

theorem contDiff_gmCubicBaseWeight (cutoff : GMSmoothCutoff) :
    ContDiff ℝ ∞ (gmCubicBaseWeight cutoff) := by
  unfold gmCubicBaseWeight
  have hzReal : ContDiff ℝ ∞ (fun z : ℝ => z ^ 2) := contDiff_id.pow 2
  have hz : ContDiff ℝ ∞ (fun z : ℝ => ((z ^ 2 : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hzReal
  exact hz.mul (contDiff_gmCubicCutoffSq cutoff)

theorem hasCompactSupport_gmCubicBaseWeight (cutoff : GMSmoothCutoff) :
    HasCompactSupport (gmCubicBaseWeight cutoff) := by
  apply (hasCompactSupport_gmCubicCutoffSq cutoff).mul_left

/-- The `gmCubicBaseWeightSchwartz` definition used by the source-facing construction in `LargeValuesS3`. -/
noncomputable def gmCubicBaseWeightSchwartz (cutoff : GMSmoothCutoff) :
    𝓢(ℝ, ℂ) :=
  (hasCompactSupport_gmCubicBaseWeight cutoff).toSchwartzMap
    (contDiff_gmCubicBaseWeight cutoff)

@[simp]
theorem gmCubicBaseWeightSchwartz_apply (cutoff : GMSmoothCutoff) (z : ℝ) :
    gmCubicBaseWeightSchwartz cutoff z = gmCubicBaseWeight cutoff z := rfl

theorem norm_iteratedDeriv_gmCubicBaseWeight_le
    (cutoff : GMSmoothCutoff) (n : ℕ) (z : ℝ) :
    ‖iteratedDeriv n (gmCubicBaseWeight cutoff) z‖ ≤
      SchwartzMap.seminorm ℝ 0 n (gmCubicBaseWeightSchwartz cutoff) := by
  have h := SchwartzMap.le_seminorm' (𝕜 := ℝ) 0 n
    (gmCubicBaseWeightSchwartz cutoff) z
  simp only [pow_zero, one_mul] at h
  change ‖iteratedDeriv n (gmCubicBaseWeight cutoff) z‖ ≤ _ at h
  exact h

theorem norm_iteratedDeriv_gmCubicCutoffSq_scaled_le
    (cutoff : GMSmoothCutoff) (n : ℕ) {v : ℝ} (hv : |v| ≤ 2) (z : ℝ) :
    ‖iteratedDeriv n (fun y : ℝ => gmCubicCutoffSq cutoff (v * y)) z‖ ≤
      (2 : ℝ) ^ n *
        SchwartzMap.seminorm ℝ 0 n (gmCubicCutoffSqSchwartz cutoff) := by
  have hcomp := congrFun (iteratedDeriv_comp_const_smul
    ((contDiff_gmCubicCutoffSq cutoff).of_le
      (WithTop.coe_le_coe.mpr (le_of_lt (ENat.coe_lt_top n)))) v) z
  rw [hcomp, norm_smul, norm_pow]
  have hcut := SchwartzMap.le_seminorm' (𝕜 := ℝ) 0 n
    (gmCubicCutoffSqSchwartz cutoff) (v * z)
  simp only [pow_zero, one_mul] at hcut
  change ‖iteratedDeriv n (gmCubicCutoffSq cutoff) (v * z)‖ ≤ _ at hcut
  have hvpow : ‖v‖ ^ n ≤ (2 : ℝ) ^ n := by
    rw [Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg v) hv n
  exact mul_le_mul hvpow hcut (norm_nonneg _)
    (by positivity)

theorem gmCubicZWeight_eq_base_mul_scaled
    (cutoff : GMSmoothCutoff) (v₁ v₂ z : ℝ) :
    gmCubicZWeight cutoff v₁ v₂ z =
      gmCubicBaseWeight cutoff z *
        gmCubicCutoffSq cutoff (v₁ * z) *
          gmCubicCutoffSq cutoff (v₂ * z) := by
  unfold gmCubicZWeight gmCubicBaseWeight gmCubicCutoffSq
  ring

/-- Explicit compact-parameter derivative majorant for the three-factor
scale weight.  Keeping the two Leibniz sums visible makes the constant's
dependence on the fixed cutoff and derivative order completely explicit. -/
noncomputable def gmCubicZDerivativeBound
    (cutoff : GMSmoothCutoff) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
    (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) *
      SchwartzMap.seminorm ℝ 0 j (gmCubicBaseWeightSchwartz cutoff) *
      ((2 : ℝ) ^ (i - j) *
        SchwartzMap.seminorm ℝ 0 (i - j) (gmCubicCutoffSqSchwartz cutoff))) *
    ((2 : ℝ) ^ (n - i) *
      SchwartzMap.seminorm ℝ 0 (n - i) (gmCubicCutoffSqSchwartz cutoff))

theorem gmCubicZDerivativeBound_nonneg
    (cutoff : GMSmoothCutoff) (n : ℕ) :
    0 ≤ gmCubicZDerivativeBound cutoff n := by
  unfold gmCubicZDerivativeBound
  positivity

private theorem norm_iteratedDeriv_mul_le_sum
    (n : ℕ) (f g : ℝ → ℂ) (x : ℝ)
    (F G : ℕ → ℝ)
    (hf : ContDiffAt ℝ n f x) (hg : ContDiffAt ℝ n g x)
    (hF : ∀ k, 0 ≤ F k)
    (hfBound : ∀ k, k ≤ n → ‖iteratedDeriv k f x‖ ≤ F k)
    (hgBound : ∀ k, k ≤ n → ‖iteratedDeriv k g x‖ ≤ G k) :
    ‖iteratedDeriv n (f * g) x‖ ≤
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * F k * G (n - k) := by
  rw [iteratedDeriv_mul hf hg]
  calc
    ‖∑ k ∈ Finset.range (n + 1),
        (n.choose k : ℂ) * iteratedDeriv k f x *
          iteratedDeriv (n - k) g x‖ ≤
      ∑ k ∈ Finset.range (n + 1),
        ‖(n.choose k : ℂ) * iteratedDeriv k f x *
          iteratedDeriv (n - k) g x‖ := norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro k hk
      have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [norm_mul, norm_mul, Complex.norm_natCast]
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hfBound k hkn) (Nat.cast_nonneg _))
        (hgBound (n - k) (Nat.sub_le n k))
        (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) (hF k))

/- theorem norm_iteratedDeriv_gmCubicZWeight_le
    (cutoff : GMSmoothCutoff) (n : ℕ) {v₁ v₂ : ℝ}
    (hv₁ : |v₁| ≤ 2) (hv₂ : |v₂| ≤ 2) (z : ℝ) :
    ‖iteratedDeriv n (gmCubicZWeight cutoff v₁ v₂) z‖ ≤
      gmCubicZDerivativeBound cutoff n := by
  have hfun : gmCubicZWeight cutoff v₁ v₂ = fun y : ℝ =>
      (gmCubicBaseWeight cutoff y * gmCubicCutoffSq cutoff (v₁ * y)) *
        gmCubicCutoffSq cutoff (v₂ * y) := by
    funext y
    exact gmCubicZWeight_eq_base_mul_scaled cutoff v₁ v₂ y
  rw [hfun]
  have hBaseSmooth : ∀ k : ℕ, ContDiffAt ℝ k (gmCubicBaseWeight cutoff) z :=
    fun k => (contDiff_gmCubicBaseWeight cutoff).contDiffAt.of_le
      (WithTop.coe_le_coe.mpr (le_of_lt (ENat.coe_lt_top k)))
  have hScaledSmooth (v : ℝ) (k : ℕ) :
      ContDiffAt ℝ k (fun y : ℝ => gmCubicCutoffSq cutoff (v * y)) z :=
    ((contDiff_gmCubicCutoffSq cutoff).comp
      (contDiff_const.mul contDiff_id)).contDiffAt.of_le
        (WithTop.coe_le_coe.mpr (le_of_lt (ENat.coe_lt_top k)))
  have hInnerSmooth : ContDiffAt ℝ n
      (fun y : ℝ => gmCubicBaseWeight cutoff y *
        gmCubicCutoffSq cutoff (v₁ * y)) z :=
    (hBaseSmooth n).mul (hScaledSmooth v₁ n)
  change ‖iteratedDeriv n
      ((fun y : ℝ => gmCubicBaseWeight cutoff y *
          gmCubicCutoffSq cutoff (v₁ * y)) *
        (fun y : ℝ => gmCubicCutoffSq cutoff (v₂ * y))) z‖ ≤ _
  rw [iteratedDeriv_mul hInnerSmooth (hScaledSmooth v₂ n)]
  calc
    ‖∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℂ) *
          iteratedDeriv i (fun y : ℝ => gmCubicBaseWeight cutoff y *
            gmCubicCutoffSq cutoff (v₁ * y)) z *
          iteratedDeriv (n - i)
            (fun y : ℝ => gmCubicCutoffSq cutoff (v₂ * y)) z‖ ≤
      ∑ i ∈ Finset.range (n + 1),
        ‖(n.choose i : ℂ) *
          iteratedDeriv i (fun y : ℝ => gmCubicBaseWeight cutoff y *
            gmCubicCutoffSq cutoff (v₁ * y)) z *
          iteratedDeriv (n - i)
            (fun y : ℝ => gmCubicCutoffSq cutoff (v₂ * y)) z‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) *
          SchwartzMap.seminorm ℝ 0 j (gmCubicBaseWeightSchwartz cutoff) *
          ((2 : ℝ) ^ (i - j) * SchwartzMap.seminorm ℝ 0 (i - j)
            (gmCubicCutoffSqSchwartz cutoff))) *
        ((2 : ℝ) ^ (n - i) * SchwartzMap.seminorm ℝ 0 (n - i)
          (gmCubicCutoffSqSchwartz cutoff)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hInner :
          ‖iteratedDeriv i (fun y : ℝ => gmCubicBaseWeight cutoff y *
            gmCubicCutoffSq cutoff (v₁ * y)) z‖ ≤
          ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) *
            SchwartzMap.seminorm ℝ 0 j (gmCubicBaseWeightSchwartz cutoff) *
            ((2 : ℝ) ^ (i - j) * SchwartzMap.seminorm ℝ 0 (i - j)
              (gmCubicCutoffSqSchwartz cutoff)) := by
        change ‖iteratedDeriv i
          (gmCubicBaseWeight cutoff *
            (fun y : ℝ => gmCubicCutoffSq cutoff (v₁ * y))) z‖ ≤ _
        rw [iteratedDeriv_mul (hBaseSmooth i) (hScaledSmooth v₁ i)]
        calc
          ‖∑ j ∈ Finset.range (i + 1),
              (i.choose j : ℂ) * iteratedDeriv j (gmCubicBaseWeight cutoff) z *
                iteratedDeriv (i - j)
                  (fun y : ℝ => gmCubicCutoffSq cutoff (v₁ * y)) z‖ ≤
            ∑ j ∈ Finset.range (i + 1),
              ‖(i.choose j : ℂ) * iteratedDeriv j (gmCubicBaseWeight cutoff) z *
                iteratedDeriv (i - j)
                  (fun y : ℝ => gmCubicCutoffSq cutoff (v₁ * y)) z‖ :=
            norm_sum_le _ _
          _ ≤ _ := by
            apply Finset.sum_le_sum
            intro j hj
            rw [norm_mul, norm_mul, Complex.norm_natCast]
            exact mul_le_mul
              (mul_le_mul_of_nonneg_left
                (norm_iteratedDeriv_gmCubicBaseWeight_le cutoff j z)
                (Nat.cast_nonneg _))
              (norm_iteratedDeriv_gmCubicCutoffSq_scaled_le cutoff (i - j) hv₁ z)
              (norm_nonneg _)
              (mul_nonneg (Nat.cast_nonneg _)
                (by positivity))
      rw [norm_mul, norm_mul, Complex.norm_natCast]
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hInner (Nat.cast_nonneg _))
        (norm_iteratedDeriv_gmCubicCutoffSq_scaled_le cutoff (n - i) hv₂ z)
        (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun j _ => by positivity))
    _ = gmCubicZDerivativeBound cutoff n := rfl -/

theorem norm_iteratedDeriv_gmCubicZWeight_le
    (cutoff : GMSmoothCutoff) (n : ℕ) {v₁ v₂ : ℝ}
    (hv₁ : |v₁| ≤ 2) (hv₂ : |v₂| ≤ 2) (z : ℝ) :
    ‖iteratedDeriv n (gmCubicZWeight cutoff v₁ v₂) z‖ ≤
      gmCubicZDerivativeBound cutoff n := by
  let Base : ℕ → ℝ := fun k =>
    SchwartzMap.seminorm ℝ 0 k (gmCubicBaseWeightSchwartz cutoff)
  let Scaled : ℕ → ℝ := fun k => (2 : ℝ) ^ k *
    SchwartzMap.seminorm ℝ 0 k (gmCubicCutoffSqSchwartz cutoff)
  let Inner : ℕ → ℝ := fun i =>
    ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * Base j * Scaled (i - j)
  have hBaseNonneg (k : ℕ) : 0 ≤ Base k := by dsimp only [Base]; positivity
  have hScaledNonneg (k : ℕ) : 0 ≤ Scaled k := by dsimp only [Scaled]; positivity
  have hInnerNonneg (k : ℕ) : 0 ≤ Inner k := by
    dsimp only [Inner]
    exact Finset.sum_nonneg fun j _ =>
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hBaseNonneg j))
        (hScaledNonneg (k - j))
  have hBaseSmooth : ∀ k : ℕ, ContDiffAt ℝ k (gmCubicBaseWeight cutoff) z :=
    fun k => (contDiff_gmCubicBaseWeight cutoff).contDiffAt.of_le
      (WithTop.coe_le_coe.mpr (le_of_lt (ENat.coe_lt_top k)))
  have hScaledSmooth (v : ℝ) (k : ℕ) :
      ContDiffAt ℝ k (fun y : ℝ => gmCubicCutoffSq cutoff (v * y)) z :=
    ((contDiff_gmCubicCutoffSq cutoff).comp
      (contDiff_const.mul contDiff_id)).contDiffAt.of_le
        (WithTop.coe_le_coe.mpr (le_of_lt (ENat.coe_lt_top k)))
  have hBaseBound (k : ℕ) (_hk : k ≤ n) :
      ‖iteratedDeriv k (gmCubicBaseWeight cutoff) z‖ ≤ Base k := by
    exact norm_iteratedDeriv_gmCubicBaseWeight_le cutoff k z
  have hScaledOneBound (k : ℕ) (_hk : k ≤ n) :
      ‖iteratedDeriv k
        (fun y : ℝ => gmCubicCutoffSq cutoff (v₁ * y)) z‖ ≤ Scaled k := by
    exact norm_iteratedDeriv_gmCubicCutoffSq_scaled_le cutoff k hv₁ z
  have hScaledTwoBound (k : ℕ) (_hk : k ≤ n) :
      ‖iteratedDeriv k
        (fun y : ℝ => gmCubicCutoffSq cutoff (v₂ * y)) z‖ ≤ Scaled k := by
    exact norm_iteratedDeriv_gmCubicCutoffSq_scaled_le cutoff k hv₂ z
  have hInnerBound (i : ℕ) (hi : i ≤ n) :
      ‖iteratedDeriv i
        (gmCubicBaseWeight cutoff *
          (fun y : ℝ => gmCubicCutoffSq cutoff (v₁ * y))) z‖ ≤ Inner i := by
    exact norm_iteratedDeriv_mul_le_sum i _ _ z Base Scaled
      (hBaseSmooth i) (hScaledSmooth v₁ i)
      hBaseNonneg
      (fun k hk => hBaseBound k (hk.trans hi))
      (fun k hk => hScaledOneBound k (hk.trans hi))
  have hOuter := norm_iteratedDeriv_mul_le_sum n
    (gmCubicBaseWeight cutoff *
      (fun y : ℝ => gmCubicCutoffSq cutoff (v₁ * y)))
    (fun y : ℝ => gmCubicCutoffSq cutoff (v₂ * y)) z Inner Scaled
    ((hBaseSmooth n).mul (hScaledSmooth v₁ n)) (hScaledSmooth v₂ n)
    hInnerNonneg hInnerBound hScaledTwoBound
  have hweight : gmCubicZWeight cutoff v₁ v₂ =
      (gmCubicBaseWeight cutoff *
        (fun y : ℝ => gmCubicCutoffSq cutoff (v₁ * y))) *
      (fun y : ℝ => gmCubicCutoffSq cutoff (v₂ * y)) := by
    funext y
    exact gmCubicZWeight_eq_base_mul_scaled cutoff v₁ v₂ y
  rw [hweight]
  simpa [gmCubicZDerivativeBound, Base, Scaled, Inner] using hOuter

private theorem integral_norm_iteratedFDeriv_gmCubicZWeight_le
    (cutoff : GMSmoothCutoff) (p : ℕ) {v₁ v₂ : ℝ}
    (hv₁ : |v₁| ≤ 2) (hv₂ : |v₂| ≤ 2) :
    (∫ z : ℝ, ‖iteratedFDeriv ℝ p (gmCubicZWeight cutoff v₁ v₂) z‖) ≤
      gmCubicZDerivativeBound cutoff p := by
  let f : ℝ → ℝ := fun z =>
    ‖iteratedFDeriv ℝ p (gmCubicZWeight cutoff v₁ v₂) z‖
  have hfInt : Integrable f := by
    simpa only [f, pow_zero, one_mul, gmCubicZWeightSchwartz_apply] using
      (SchwartzMap.integrable_pow_mul_iteratedFDeriv volume
        (gmCubicZWeightSchwartz cutoff v₁ v₂) 0 p)
  have hsupport : Function.support f ⊆ Set.Icc (1 : ℝ) 2 := by
    intro z hz
    by_contra hnot
    have hout : z < 1 ∨ 2 < z := by
      by_cases hlow : z < 1
      · exact Or.inl hlow
      · exact Or.inr (lt_of_not_ge fun hupp => hnot ⟨le_of_not_gt hlow, hupp⟩)
    have hzero : gmCubicZWeight cutoff v₁ v₂ =ᶠ[nhds z] 0 := by
      rcases hout with hlow | hhigh
      · filter_upwards [Iio_mem_nhds hlow] with y hy
        simp [gmCubicZWeight, gmSmoothCutoff_eq_zero_of_lt_one cutoff hy]
      · filter_upwards [Ioi_mem_nhds hhigh] with y hy
        simp [gmCubicZWeight,
          gmSmoothCutoff_eq_zero_of_two_le cutoff (le_of_lt hy)]
    apply hz
    dsimp only [f]
    rw [(hzero.iteratedFDeriv ℝ p).eq_of_nhds]
    simp
  have hEq : f = Set.indicator (Set.Icc (1 : ℝ) 2) f := by
    funext z
    by_cases hz : z ∈ Set.Icc (1 : ℝ) 2
    · simp [hz]
    · have : f z = 0 := not_ne_iff.mp fun hne => hz (hsupport hne)
      simp [Set.indicator, hz, this]
  rw [show (∫ z : ℝ,
      ‖iteratedFDeriv ℝ p (gmCubicZWeight cutoff v₁ v₂) z‖) =
      ∫ z : ℝ, f z by rfl]
  rw [hEq, MeasureTheory.integral_indicator measurableSet_Icc]
  calc
    (∫ z : ℝ in Set.Icc 1 2, f z) ≤
        ∫ _z : ℝ in Set.Icc 1 2, gmCubicZDerivativeBound cutoff p := by
      apply MeasureTheory.setIntegral_mono_on
      · exact hfInt.integrableOn
      · exact MeasureTheory.integrableOn_const
          (hs := ne_of_lt
            (measure_Icc_lt_top : volume (Set.Icc (1 : ℝ) 2) < (⊤ : ENNReal)))
      · exact measurableSet_Icc
      · intro z hz
        dsimp only [f]
        rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
        exact norm_iteratedDeriv_gmCubicZWeight_le cutoff p hv₁ hv₂ z
    _ = gmCubicZDerivativeBound cutoff p := by
      simp
      ring

/-- Proposition 7.1's uniform compact-amplitude Fourier estimate before
specializing the cancellation frequency.  The constant is independent of
both ratio parameters throughout the source box. -/
theorem gmCubicZFourier_uniform_decay
    (cutoff : GMSmoothCutoff) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {v₁ v₂ ξ : ℝ}, |v₁| ≤ 2 → |v₂| ≤ 2 →
      |ξ| ^ n * ‖gmCubicZFourier cutoff v₁ v₂ ξ‖ ≤ C := by
  let C : ℝ := 2 ^ n * ∑ p ∈ Finset.range (n + 1),
    gmCubicZDerivativeBound cutoff p
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact mul_nonneg (by positivity)
      (Finset.sum_nonneg fun p _ => gmCubicZDerivativeBound_nonneg cutoff p)
  refine ⟨C, hC, ?_⟩
  intro v₁ v₂ ξ hv₁ hv₂
  have hIntegrable : ∀ (k p : ℕ), k ≤ (0 : ℕ∞) → p ≤ (⊤ : ℕ∞) →
      Integrable (fun z : ℝ => ‖z‖ ^ k *
        ‖iteratedFDeriv ℝ p (gmCubicZWeight cutoff v₁ v₂) z‖) := by
    intro k p _hk _hp
    simpa only [gmCubicZWeightSchwartz_apply] using
      (SchwartzMap.integrable_pow_mul_iteratedFDeriv volume
        (gmCubicZWeightSchwartz cutoff v₁ v₂) k p)
  have hFourier := pow_mul_norm_iteratedFDeriv_fourier_le
    (f := gmCubicZWeight cutoff v₁ v₂)
    (K := (0 : ℕ∞)) (N := (⊤ : ℕ∞))
    (contDiff_gmCubicZWeight cutoff v₁ v₂) hIntegrable
    (k := 0) (n := n) (by norm_num) (by simp) ξ
  simp only [pow_zero, one_mul, zero_add, Finset.range_one,
    norm_iteratedFDeriv_zero] at hFourier
  have hFourier' : |ξ| ^ n * ‖gmCubicZFourier cutoff v₁ v₂ ξ‖ ≤
      2 ^ n * ∑ p ∈ Finset.range (n + 1),
        ∫ z : ℝ, ‖iteratedFDeriv ℝ p (gmCubicZWeight cutoff v₁ v₂) z‖ := by
    simpa [gmCubicZFourier, Real.norm_eq_abs, SchwartzMap.fourier_coe]
      using hFourier
  calc
    |ξ| ^ n * ‖gmCubicZFourier cutoff v₁ v₂ ξ‖ ≤
        2 ^ n * ∑ p ∈ Finset.range (n + 1),
          ∫ z : ℝ, ‖iteratedFDeriv ℝ p
            (gmCubicZWeight cutoff v₁ v₂) z‖ := hFourier'
    _ ≤ 2 ^ n * ∑ p ∈ Finset.range (n + 1),
        gmCubicZDerivativeBound cutoff p := by
      gcongr with p hp
      exact integral_norm_iteratedFDeriv_gmCubicZWeight_le cutoff p hv₁ hv₂
    _ = C := rfl

theorem gmCubicZFourier_far_frequency_pow
    (cutoff : GMSmoothCutoff) (η : ℝ) (hη : 0 < η) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {T v₁ v₂ ξ : ℝ}, 1 ≤ T →
      |v₁| ≤ 2 → |v₂| ≤ 2 → T ^ η ≤ |ξ| →
      ‖gmCubicZFourier cutoff v₁ v₂ ξ‖ ≤ C / T ^ A := by
  obtain ⟨n, hnRaw⟩ := exists_nat_gt ((A : ℝ) / η)
  have hn : (A : ℝ) ≤ η * (n : ℝ) := by
    rw [div_lt_iff₀ hη] at hnRaw
    linarith
  obtain ⟨C, hC, hDecay⟩ := gmCubicZFourier_uniform_decay cutoff n
  refine ⟨C, hC, ?_⟩
  intro T v₁ v₂ ξ hT hv₁ hv₂ hξ
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hξpos : 0 < |ξ| := (Real.rpow_pos_of_pos hTpos η).trans_le hξ
  have hpowξ : (T ^ η) ^ n ≤ |ξ| ^ n :=
    pow_le_pow_left₀ (Real.rpow_nonneg hTpos.le η) hξ n
  have hpowT : T ^ A ≤ (T ^ η) ^ n := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast,
      ← Real.rpow_mul hTpos.le]
    exact Real.rpow_le_rpow_of_exponent_le hT hn
  have hdiv : ‖gmCubicZFourier cutoff v₁ v₂ ξ‖ ≤ C / |ξ| ^ n := by
    rw [le_div_iff₀ (pow_pos hξpos n)]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hDecay hv₁ hv₂
  calc
    ‖gmCubicZFourier cutoff v₁ v₂ ξ‖ ≤ C / |ξ| ^ n := hdiv
    _ ≤ C / (T ^ η) ^ n :=
      div_le_div_of_nonneg_left hC (by positivity) hpowξ
    _ ≤ C / T ^ A :=
      div_le_div_of_nonneg_left hC (by positivity) hpowT

theorem gmCubicZFourier_cancellation_pow
    (cutoff : GMSmoothCutoff) (η : ℝ) (hη : 0 < η) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {T : ℝ} {N : ℕ} {v₁ v₂ : ℝ}
      {m : ℤ × (ℤ × ℤ)}, 1 ≤ T → 0 < N →
      |v₁| ≤ 2 → |v₂| ≤ 2 →
      T ^ η / (N : ℝ) ≤
        |(m.1 : ℝ) * v₁ + (m.2.1 : ℝ) * v₂ + (m.2.2 : ℝ)| →
      ‖gmCubicZFourier cutoff v₁ v₂
        ((N : ℝ) * ((m.1 : ℝ) * v₁ + (m.2.1 : ℝ) * v₂ +
          (m.2.2 : ℝ)))‖ ≤ C / T ^ A := by
  obtain ⟨C, hC, hFar⟩ := gmCubicZFourier_far_frequency_pow cutoff η hη A
  refine ⟨C, hC, ?_⟩
  intro T N v₁ v₂ m hT hN hv₁ hv₂ hcancel
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hfreq : T ^ η ≤
      |(N : ℝ) * ((m.1 : ℝ) * v₁ + (m.2.1 : ℝ) * v₂ +
        (m.2.2 : ℝ))| := by
    rw [abs_mul, abs_of_pos hNpos]
    have := mul_le_mul_of_nonneg_left hcancel hNpos.le
    field_simp at this
    exact this
  exact hFar hT hv₁ hv₂ hfreq

/-- Arbitrary-order decay specialized to the source `T^η` cancellation
threshold. -/
theorem gmCubicZFourier_far_frequency_pow_100
    (cutoff : GMSmoothCutoff) (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {T v₁ v₂ ξ : ℝ}, 1 ≤ T →
      |v₁| ≤ 2 → |v₂| ≤ 2 → T ^ η ≤ |ξ| →
      ‖gmCubicZFourier cutoff v₁ v₂ ξ‖ ≤ C / T ^ 100 := by
  obtain ⟨n, hnRaw⟩ := exists_nat_gt (100 / η)
  have hn : 100 ≤ η * (n : ℝ) := by
    rw [div_lt_iff₀ hη] at hnRaw
    linarith
  obtain ⟨C, hC, hDecay⟩ := gmCubicZFourier_uniform_decay cutoff n
  refine ⟨C, hC, ?_⟩
  intro T v₁ v₂ ξ hT hv₁ hv₂ hξ
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hξpos : 0 < |ξ| := (Real.rpow_pos_of_pos hTpos η).trans_le hξ
  have hpowξ : (T ^ η) ^ n ≤ |ξ| ^ n :=
    pow_le_pow_left₀ (Real.rpow_nonneg hTpos.le η) hξ n
  have hpowT : T ^ 100 ≤ (T ^ η) ^ n := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast,
      ← Real.rpow_mul hTpos.le]
    exact Real.rpow_le_rpow_of_exponent_le hT hn
  have hdiv : ‖gmCubicZFourier cutoff v₁ v₂ ξ‖ ≤ C / |ξ| ^ n := by
    rw [le_div_iff₀ (pow_pos hξpos n)]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hDecay hv₁ hv₂
  calc
    ‖gmCubicZFourier cutoff v₁ v₂ ξ‖ ≤ C / |ξ| ^ n := hdiv
    _ ≤ C / (T ^ η) ^ n :=
      div_le_div_of_nonneg_left hC (by positivity) hpowξ
    _ ≤ C / T ^ 100 :=
      div_le_div_of_nonneg_left hC (by positivity) hpowT

/-- The literal cancellation-frequency consequence used in Proposition 7.1.
Outside a slab of width `T^η/N` around
`m₁v₁ + m₂v₂ + m₃ = 0`, the exact Fourier kernel is `O(T⁻¹⁰⁰)`. -/
theorem gmCubicZFourier_cancellation_pow_100
    (cutoff : GMSmoothCutoff) (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {T : ℝ} {N : ℕ} {v₁ v₂ : ℝ}
      {m : ℤ × (ℤ × ℤ)}, 1 ≤ T → 0 < N →
      |v₁| ≤ 2 → |v₂| ≤ 2 →
      T ^ η / (N : ℝ) ≤
        |(m.1 : ℝ) * v₁ + (m.2.1 : ℝ) * v₂ + (m.2.2 : ℝ)| →
      ‖gmCubicZFourier cutoff v₁ v₂
        ((N : ℝ) * ((m.1 : ℝ) * v₁ + (m.2.1 : ℝ) * v₂ +
          (m.2.2 : ℝ)))‖ ≤ C / T ^ 100 := by
  obtain ⟨C, hC, hFar⟩ := gmCubicZFourier_far_frequency_pow_100 cutoff η hη
  refine ⟨C, hC, ?_⟩
  intro T N v₁ v₂ m hT hN hv₁ hv₂ hcancel
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hfreq : T ^ η ≤
      |(N : ℝ) * ((m.1 : ℝ) * v₁ + (m.2.1 : ℝ) * v₂ +
        (m.2.2 : ℝ))| := by
    rw [abs_mul, abs_of_pos hNpos]
    have := mul_le_mul_of_nonneg_left hcancel hNpos.le
    field_simp at this
    exact this
  exact hFar hT hv₁ hv₂ hfreq

/-- The remaining `z`-integral is precisely the Fourier transform of the
compact scale amplitude, with all three `R`-factors outside. -/
theorem integral_gmCubicRatioIntegrand_eq_fourier
    (cutoff : GMSmoothCutoff) (N : ℕ) (W : Finset ℝ)
    (m : ℤ × (ℤ × ℤ)) (v₁ v₂ : ℝ) :
    (∫ z : ℝ, gmCubicRatioIntegrand cutoff N W m ((v₁, v₂), z)) =
      gmCubicZFourier cutoff v₁ v₂
          ((N : ℝ) * ((m.1 : ℝ) * v₁ + (m.2.1 : ℝ) * v₂ +
            (m.2.2 : ℝ))) *
        gmR W v₁ * gmR W (v₂ / v₁) * gmR W (1 / v₂) := by
  have hpoint (z : ℝ) :
      gmCubicRatioIntegrand cutoff N W m ((v₁, v₂), z) =
        (gmTraceOscillation
            ((N : ℝ) * ((m.1 : ℝ) * v₁ + (m.2.1 : ℝ) * v₂ +
              (m.2.2 : ℝ))) z *
          gmCubicZWeight cutoff v₁ v₂ z) *
          gmR W v₁ * gmR W (v₂ / v₁) * gmR W (1 / v₂) := by
    unfold gmCubicRatioIntegrand gmCubicZWeight
    push_cast
    ring
  simp_rw [hpoint]
  rw [MeasureTheory.integral_mul_const, MeasureTheory.integral_mul_const,
    MeasureTheory.integral_mul_const]
  rw [← gmCubicZFourier_eq_integral]

/-- Globally continuous form of the ratio integrand, before rewriting its
three `R`-factors. -/
noncomputable def gmCubicRatioRawIntegrand (cutoff : GMSmoothCutoff)
    (N : ℕ) (W : Finset ℝ) (m : ℤ × (ℤ × ℤ))
    (q : (ℝ × ℝ) × ℝ) : ℂ :=
  ((q.2 ^ 2 : ℝ) : ℂ) *
    gmCubicS3ModeSummedIntegrand cutoff N W m (gmCubicRatioMap q)

theorem continuous_gmCubicRatioMap : Continuous gmCubicRatioMap := by
  unfold gmCubicRatioMap
  fun_prop

theorem continuous_gmCubicRatioRawIntegrand
    (cutoff : GMSmoothCutoff) (N : ℕ) (W : Finset ℝ)
    (m : ℤ × (ℤ × ℤ)) :
    Continuous (gmCubicRatioRawIntegrand cutoff N W m) := by
  unfold gmCubicRatioRawIntegrand
  have hz : Continuous (fun q : (ℝ × ℝ) × ℝ => ((q.2 ^ 2 : ℝ) : ℂ)) := by
    fun_prop
  exact hz.mul ((continuous_gmCubicS3ModeSummedIntegrand cutoff N W m).comp
    continuous_gmCubicRatioMap)

/-- Fixed compact box containing the transformed support. -/
def gmCubicRatioBox : Set ((ℝ × ℝ) × ℝ) :=
  (Set.Icc (1 / 2 : ℝ) 2 ×ˢ Set.Icc (1 / 2 : ℝ) 2) ×ˢ
    Set.Icc (1 : ℝ) 2

theorem isCompact_gmCubicRatioBox : IsCompact gmCubicRatioBox :=
  (isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc

theorem gmCubicRatioRawIntegrand_eq_zero_of_not_mem_box
    (cutoff : GMSmoothCutoff) (N : ℕ) (W : Finset ℝ)
    (m : ℤ × (ℤ × ℤ)) {q : (ℝ × ℝ) × ℝ}
    (hq : q ∉ gmCubicRatioBox) :
    gmCubicRatioRawIntegrand cutoff N W m q = 0 := by
  by_cases hz : q.2 ∈ Set.Icc (1 : ℝ) 2
  · have hxy : q.1 ∉ Set.Icc (1 / 2 : ℝ) 2 ×ˢ Set.Icc (1 / 2 : ℝ) 2 := by
      intro hxy
      exact hq ⟨hxy, hz⟩
    simp only [Set.mem_prod, Set.mem_Icc, not_and_or] at hxy
    rcases hxy with hv₁ | hv₂
    · rcases hv₁ with hv₁ | hv₁
      · have hscale : q.1.1 * q.2 ≤ 1 := calc
          q.1.1 * q.2 ≤ (1 / 2 : ℝ) * q.2 :=
            mul_le_mul_of_nonneg_right (not_le.mp hv₁).le (by linarith [hz.1])
          _ ≤ 1 := by nlinarith [hz.2]
        have hcut : cutoff (q.1.1 * q.2) = 0 :=
          gmSmoothCutoff_eq_zero_of_le_one cutoff hscale
        unfold gmCubicRatioRawIntegrand gmCubicRatioMap
        rw [gmCubicS3ModeSummedIntegrand_eq_RPhase]
        simp [hcut]
      · have hv₁' : 2 < q.1.1 := not_le.mp hv₁
        have hscale : 2 ≤ q.1.1 * q.2 := calc
          2 = 2 * 1 := by ring
          _ ≤ q.1.1 * 1 := mul_le_mul_of_nonneg_right hv₁'.le (by norm_num)
          _ ≤ q.1.1 * q.2 :=
            mul_le_mul_of_nonneg_left hz.1 (by positivity)
        have hcut : cutoff (q.1.1 * q.2) = 0 :=
          gmSmoothCutoff_eq_zero_of_two_le cutoff hscale
        unfold gmCubicRatioRawIntegrand gmCubicRatioMap
        rw [gmCubicS3ModeSummedIntegrand_eq_RPhase]
        simp [hcut]
    · rcases hv₂ with hv₂ | hv₂
      · have hscale : q.1.2 * q.2 ≤ 1 := calc
          q.1.2 * q.2 ≤ (1 / 2 : ℝ) * q.2 :=
            mul_le_mul_of_nonneg_right (not_le.mp hv₂).le (by linarith [hz.1])
          _ ≤ 1 := by nlinarith [hz.2]
        have hcut : cutoff (q.1.2 * q.2) = 0 :=
          gmSmoothCutoff_eq_zero_of_le_one cutoff hscale
        unfold gmCubicRatioRawIntegrand gmCubicRatioMap
        rw [gmCubicS3ModeSummedIntegrand_eq_RPhase]
        simp [hcut]
      · have hv₂' : 2 < q.1.2 := not_le.mp hv₂
        have hscale : 2 ≤ q.1.2 * q.2 := calc
          2 = 2 * 1 := by ring
          _ ≤ q.1.2 * 1 := mul_le_mul_of_nonneg_right hv₂'.le (by norm_num)
          _ ≤ q.1.2 * q.2 :=
            mul_le_mul_of_nonneg_left hz.1 (by positivity)
        have hcut : cutoff (q.1.2 * q.2) = 0 :=
          gmSmoothCutoff_eq_zero_of_two_le cutoff hscale
        unfold gmCubicRatioRawIntegrand gmCubicRatioMap
        rw [gmCubicS3ModeSummedIntegrand_eq_RPhase]
        simp [hcut]
  · have hcut : cutoff q.2 = 0 := by
      simp only [Set.mem_Icc, not_and_or] at hz
      rcases hz with hz | hz
      · exact gmSmoothCutoff_eq_zero_of_le_one cutoff (not_le.mp hz).le
      · exact gmSmoothCutoff_eq_zero_of_two_le cutoff (not_le.mp hz).le
    unfold gmCubicRatioRawIntegrand gmCubicRatioMap
    rw [gmCubicS3ModeSummedIntegrand_eq_RPhase]
    simp [hcut]

theorem hasCompactSupport_gmCubicRatioRawIntegrand
    (cutoff : GMSmoothCutoff) (N : ℕ) (W : Finset ℝ)
    (m : ℤ × (ℤ × ℤ)) :
    HasCompactSupport (gmCubicRatioRawIntegrand cutoff N W m) := by
  apply HasCompactSupport.intro isCompact_gmCubicRatioBox
  intro q hq
  exact gmCubicRatioRawIntegrand_eq_zero_of_not_mem_box cutoff N W m hq

theorem integrable_gmCubicRatioRawIntegrand
    (cutoff : GMSmoothCutoff) (N : ℕ) (W : Finset ℝ)
    (m : ℤ × (ℤ × ℤ)) :
    Integrable (gmCubicRatioRawIntegrand cutoff N W m)
      ((volume.prod volume).prod volume) :=
  (continuous_gmCubicRatioRawIntegrand cutoff N W m).integrable_of_hasCompactSupport
    (hasCompactSupport_gmCubicRatioRawIntegrand cutoff N W m)

/-- The globally continuous source form and the explicit ratio form agree
everywhere.  At nonpositive outer scale both vanish by cutoff support. -/
theorem gmCubicRatioRawIntegrand_eq_ratioIntegrand
    (cutoff : GMSmoothCutoff) (N : ℕ) (W : Finset ℝ)
    (m : ℤ × (ℤ × ℤ)) (q : (ℝ × ℝ) × ℝ) :
    gmCubicRatioRawIntegrand cutoff N W m q =
      gmCubicRatioIntegrand cutoff N W m q := by
  by_cases hz : 0 < q.2
  · simpa [gmCubicRatioRawIntegrand] using
      gmCubicS3ModeSummedIntegrand_ratioMap_all
        cutoff N W m q.1.1 q.1.2 hz
  · have hcut : cutoff q.2 = 0 :=
      gmSmoothCutoff_eq_zero_of_le_one cutoff
        (by have := not_lt.mp hz; linarith)
    unfold gmCubicRatioRawIntegrand gmCubicRatioMap gmCubicRatioIntegrand
    rw [gmCubicS3ModeSummedIntegrand_eq_RPhase]
    simp [hcut]

theorem integrable_gmCubicRatioIntegrand
    (cutoff : GMSmoothCutoff) (N : ℕ) (W : Finset ℝ)
    (m : ℤ × (ℤ × ℤ)) :
    Integrable (gmCubicRatioIntegrand cutoff N W m)
      ((volume.prod volume).prod volume) := by
  refine (integrable_gmCubicRatioRawIntegrand cutoff N W m).congr ?_
  filter_upwards with q
  exact gmCubicRatioRawIntegrand_eq_ratioIntegrand cutoff N W m q

/-- Exact Fubini interchange from the source order `(z,v₁,v₂)` to the
Fourier-analysis order `(v₁,v₂,z)`. -/
theorem integral_z_v₁_v₂_gmCubicRatioIntegrand_eq_v₁_v₂_z
    (cutoff : GMSmoothCutoff) (N : ℕ) (W : Finset ℝ)
    (m : ℤ × (ℤ × ℤ)) :
    (∫ z : ℝ, ∫ v₁ : ℝ, ∫ v₂ : ℝ,
        gmCubicRatioIntegrand cutoff N W m ((v₁, v₂), z)) =
      ∫ v₁ : ℝ, ∫ v₂ : ℝ, ∫ z : ℝ,
        gmCubicRatioIntegrand cutoff N W m ((v₁, v₂), z) := by
  let f : (ℝ × ℝ) × ℝ → ℂ := gmCubicRatioIntegrand cutoff N W m
  have hf : Integrable f ((volume.prod volume).prod volume) :=
    integrable_gmCubicRatioIntegrand cutoff N W m
  calc
    (∫ z : ℝ, ∫ v₁ : ℝ, ∫ v₂ : ℝ,
        gmCubicRatioIntegrand cutoff N W m ((v₁, v₂), z)) =
      ∫ z : ℝ, ∫ q : ℝ × ℝ, f (q, z) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [hf.prod_left_ae] with z hz
        exact (MeasureTheory.integral_prod _ hz).symm
    _ = ∫ q : (ℝ × ℝ) × ℝ, f q ∂(volume.prod volume).prod volume :=
      (MeasureTheory.integral_prod_symm _ hf).symm
    _ = ∫ q : ℝ × ℝ, ∫ z : ℝ, f (q, z) :=
      MeasureTheory.integral_prod _ hf
    _ = ∫ v₁ : ℝ, ∫ v₂ : ℝ, ∫ z : ℝ,
        gmCubicRatioIntegrand cutoff N W m ((v₁, v₂), z) := by
      simpa [f] using MeasureTheory.integral_prod
        (fun q : ℝ × ℝ => ∫ z : ℝ, f (q, z)) hf.integral_prod_left

/-- The exact Fourier-side expression for one nonzero cubic frequency. -/
noncomputable def gmCubicS3FourierIntegral (cutoff : GMSmoothCutoff)
    (N : ℕ) (W : Finset ℝ) (m : ℤ × (ℤ × ℤ)) : ℂ :=
  (N : ℂ) ^ 3 * ∫ v₁ : ℝ, ∫ v₂ : ℝ,
    gmCubicZFourier cutoff v₁ v₂
        ((N : ℝ) * ((m.1 : ℝ) * v₁ + (m.2.1 : ℝ) * v₂ +
          (m.2.2 : ℝ))) *
      gmR W v₁ * gmR W (v₂ / v₁) * gmR W (1 / v₂)

theorem gmCubicS3RatioIntegral_eq_fourierIntegral
    (cutoff : GMSmoothCutoff) (N : ℕ) (W : Finset ℝ)
    (m : ℤ × (ℤ × ℤ)) :
    gmCubicS3RatioIntegral cutoff N W m =
      gmCubicS3FourierIntegral cutoff N W m := by
  unfold gmCubicS3RatioIntegral gmCubicS3FourierIntegral
  congr 1
  rw [integral_z_v₁_v₂_gmCubicRatioIntegrand_eq_v₁_v₂_z]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with v₁
  apply MeasureTheory.integral_congr_ae
  filter_upwards with v₂
  exact integral_gmCubicRatioIntegrand_eq_fourier cutoff N W m v₁ v₂

/-! ## Proposition 7.1: cancellation-slab localization -/

/-- The `gmCubicRatioSquare` definition used by the source-facing construction in `LargeValuesS3`. -/
def gmCubicRatioSquare : Set (ℝ × ℝ) :=
  Set.Icc (1 / 2 : ℝ) 2 ×ˢ Set.Icc (1 / 2 : ℝ) 2

theorem measurableSet_gmCubicRatioSquare : MeasurableSet gmCubicRatioSquare :=
  measurableSet_Icc.prod measurableSet_Icc

/-- The `gmCubicCancellationSlab` definition used by the source-facing construction in `LargeValuesS3`. -/
def gmCubicCancellationSlab (η T : ℝ) (N : ℕ)
    (m : ℤ × (ℤ × ℤ)) : Set (ℝ × ℝ) :=
  gmCubicRatioSquare ∩
    {q | |(m.1 : ℝ) * q.1 + (m.2.1 : ℝ) * q.2 + (m.2.2 : ℝ)| ≤
      T ^ η / (N : ℝ)}

theorem measurableSet_gmCubicCancellationSlab
    (η T : ℝ) (N : ℕ) (m : ℤ × (ℤ × ℤ)) :
    MeasurableSet (gmCubicCancellationSlab η T N m) := by
  apply measurableSet_gmCubicRatioSquare.inter
  exact measurableSet_le
    (((continuous_const.mul continuous_fst).add
      (continuous_const.mul continuous_snd)).add continuous_const).abs.measurable
    measurable_const

/-- The `gmCubicFourierIntegrand` definition used by the source-facing construction in `LargeValuesS3`. -/
noncomputable def gmCubicFourierIntegrand (cutoff : GMSmoothCutoff)
    (N : ℕ) (W : Finset ℝ) (m : ℤ × (ℤ × ℤ)) (q : ℝ × ℝ) : ℂ :=
  gmCubicZFourier cutoff q.1 q.2
      ((N : ℝ) * ((m.1 : ℝ) * q.1 + (m.2.1 : ℝ) * q.2 +
        (m.2.2 : ℝ))) *
    gmR W q.1 * gmR W (q.2 / q.1) * gmR W (1 / q.2)

theorem integrable_gmCubicFourierIntegrand
    (cutoff : GMSmoothCutoff) (N : ℕ) (W : Finset ℝ)
    (m : ℤ × (ℤ × ℤ)) :
    Integrable (gmCubicFourierIntegrand cutoff N W m) (volume.prod volume) := by
  have hall := integrable_gmCubicRatioIntegrand cutoff N W m
  have hinner : Integrable (fun q : ℝ × ℝ =>
      ∫ z : ℝ, gmCubicRatioIntegrand cutoff N W m (q, z))
      (volume.prod volume) := hall.integral_prod_left
  refine hinner.congr ?_
  filter_upwards with q
  simpa [gmCubicFourierIntegrand] using
    integral_gmCubicRatioIntegrand_eq_fourier cutoff N W m q.1 q.2

theorem gmCubicS3FourierIntegral_eq_integral
    (cutoff : GMSmoothCutoff) (N : ℕ) (W : Finset ℝ)
    (m : ℤ × (ℤ × ℤ)) :
    gmCubicS3FourierIntegral cutoff N W m =
      (N : ℂ) ^ 3 * ∫ q : ℝ × ℝ,
        gmCubicFourierIntegrand cutoff N W m q := by
  unfold gmCubicS3FourierIntegral
  congr 1
  simpa [gmCubicFourierIntegrand] using (MeasureTheory.integral_prod
    (gmCubicFourierIntegrand cutoff N W m)
      (integrable_gmCubicFourierIntegrand cutoff N W m)).symm

theorem gmCubicFourierIntegrand_eq_zero_of_not_mem_ratioSquare
    (cutoff : GMSmoothCutoff) (N : ℕ) (W : Finset ℝ)
    (m : ℤ × (ℤ × ℤ)) {q : ℝ × ℝ} (hq : q ∉ gmCubicRatioSquare) :
    gmCubicFourierIntegrand cutoff N W m q = 0 := by
  unfold gmCubicFourierIntegrand
  rw [← integral_gmCubicRatioIntegrand_eq_fourier cutoff N W m q.1 q.2]
  apply integral_eq_zero_of_ae
  filter_upwards with z
  rw [← gmCubicRatioRawIntegrand_eq_ratioIntegrand cutoff N W m (q, z)]
  exact gmCubicRatioRawIntegrand_eq_zero_of_not_mem_box cutoff N W m (by
    intro hbox
    exact hq hbox.1)

theorem gmCubicS3Mode_eq_fourierIntegral
    (cutoff : GMSmoothCutoff) (N : ℕ) (W : Finset ℝ)
    (m : ℤ × (ℤ × ℤ))
    (hm1 : m.1 ≠ 0) (hm2 : m.2.1 ≠ 0) (hm3 : m.2.2 ≠ 0) :
    gmCubicS3Mode cutoff N W m =
      gmCubicS3FourierIntegral cutoff N W m := by
  rw [gmCubicS3Mode_eq_integral cutoff N W m hm1 hm2 hm3,
    gmCubicS3ModeIntegral_eq_ratioIntegral,
    gmCubicS3RatioIntegral_eq_fourierIntegral]

theorem continuousAt_gmR (W : Finset ℝ) {v : ℝ} (hv : v ≠ 0) :
    ContinuousAt (gmR W) v := by
  have hlog : ContinuousAt (fun x : ℝ => Real.log |x|) v :=
    (Real.continuousAt_log (abs_ne_zero.mpr hv)).comp continuous_abs.continuousAt
  have hphase : ContinuousAt (fun x : ℝ =>
      gmRPhase W (Real.log |x|)) v :=
    (continuous_gmRPhase W).continuousAt.comp hlog
  apply hphase.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hv] with x hx
  exact gmR_eq_gmRPhase_log hx

/-- The exact product of the three source exponential-sum norms occurring
after the ratio change of variables in Guth--Maynard equation (7.3). -/
noncomputable def gmCubicRAmplitude (W : Finset ℝ) (q : ℝ × ℝ) : ℝ :=
  ‖gmR W q.1‖ * ‖gmR W (q.2 / q.1)‖ * ‖gmR W (1 / q.2)‖

theorem continuousOn_gmCubicRAmplitude (W : Finset ℝ) :
    ContinuousOn (gmCubicRAmplitude W) gmCubicRatioSquare := by
  apply continuousOn_of_forall_continuousAt
  intro q hq
  have hq1pos : 0 < q.1 := lt_of_lt_of_le (by norm_num) hq.1.1
  have hq2pos : 0 < q.2 := lt_of_lt_of_le (by norm_num) hq.2.1
  have hq1 : q.1 ≠ 0 := hq1pos.ne'
  have hq2 : q.2 ≠ 0 := hq2pos.ne'
  have hratio : q.2 / q.1 ≠ 0 := div_ne_zero hq2 hq1
  have hinv : 1 / q.2 ≠ 0 := one_div_ne_zero hq2
  have hratioCont : ContinuousAt (fun p : ℝ × ℝ => p.2 / p.1) q :=
    continuous_snd.continuousAt.div continuous_fst.continuousAt hq1
  have hinvCont : ContinuousAt (fun p : ℝ × ℝ => 1 / p.2) q :=
    (continuousAt_const : ContinuousAt (fun _ : ℝ × ℝ => (1 : ℝ)) q).div
      continuous_snd.continuousAt hq2
  have hgmRatio : ContinuousAt (fun p : ℝ × ℝ => gmR W (p.2 / p.1)) q :=
    (continuousAt_gmR W hratio).tendsto.comp hratioCont.tendsto
  have hgmInv : ContinuousAt (fun p : ℝ × ℝ => gmR W (1 / p.2)) q :=
    (continuousAt_gmR W hinv).tendsto.comp hinvCont.tendsto
  unfold gmCubicRAmplitude
  exact ((((continuousAt_gmR W hq1).comp continuous_fst.continuousAt).norm.mul
    hgmRatio.norm).mul hgmInv.norm)

theorem integrableOn_gmCubicRAmplitude_ratioSquare (W : Finset ℝ) :
    IntegrableOn (gmCubicRAmplitude W) gmCubicRatioSquare :=
  (continuousOn_gmCubicRAmplitude W).integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc)

/-- The `gmCubicCancellationMass` definition used by the source-facing construction in `LargeValuesS3`. -/
noncomputable def gmCubicCancellationMass (η T : ℝ) (N : ℕ)
    (W : Finset ℝ) (m : ℤ × (ℤ × ℤ)) : ℝ :=
  ∫ q in gmCubicCancellationSlab η T N m, gmCubicRAmplitude W q

theorem integrableOn_gmCubicRAmplitude_cancellationSlab
    (η T : ℝ) (N : ℕ) (W : Finset ℝ) (m : ℤ × (ℤ × ℤ)) :
    IntegrableOn (gmCubicRAmplitude W) (gmCubicCancellationSlab η T N m) :=
  (integrableOn_gmCubicRAmplitude_ratioSquare W).mono_set inter_subset_left

theorem gmCubicRAmplitude_nonneg (W : Finset ℝ) (q : ℝ × ℝ) :
    0 ≤ gmCubicRAmplitude W q := by
  unfold gmCubicRAmplitude
  positivity

theorem gmCubicRAmplitude_le_card_cubed
    (W : Finset ℝ) {q : ℝ × ℝ} (hq : q ∈ gmCubicRatioSquare) :
    gmCubicRAmplitude W q ≤ (W.card : ℝ) ^ 3 := by
  have hq1pos : 0 < q.1 := lt_of_lt_of_le (by norm_num) hq.1.1
  have hq2pos : 0 < q.2 := lt_of_lt_of_le (by norm_num) hq.2.1
  have hq1 : q.1 ≠ 0 := hq1pos.ne'
  have hq2 : q.2 ≠ 0 := hq2pos.ne'
  have hratio : q.2 / q.1 ≠ 0 := div_ne_zero hq2 hq1
  have hinv : 1 / q.2 ≠ 0 := one_div_ne_zero hq2
  have h1 := norm_gmR_le_card W q.1 hq1
  have h2 := norm_gmR_le_card W (q.2 / q.1) hratio
  have h3 := norm_gmR_le_card W (1 / q.2) hinv
  unfold gmCubicRAmplitude
  calc
    ‖gmR W q.1‖ * ‖gmR W (q.2 / q.1)‖ * ‖gmR W (1 / q.2)‖ ≤
        (W.card : ℝ) * (W.card : ℝ) * (W.card : ℝ) := by
      gcongr
    _ = (W.card : ℝ) ^ 3 := by ring

theorem norm_gmCubicFourierIntegrand_eq
    (cutoff : GMSmoothCutoff) (N : ℕ) (W : Finset ℝ)
    (m : ℤ × (ℤ × ℤ)) (q : ℝ × ℝ) :
    ‖gmCubicFourierIntegrand cutoff N W m q‖ =
      ‖gmCubicZFourier cutoff q.1 q.2
        ((N : ℝ) * ((m.1 : ℝ) * q.1 + (m.2.1 : ℝ) * q.2 +
          (m.2.2 : ℝ)))‖ * gmCubicRAmplitude W q := by
  simp only [gmCubicFourierIntegrand, gmCubicRAmplitude, norm_mul]
  ring

theorem norm_gmCubicFourierIntegrand_le_on_slab
    (cutoff : GMSmoothCutoff) {C : ℝ}
    (hC : ∀ {v₁ v₂ ξ : ℝ}, |v₁| ≤ 2 → |v₂| ≤ 2 →
      ‖gmCubicZFourier cutoff v₁ v₂ ξ‖ ≤ C)
    {η T : ℝ} {N : ℕ} {W : Finset ℝ} {m : ℤ × (ℤ × ℤ)}
    {q : ℝ × ℝ} (hq : q ∈ gmCubicCancellationSlab η T N m) :
    ‖gmCubicFourierIntegrand cutoff N W m q‖ ≤
      C * gmCubicRAmplitude W q := by
  rw [norm_gmCubicFourierIntegrand_eq]
  apply mul_le_mul_of_nonneg_right _ (gmCubicRAmplitude_nonneg W q)
  apply hC
  · calc
      |q.1| = q.1 := abs_of_nonneg (le_trans (by norm_num) hq.1.1.1)
      _ ≤ 2 := hq.1.1.2
  · calc
      |q.2| = q.2 := abs_of_nonneg (le_trans (by norm_num) hq.1.2.1)
      _ ≤ 2 := hq.1.2.2

theorem norm_gmCubicFourierIntegrand_le_off_slab
    (cutoff : GMSmoothCutoff) {η T : ℝ} {N A : ℕ}
    {W : Finset ℝ} {m : ℤ × (ℤ × ℤ)} {C : ℝ}
    (hT : 1 ≤ T) (hN : 0 < N)
    (hTail : ∀ {T : ℝ} {N : ℕ} {v₁ v₂ : ℝ}
      {m : ℤ × (ℤ × ℤ)}, 1 ≤ T → 0 < N →
      |v₁| ≤ 2 → |v₂| ≤ 2 →
      T ^ η / (N : ℝ) ≤
        |(m.1 : ℝ) * v₁ + (m.2.1 : ℝ) * v₂ + (m.2.2 : ℝ)| →
      ‖gmCubicZFourier cutoff v₁ v₂
        ((N : ℝ) * ((m.1 : ℝ) * v₁ + (m.2.1 : ℝ) * v₂ +
          (m.2.2 : ℝ)))‖ ≤ C / T ^ A)
    {q : ℝ × ℝ}
    (hq : q ∈ gmCubicRatioSquare \ gmCubicCancellationSlab η T N m) :
    ‖gmCubicFourierIntegrand cutoff N W m q‖ ≤
      (C / T ^ A) * (W.card : ℝ) ^ 3 := by
  have hcancel : T ^ η / (N : ℝ) ≤
      |(m.1 : ℝ) * q.1 + (m.2.1 : ℝ) * q.2 + (m.2.2 : ℝ)| := by
    have hnle : ¬ |(m.1 : ℝ) * q.1 + (m.2.1 : ℝ) * q.2 + (m.2.2 : ℝ)| ≤
        T ^ η / (N : ℝ) := by
      intro hc
      exact hq.2 ⟨hq.1, hc⟩
    exact le_of_lt (lt_of_not_ge hnle)
  have hkernel := hTail hT hN (by
      calc
        |q.1| = q.1 := abs_of_nonneg (le_trans (by norm_num) hq.1.1.1)
        _ ≤ 2 := hq.1.1.2) (by
      calc
        |q.2| = q.2 := abs_of_nonneg (le_trans (by norm_num) hq.1.2.1)
        _ ≤ 2 := hq.1.2.2) hcancel
  rw [norm_gmCubicFourierIntegrand_eq]
  exact mul_le_mul hkernel (gmCubicRAmplitude_le_card_cubed W hq.1)
    (gmCubicRAmplitude_nonneg W q) ((norm_nonneg _).trans hkernel)

theorem volume_real_gmCubicRatioSquare :
    (volume.prod volume).real gmCubicRatioSquare = 9 / 4 := by
  rw [gmCubicRatioSquare, MeasureTheory.measureReal_prod_prod,
    Real.volume_real_Icc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 2)]
  norm_num

theorem integral_gmCubicFourierIntegrand_eq_ratioSquare
    (cutoff : GMSmoothCutoff) (N : ℕ) (W : Finset ℝ)
    (m : ℤ × (ℤ × ℤ)) :
    (∫ q : ℝ × ℝ, gmCubicFourierIntegrand cutoff N W m q) =
      ∫ q : ℝ × ℝ in gmCubicRatioSquare,
        gmCubicFourierIntegrand cutoff N W m q := by
  symm
  apply MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
  intro q hq
  exact gmCubicFourierIntegrand_eq_zero_of_not_mem_ratioSquare
    cutoff N W m hq

theorem integral_gmCubicFourierIntegrand_split_slab
    (cutoff : GMSmoothCutoff) (η T : ℝ) (N : ℕ) (W : Finset ℝ)
    (m : ℤ × (ℤ × ℤ)) :
    (∫ q : ℝ × ℝ, gmCubicFourierIntegrand cutoff N W m q) =
      (∫ q : ℝ × ℝ in gmCubicCancellationSlab η T N m,
        gmCubicFourierIntegrand cutoff N W m q) +
      (∫ q : ℝ × ℝ in
          gmCubicRatioSquare \ gmCubicCancellationSlab η T N m,
        gmCubicFourierIntegrand cutoff N W m q) := by
  rw [integral_gmCubicFourierIntegrand_eq_ratioSquare]
  have hUnion : gmCubicCancellationSlab η T N m ∪
      (gmCubicRatioSquare \ gmCubicCancellationSlab η T N m) =
        gmCubicRatioSquare := by
    ext q
    simp only [gmCubicCancellationSlab, Set.mem_union, Set.mem_inter_iff,
      Set.mem_diff]
    tauto
  calc
    (∫ q : ℝ × ℝ in gmCubicRatioSquare,
        gmCubicFourierIntegrand cutoff N W m q) =
        ∫ q : ℝ × ℝ in gmCubicCancellationSlab η T N m ∪
            (gmCubicRatioSquare \ gmCubicCancellationSlab η T N m),
          gmCubicFourierIntegrand cutoff N W m q := by rw [hUnion]
    _ = _ := MeasureTheory.setIntegral_union Set.disjoint_sdiff_right
      (measurableSet_gmCubicRatioSquare.diff
        (measurableSet_gmCubicCancellationSlab η T N m))
      (integrable_gmCubicFourierIntegrand cutoff N W m).restrict
      (integrable_gmCubicFourierIntegrand cutoff N W m).restrict

theorem norm_gmCubicFourierIntegrand_slabIntegral_le
    (cutoff : GMSmoothCutoff) {C : ℝ}
    (hC : ∀ {v₁ v₂ ξ : ℝ}, |v₁| ≤ 2 → |v₂| ≤ 2 →
      ‖gmCubicZFourier cutoff v₁ v₂ ξ‖ ≤ C)
    (η T : ℝ) (N : ℕ) (W : Finset ℝ) (m : ℤ × (ℤ × ℤ)) :
    ‖∫ q : ℝ × ℝ in gmCubicCancellationSlab η T N m,
        gmCubicFourierIntegrand cutoff N W m q‖ ≤
      C * gmCubicCancellationMass η T N W m := by
  have hg : Integrable (fun q : ℝ × ℝ =>
      C * gmCubicRAmplitude W q)
      ((volume.prod volume).restrict (gmCubicCancellationSlab η T N m)) :=
    (integrableOn_gmCubicRAmplitude_cancellationSlab η T N W m).const_mul C
  calc
    ‖∫ q : ℝ × ℝ in gmCubicCancellationSlab η T N m,
        gmCubicFourierIntegrand cutoff N W m q‖ ≤
        ∫ q : ℝ × ℝ in gmCubicCancellationSlab η T N m,
          C * gmCubicRAmplitude W q := by
      apply MeasureTheory.norm_integral_le_of_norm_le hg
      filter_upwards [ae_restrict_mem
        (measurableSet_gmCubicCancellationSlab η T N m)] with q hq
      exact norm_gmCubicFourierIntegrand_le_on_slab cutoff hC hq
    _ = C * gmCubicCancellationMass η T N W m := by
      rw [MeasureTheory.integral_const_mul]
      rfl

theorem norm_gmCubicFourierIntegrand_offSlabIntegral_le
    (cutoff : GMSmoothCutoff) {η T : ℝ} {N A : ℕ}
    {W : Finset ℝ} {m : ℤ × (ℤ × ℤ)} {C : ℝ}
    (hT : 1 ≤ T) (hN : 0 < N) (hC : 0 ≤ C)
    (hTail : ∀ {T : ℝ} {N : ℕ} {v₁ v₂ : ℝ}
      {m : ℤ × (ℤ × ℤ)}, 1 ≤ T → 0 < N →
      |v₁| ≤ 2 → |v₂| ≤ 2 →
      T ^ η / (N : ℝ) ≤
        |(m.1 : ℝ) * v₁ + (m.2.1 : ℝ) * v₂ + (m.2.2 : ℝ)| →
      ‖gmCubicZFourier cutoff v₁ v₂
        ((N : ℝ) * ((m.1 : ℝ) * v₁ + (m.2.1 : ℝ) * v₂ +
          (m.2.2 : ℝ)))‖ ≤ C / T ^ A) :
    ‖∫ q : ℝ × ℝ in
        gmCubicRatioSquare \ gmCubicCancellationSlab η T N m,
        gmCubicFourierIntegrand cutoff N W m q‖ ≤
      (C / T ^ A) * (W.card : ℝ) ^ 3 * (9 / 4) := by
  let s := gmCubicRatioSquare \ gmCubicCancellationSlab η T N m
  have hsSub : s ⊆ gmCubicRatioSquare := diff_subset
  have hsFinite : (volume.prod volume) s < (⊤ : ENNReal) :=
    lt_of_le_of_lt (measure_mono hsSub)
      (isCompact_Icc.prod isCompact_Icc).measure_lt_top
  have hconst : 0 ≤ (C / T ^ A) * (W.card : ℝ) ^ 3 := by
    positivity
  have hraw := MeasureTheory.norm_setIntegral_le_of_norm_le_const
    (f := gmCubicFourierIntegrand cutoff N W m) hsFinite
      (fun q hq => norm_gmCubicFourierIntegrand_le_off_slab
        cutoff hT hN hTail hq)
  calc
    ‖∫ q : ℝ × ℝ in s,
        gmCubicFourierIntegrand cutoff N W m q‖ ≤
        (C / T ^ A) * (W.card : ℝ) ^ 3 *
          (volume.prod volume).real s := hraw
    _ ≤ (C / T ^ A) * (W.card : ℝ) ^ 3 *
          (volume.prod volume).real gmCubicRatioSquare := by
      gcongr
      exact ((isCompact_Icc.prod isCompact_Icc).measure_lt_top
        (μ := volume.prod volume)).ne
    _ = (C / T ^ A) * (W.card : ℝ) ^ 3 * (9 / 4) := by
      rw [volume_real_gmCubicRatioSquare]

theorem gmCubicCancellationMass_nonneg
    (η T : ℝ) (N : ℕ) (W : Finset ℝ) (m : ℤ × (ℤ × ℤ)) :
    0 ≤ gmCubicCancellationMass η T N W m := by
  unfold gmCubicCancellationMass
  apply MeasureTheory.integral_nonneg_of_ae
  exact Filter.Eventually.of_forall (gmCubicRAmplitude_nonneg W)

private theorem cubic_mode_far_error_le
    {C T : ℝ} {N : ℕ} {R : ℝ}
    (hC : 0 ≤ C) (hT : 1 ≤ T) (hN : (N : ℝ) ≤ T)
    (hR0 : 0 ≤ R) (hR : R ≤ 2 * T) :
    (N : ℝ) ^ 3 * ((C / T ^ 206) * R ^ 3 * (9 / 4)) ≤
      18 * C / T ^ 200 := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hN0 : 0 ≤ (N : ℝ) := by positivity
  have hNpow : (N : ℝ) ^ 3 ≤ T ^ 3 := by gcongr
  have hRpow : R ^ 3 ≤ (2 * T) ^ 3 := by gcongr
  have hprod : (N : ℝ) ^ 3 * R ^ 3 ≤ 8 * T ^ 6 := by
    calc
      (N : ℝ) ^ 3 * R ^ 3 ≤ T ^ 3 * (2 * T) ^ 3 :=
        mul_le_mul hNpow hRpow (by positivity) (by positivity)
      _ = 8 * T ^ 6 := by ring
  calc
    (N : ℝ) ^ 3 * ((C / T ^ 206) * R ^ 3 * (9 / 4)) =
        (C * ((N : ℝ) ^ 3 * R ^ 3) * (9 / 4)) / T ^ 206 := by ring
    _ ≤ (C * (8 * T ^ 6) * (9 / 4)) / T ^ 206 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      gcongr
    _ = 18 * C / T ^ 200 := by
      field_simp
      ring

/-- Guth--Maynard Proposition 7.1 for one genuinely nonzero frequency
triple.  The main term is the literal cancellation-slab integral of the
three source exponential sums, and the error includes the outer `N^3`, the
trivial `|W|^3` loss, and the full ratio-square volume. -/
theorem gmCubicS3Mode_prop7_1
    (cutoff : GMSmoothCutoff) (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ {T : ℝ} {N : ℕ} {W : Finset ℝ}
      {m : ℤ × (ℤ × ℤ)},
      1 ≤ T → 0 < N → (N : ℝ) ≤ T →
      IsSeparated 1 W → InBaseInterval T W →
      m.1 ≠ 0 → m.2.1 ≠ 0 → m.2.2 ≠ 0 →
      ‖gmCubicS3Mode cutoff N W m‖ ≤
        C * (N : ℝ) ^ 3 * gmCubicCancellationMass η T N W m +
          C / T ^ 200 := by
  obtain ⟨C₀, hC₀, hZeroRaw⟩ := gmCubicZFourier_uniform_decay cutoff 0
  have hZero : ∀ {v₁ v₂ ξ : ℝ}, |v₁| ≤ 2 → |v₂| ≤ 2 →
      ‖gmCubicZFourier cutoff v₁ v₂ ξ‖ ≤ C₀ := by
    intro v₁ v₂ ξ hv₁ hv₂
    simpa using hZeroRaw hv₁ hv₂
  obtain ⟨C₁, hC₁, hTail⟩ :=
    gmCubicZFourier_cancellation_pow cutoff η hη 206
  let C : ℝ := C₀ + 18 * C₁ + 1
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro T N W m hT hN hNT hSep hW hm1 hm2 hm3
  have hCard : (W.card : ℝ) ≤ 2 * T :=
    gmSeparated_card_le_two_height hT hSep hW
  have hIn := norm_gmCubicFourierIntegrand_slabIntegral_le
    cutoff hZero η T N W m
  have hOut := norm_gmCubicFourierIntegrand_offSlabIntegral_le
    (W := W) (m := m) (A := 206) cutoff hT hN hC₁ hTail
  have hSplit := integral_gmCubicFourierIntegrand_split_slab
    cutoff η T N W m
  let I : ℂ := ∫ q : ℝ × ℝ,
    gmCubicFourierIntegrand cutoff N W m q
  let I₀ : ℂ := ∫ q : ℝ × ℝ in gmCubicCancellationSlab η T N m,
    gmCubicFourierIntegrand cutoff N W m q
  let I₁ : ℂ := ∫ q : ℝ × ℝ in
      gmCubicRatioSquare \ gmCubicCancellationSlab η T N m,
    gmCubicFourierIntegrand cutoff N W m q
  have hSplit' : I = I₀ + I₁ := hSplit
  have hINorm : ‖I‖ ≤
      C₀ * gmCubicCancellationMass η T N W m +
        (C₁ / T ^ 206) * (W.card : ℝ) ^ 3 * (9 / 4) := by
    calc
      ‖I‖ = ‖I₀ + I₁‖ := by rw [hSplit']
      _ ≤ ‖I₀‖ + ‖I₁‖ := norm_add_le _ _
      _ ≤ C₀ * gmCubicCancellationMass η T N W m +
          (C₁ / T ^ 206) * (W.card : ℝ) ^ 3 * (9 / 4) :=
        add_le_add hIn hOut
  rw [gmCubicS3Mode_eq_fourierIntegral cutoff N W m hm1 hm2 hm3,
    gmCubicS3FourierIntegral_eq_integral]
  change ‖(N : ℂ) ^ 3 * I‖ ≤ _
  rw [norm_mul, norm_pow, Complex.norm_natCast]
  have hMass := gmCubicCancellationMass_nonneg η T N W m
  have hFar : (N : ℝ) ^ 3 *
      ((C₁ / T ^ 206) * (W.card : ℝ) ^ 3 * (9 / 4)) ≤
        18 * C₁ / T ^ 200 :=
    cubic_mode_far_error_le hC₁ hT hNT (by positivity) hCard
  have hC₀le : C₀ ≤ C := by dsimp only [C]; linarith
  have hC₁le : 18 * C₁ ≤ C := by dsimp only [C]; linarith
  calc
    (N : ℝ) ^ 3 * ‖I‖ ≤
        (N : ℝ) ^ 3 *
          (C₀ * gmCubicCancellationMass η T N W m +
            (C₁ / T ^ 206) * (W.card : ℝ) ^ 3 * (9 / 4)) := by
      gcongr
    _ = C₀ * (N : ℝ) ^ 3 * gmCubicCancellationMass η T N W m +
          (N : ℝ) ^ 3 *
            ((C₁ / T ^ 206) * (W.card : ℝ) ^ 3 * (9 / 4)) := by ring
    _ ≤ C * (N : ℝ) ^ 3 * gmCubicCancellationMass η T N W m +
          18 * C₁ / T ^ 200 := by
      apply add_le_add
      · gcongr
      · exact hFar
    _ ≤ C * (N : ℝ) ^ 3 * gmCubicCancellationMass η T N W m +
          C / T ^ 200 := by
      gcongr

/-- The geometric second assertion in Guth--Maynard Proposition 7.1.
On the source ratio square, a cancellation slab of width at most one can
meet an ordered nonzero frequency triple only when the two largest
frequencies are comparable.  The harmless explicit constant `5` records
the two ratio bounds and the unit slab width. -/
theorem gmCubicCancellationSlab_ordered_comparable
    {η T : ℝ} {N : ℕ} {m : ℤ × (ℤ × ℤ)} {q : ℝ × ℝ}
    (hq : q ∈ gmCubicCancellationSlab η T N m)
    (hwidth : T ^ η / (N : ℝ) ≤ 1)
    (hm2 : m.2.1 ≠ 0)
    (h12 : |(m.1 : ℝ)| ≤ |(m.2.1 : ℝ)|) :
    |(m.2.2 : ℝ)| ≤ 5 * |(m.2.1 : ℝ)| := by
  have hq1 : |q.1| ≤ 2 := by
    rw [abs_of_nonneg (le_trans (by norm_num) hq.1.1.1)]
    exact hq.1.1.2
  have hq2 : |q.2| ≤ 2 := by
    rw [abs_of_nonneg (le_trans (by norm_num) hq.1.2.1)]
    exact hq.1.2.2
  have hcancel :
      |(m.1 : ℝ) * q.1 + (m.2.1 : ℝ) * q.2 + (m.2.2 : ℝ)| ≤ 1 :=
    hq.2.trans hwidth
  have hm2oneInt : (1 : ℤ) ≤ |m.2.1| := by
    rcases lt_or_gt_of_ne hm2 with hmneg | hmpos
    · rw [abs_of_neg hmneg]
      omega
    · rw [abs_of_pos hmpos]
      omega
  have hm2one : (1 : ℝ) ≤ |(m.2.1 : ℝ)| := by
    exact_mod_cast hm2oneInt
  have hmul1 : |(m.1 : ℝ)| * |q.1| ≤ 2 * |(m.1 : ℝ)| := by
    simpa [mul_comm] using
      (mul_le_mul_of_nonneg_left hq1 (abs_nonneg (m.1 : ℝ)))
  have hmul2 : |(m.2.1 : ℝ)| * |q.2| ≤ 2 * |(m.2.1 : ℝ)| := by
    simpa [mul_comm] using
      (mul_le_mul_of_nonneg_left hq2 (abs_nonneg (m.2.1 : ℝ)))
  calc
    |(m.2.2 : ℝ)| =
        |((m.1 : ℝ) * q.1 + (m.2.1 : ℝ) * q.2 + (m.2.2 : ℝ)) -
          ((m.1 : ℝ) * q.1 + (m.2.1 : ℝ) * q.2)| := by ring_nf
    _ ≤ |(m.1 : ℝ) * q.1 + (m.2.1 : ℝ) * q.2 + (m.2.2 : ℝ)| +
          |(m.1 : ℝ) * q.1 + (m.2.1 : ℝ) * q.2| := abs_sub _ _
    _ ≤ 1 + (|(m.1 : ℝ) * q.1| + |(m.2.1 : ℝ) * q.2|) := by
      gcongr
      exact abs_add_le _ _
    _ = 1 + (|(m.1 : ℝ)| * |q.1| + |(m.2.1 : ℝ)| * |q.2|) := by
      rw [abs_mul, abs_mul]
    _ ≤ 1 + (2 * |(m.1 : ℝ)| + 2 * |(m.2.1 : ℝ)|) := by
      gcongr
    _ ≤ 1 + 4 * |(m.2.1 : ℝ)| := by
      gcongr
      nlinarith [abs_nonneg (m.1 : ℝ), abs_nonneg (m.2.1 : ℝ)]
    _ ≤ 5 * |(m.2.1 : ℝ)| := by linarith

/-- An ordered frequency triple outside the Proposition 7.1 comparability
range has an empty cancellation slab. -/
theorem gmCubicCancellationSlab_eq_empty_of_unbalanced
    {η T : ℝ} {N : ℕ} {m : ℤ × (ℤ × ℤ)}
    (hwidth : T ^ η / (N : ℝ) ≤ 1)
    (hm2 : m.2.1 ≠ 0)
    (h12 : |(m.1 : ℝ)| ≤ |(m.2.1 : ℝ)|)
    (h23 : 5 * |(m.2.1 : ℝ)| < |(m.2.2 : ℝ)|) :
    gmCubicCancellationSlab η T N m = ∅ := by
  ext q
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hq
  exact (not_le_of_gt h23)
    (gmCubicCancellationSlab_ordered_comparable hq hwidth hm2 h12)

theorem gmCubicCancellationMass_eq_zero_of_unbalanced
    {η T : ℝ} {N : ℕ} {W : Finset ℝ} {m : ℤ × (ℤ × ℤ)}
    (hwidth : T ^ η / (N : ℝ) ≤ 1)
    (hm2 : m.2.1 ≠ 0)
    (h12 : |(m.1 : ℝ)| ≤ |(m.2.1 : ℝ)|)
    (h23 : 5 * |(m.2.1 : ℝ)| < |(m.2.2 : ℝ)|) :
    gmCubicCancellationMass η T N W m = 0 := by
  rw [gmCubicCancellationMass,
    gmCubicCancellationSlab_eq_empty_of_unbalanced hwidth hm2 h12 h23]
  simp

/-- The source range `N ≥ T^(2/3)` makes the Proposition 7.1
cancellation width at most one for every `η ≤ 2/3`. -/
theorem gmCubicCancellationWidth_le_one
    {η T : ℝ} {N : ℕ} (hT : 1 ≤ T) (hη : η ≤ 2 / 3)
    (hN : T ^ (2 / 3 : ℝ) ≤ (N : ℝ)) :
    T ^ η / (N : ℝ) ≤ 1 := by
  have hNpos : 0 < (N : ℝ) :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hT) _)
      hN
  rw [div_le_one hNpos]
  exact (Real.rpow_le_rpow_of_exponent_le hT hη).trans hN

/-- The negligible unbalanced-frequency conclusion in the ordered form of
Guth--Maynard Proposition 7.1. -/
theorem gmCubicS3Mode_unbalanced_prop7_1
    (cutoff : GMSmoothCutoff) (η : ℝ) (hηpos : 0 < η)
    (hηupper : η ≤ 2 / 3) :
    ∃ C : ℝ, 0 < C ∧ ∀ {T : ℝ} {N : ℕ} {W : Finset ℝ}
      {m : ℤ × (ℤ × ℤ)},
      1 ≤ T → 0 < N → (N : ℝ) ≤ T →
      T ^ (2 / 3 : ℝ) ≤ (N : ℝ) →
      IsSeparated 1 W → InBaseInterval T W →
      m.1 ≠ 0 → m.2.1 ≠ 0 → m.2.2 ≠ 0 →
      |(m.1 : ℝ)| ≤ |(m.2.1 : ℝ)| →
      5 * |(m.2.1 : ℝ)| < |(m.2.2 : ℝ)| →
      ‖gmCubicS3Mode cutoff N W m‖ ≤ C / T ^ 200 := by
  obtain ⟨C, hC, hMode⟩ := gmCubicS3Mode_prop7_1 cutoff η hηpos
  refine ⟨C, hC, ?_⟩
  intro T N W m hT hN hNT hNlower hSep hBase hm1 hm2 hm3 h12 h23
  have hwidth := gmCubicCancellationWidth_le_one hT hηupper hNlower
  have hmass := gmCubicCancellationMass_eq_zero_of_unbalanced
    (W := W) hwidth hm2 h12 h23
  simpa [hmass] using hMode hT hN hNT hSep hBase hm1 hm2 hm3

/-- Simultaneously reversing the ordinate difference and the integer
frequency conjugates one nonzero scaled trace mode. -/
theorem gmNonzeroScaledTraceMode_neg_neg_eq_star
    (cutoff : GMSmoothCutoff) (N : ℕ) (t : ℝ) (m : ℤ) :
    gmNonzeroScaledTraceMode cutoff N (-t) (-m) =
      star (gmNonzeroScaledTraceMode cutoff N t m) := by
  by_cases hm : m = 0
  · subst m
    simp [gmNonzeroScaledTraceMode]
  · have hneg : -m ≠ 0 := neg_ne_zero.mpr hm
    simp only [gmNonzeroScaledTraceMode, if_neg hm, if_neg hneg,
      gmScaledTraceMode]
    have hfreq : (N : ℝ) * ((-m : ℤ) : ℝ) =
        -((N : ℝ) * (m : ℝ)) := by push_cast; ring
    rw [hfreq, gmTraceFourier_neg_eq_conj cutoff (-t), neg_neg]
    simp

/-- Cyclically rotating the three frequencies leaves the exact cubic mode
unchanged. -/
theorem gmCubicS3Mode_cyclic
    (cutoff : GMSmoothCutoff) (N : ℕ) (W : Finset ℝ)
    (m₁ m₂ m₃ : ℤ) :
    gmCubicS3Mode cutoff N W (m₁, (m₂, m₃)) =
      gmCubicS3Mode cutoff N W (m₂, (m₃, m₁)) := by
  unfold gmCubicS3Mode
  calc
    (∑ t : GMRow W, ∑ u : GMRow W, ∑ v : GMRow W,
        gmNonzeroScaledTraceMode cutoff N ((t : ℝ) - (u : ℝ)) m₁ *
          gmNonzeroScaledTraceMode cutoff N ((u : ℝ) - (v : ℝ)) m₂ *
            gmNonzeroScaledTraceMode cutoff N ((v : ℝ) - (t : ℝ)) m₃) =
        ∑ u : GMRow W, ∑ t : GMRow W, ∑ v : GMRow W,
        gmNonzeroScaledTraceMode cutoff N ((t : ℝ) - (u : ℝ)) m₁ *
          gmNonzeroScaledTraceMode cutoff N ((u : ℝ) - (v : ℝ)) m₂ *
            gmNonzeroScaledTraceMode cutoff N ((v : ℝ) - (t : ℝ)) m₃ := by
      rw [Finset.sum_comm]
    _ = ∑ u : GMRow W, ∑ v : GMRow W, ∑ t : GMRow W,
        gmNonzeroScaledTraceMode cutoff N ((t : ℝ) - (u : ℝ)) m₁ *
          gmNonzeroScaledTraceMode cutoff N ((u : ℝ) - (v : ℝ)) m₂ *
            gmNonzeroScaledTraceMode cutoff N ((v : ℝ) - (t : ℝ)) m₃ := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [Finset.sum_comm]
    _ = ∑ u : GMRow W, ∑ v : GMRow W, ∑ t : GMRow W,
        gmNonzeroScaledTraceMode cutoff N ((u : ℝ) - (v : ℝ)) m₂ *
          gmNonzeroScaledTraceMode cutoff N ((v : ℝ) - (t : ℝ)) m₃ *
            gmNonzeroScaledTraceMode cutoff N ((t : ℝ) - (u : ℝ)) m₁ := by
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro v hv
      apply Finset.sum_congr rfl
      intro t ht
      ring
    _ = _ := by rfl

/-- Swapping the first two absolute frequencies (and simultaneously
reversing all three signs) conjugates the exact mode.  Together with cyclic
rotation this supplies the full sixfold sorting symmetry used in (7.6). -/
theorem gmCubicS3Mode_swap12_neg_eq_star
    (cutoff : GMSmoothCutoff) (N : ℕ) (W : Finset ℝ)
    (m₁ m₂ m₃ : ℤ) :
  gmCubicS3Mode cutoff N W (-m₂, (-m₁, -m₃)) =
      star (gmCubicS3Mode cutoff N W (m₁, (m₂, m₃))) := by
  unfold gmCubicS3Mode
  calc
    (∑ t : GMRow W, ∑ u : GMRow W, ∑ v : GMRow W,
        gmNonzeroScaledTraceMode cutoff N ((t : ℝ) - (u : ℝ)) (-m₂) *
          gmNonzeroScaledTraceMode cutoff N ((u : ℝ) - (v : ℝ)) (-m₁) *
            gmNonzeroScaledTraceMode cutoff N ((v : ℝ) - (t : ℝ)) (-m₃)) =
        ∑ t : GMRow W, ∑ v : GMRow W, ∑ u : GMRow W,
        gmNonzeroScaledTraceMode cutoff N ((t : ℝ) - (u : ℝ)) (-m₂) *
          gmNonzeroScaledTraceMode cutoff N ((u : ℝ) - (v : ℝ)) (-m₁) *
            gmNonzeroScaledTraceMode cutoff N ((v : ℝ) - (t : ℝ)) (-m₃) := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [Finset.sum_comm]
    _ = ∑ v : GMRow W, ∑ t : GMRow W, ∑ u : GMRow W,
        gmNonzeroScaledTraceMode cutoff N ((t : ℝ) - (u : ℝ)) (-m₂) *
          gmNonzeroScaledTraceMode cutoff N ((u : ℝ) - (v : ℝ)) (-m₁) *
            gmNonzeroScaledTraceMode cutoff N ((v : ℝ) - (t : ℝ)) (-m₃) := by
      rw [Finset.sum_comm]
    _ = ∑ v : GMRow W, ∑ u : GMRow W, ∑ t : GMRow W,
        gmNonzeroScaledTraceMode cutoff N ((t : ℝ) - (u : ℝ)) (-m₂) *
          gmNonzeroScaledTraceMode cutoff N ((u : ℝ) - (v : ℝ)) (-m₁) *
            gmNonzeroScaledTraceMode cutoff N ((v : ℝ) - (t : ℝ)) (-m₃) := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [Finset.sum_comm]
    _ = ∑ v : GMRow W, ∑ u : GMRow W, ∑ t : GMRow W,
        star (gmNonzeroScaledTraceMode cutoff N ((v : ℝ) - (u : ℝ)) m₁) *
          star (gmNonzeroScaledTraceMode cutoff N ((u : ℝ) - (t : ℝ)) m₂) *
            star (gmNonzeroScaledTraceMode cutoff N ((t : ℝ) - (v : ℝ)) m₃) := by
      apply Finset.sum_congr rfl
      intro v hv
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro t ht
      rw [show (t : ℝ) - (u : ℝ) = -((u : ℝ) - (t : ℝ)) by ring,
        show (u : ℝ) - (v : ℝ) = -((v : ℝ) - (u : ℝ)) by ring,
        show (v : ℝ) - (t : ℝ) = -((t : ℝ) - (v : ℝ)) by ring,
        gmNonzeroScaledTraceMode_neg_neg_eq_star,
        gmNonzeroScaledTraceMode_neg_neg_eq_star,
        gmNonzeroScaledTraceMode_neg_neg_eq_star]
      ring
    _ = _ := by
      simp only [star_sum, star_mul]
      apply Finset.sum_congr rfl
      intro t ht
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro v hv
      ring

theorem norm_gmCubicS3Mode_swap12_neg
    (cutoff : GMSmoothCutoff) (N : ℕ) (W : Finset ℝ)
    (m₁ m₂ m₃ : ℤ) :
    ‖gmCubicS3Mode cutoff N W (-m₂, (-m₁, -m₃))‖ =
      ‖gmCubicS3Mode cutoff N W (m₁, (m₂, m₃))‖ := by
  rw [gmCubicS3Mode_swap12_neg_eq_star, norm_star]

theorem norm_gmCubicS3Mode_cyclic
    (cutoff : GMSmoothCutoff) (N : ℕ) (W : Finset ℝ)
    (m₁ m₂ m₃ : ℤ) :
    ‖gmCubicS3Mode cutoff N W (m₁, (m₂, m₃))‖ =
      ‖gmCubicS3Mode cutoff N W (m₂, (m₃, m₁))‖ := by
  rw [gmCubicS3Mode_cyclic]

theorem norm_gmCubicS3Mode_cyclic_two
    (cutoff : GMSmoothCutoff) (N : ℕ) (W : Finset ℝ)
    (m₁ m₂ m₃ : ℤ) :
    ‖gmCubicS3Mode cutoff N W (m₁, (m₂, m₃))‖ =
      ‖gmCubicS3Mode cutoff N W (m₃, (m₁, m₂))‖ := by
  calc
    ‖gmCubicS3Mode cutoff N W (m₁, (m₂, m₃))‖ =
        ‖gmCubicS3Mode cutoff N W (m₂, (m₃, m₁))‖ :=
      norm_gmCubicS3Mode_cyclic cutoff N W m₁ m₂ m₃
    _ = ‖gmCubicS3Mode cutoff N W (m₃, (m₁, m₂))‖ :=
      norm_gmCubicS3Mode_cyclic cutoff N W m₂ m₃ m₁

/-- The six signed permutations generated by cyclic rotation and the
conjugating transposition.  Their absolute-coordinate triples are exactly
the six ordinary permutations. -/
def gmCubicSignedPermutations (m : ℤ × (ℤ × ℤ)) :
    Finset (ℤ × (ℤ × ℤ)) :=
  { (m.1, (m.2.1, m.2.2)),
    (m.2.1, (m.2.2, m.1)),
    (m.2.2, (m.1, m.2.1)),
    (-m.2.1, (-m.1, -m.2.2)),
    (-m.1, (-m.2.2, -m.2.1)),
    (-m.2.2, (-m.2.1, -m.1)) }

/-- Every genuinely nonzero triple has a source-equivalent representative
with ordered absolute frequencies.  The representative remains in every
symmetric source box containing the original triple.  This is the exact
sixfold finite reindexing needed before the dyadic selection in (7.6). -/
theorem exists_ordered_gmCubicS3Mode
    (cutoff : GMSmoothCutoff) (N : ℕ) (W : Finset ℝ)
    (m : ℤ × (ℤ × ℤ))
    (hm1 : m.1 ≠ 0) (hm2 : m.2.1 ≠ 0) (hm3 : m.2.2 ≠ 0) :
    ∃ n : ℤ × (ℤ × ℤ),
      n.1 ≠ 0 ∧ n.2.1 ≠ 0 ∧ n.2.2 ≠ 0 ∧
      |(n.1 : ℝ)| ≤ |(n.2.1 : ℝ)| ∧
      |(n.2.1 : ℝ)| ≤ |(n.2.2 : ℝ)| ∧
      ‖gmCubicS3Mode cutoff N W n‖ =
        ‖gmCubicS3Mode cutoff N W m‖ ∧
      m ∈ gmCubicSignedPermutations n ∧
      ∀ H, m ∈ gmCubicFrequencyBox H → n ∈ gmCubicFrequencyBox H := by
  let a := m.1
  let b := m.2.1
  let c := m.2.2
  have ha : a ≠ 0 := hm1
  have hb : b ≠ 0 := hm2
  have hc : c ≠ 0 := hm3
  rcases le_total |(a : ℝ)| |(b : ℝ)| with hab | hba
  · rcases le_total |(b : ℝ)| |(c : ℝ)| with hbc | hcb
    · refine ⟨(a, (b, c)), ha, hb, hc, hab, hbc, rfl, ?_⟩
      constructor
      · dsimp only [a, b, c]
        simp [gmCubicSignedPermutations]
      · intro H hbox
        exact hbox
    · rcases le_total |(a : ℝ)| |(c : ℝ)| with hac | hca
      · refine ⟨(-a, (-c, -b)), neg_ne_zero.mpr ha, neg_ne_zero.mpr hc,
          neg_ne_zero.mpr hb, ?_, ?_, ?_, ?_⟩
        · simpa only [Int.cast_neg, abs_neg] using hac
        · simpa only [Int.cast_neg, abs_neg] using hcb
        · calc
            ‖gmCubicS3Mode cutoff N W (-a, (-c, -b))‖ =
                ‖gmCubicS3Mode cutoff N W (c, (a, b))‖ :=
              norm_gmCubicS3Mode_swap12_neg cutoff N W c a b
            _ = ‖gmCubicS3Mode cutoff N W (a, (b, c))‖ :=
              (norm_gmCubicS3Mode_cyclic_two cutoff N W a b c).symm
            _ = ‖gmCubicS3Mode cutoff N W m‖ := by rfl
        · constructor
          · dsimp only [a, b, c]
            simp [gmCubicSignedPermutations]
          · intro H hbox
            rw [mem_gmCubicFrequencyBox] at hbox ⊢
            dsimp only [a, b, c] at hbox ⊢
            omega
      · refine ⟨(c, (a, b)), hc, ha, hb, hca, hab, ?_, ?_⟩
        · calc
            ‖gmCubicS3Mode cutoff N W (c, (a, b))‖ =
                ‖gmCubicS3Mode cutoff N W (a, (b, c))‖ :=
              (norm_gmCubicS3Mode_cyclic_two cutoff N W a b c).symm
            _ = ‖gmCubicS3Mode cutoff N W m‖ := by rfl
        · constructor
          · dsimp only [a, b, c]
            simp [gmCubicSignedPermutations]
          · intro H hbox
            rw [mem_gmCubicFrequencyBox] at hbox ⊢
            dsimp only [a, b, c] at hbox ⊢
            omega
  · rcases le_total |(a : ℝ)| |(c : ℝ)| with hac | hca
    · refine ⟨(-b, (-a, -c)), neg_ne_zero.mpr hb, neg_ne_zero.mpr ha,
        neg_ne_zero.mpr hc, ?_, ?_, ?_, ?_⟩
      · simpa only [Int.cast_neg, abs_neg] using hba
      · simpa only [Int.cast_neg, abs_neg] using hac
      · calc
          ‖gmCubicS3Mode cutoff N W (-b, (-a, -c))‖ =
              ‖gmCubicS3Mode cutoff N W (a, (b, c))‖ :=
            norm_gmCubicS3Mode_swap12_neg cutoff N W a b c
          _ = ‖gmCubicS3Mode cutoff N W m‖ := by rfl
      · constructor
        · dsimp only [a, b, c]
          simp [gmCubicSignedPermutations]
        · intro H hbox
          rw [mem_gmCubicFrequencyBox] at hbox ⊢
          dsimp only [a, b, c] at hbox ⊢
          omega
    · rcases le_total |(b : ℝ)| |(c : ℝ)| with hbc | hcb
      · refine ⟨(b, (c, a)), hb, hc, ha, hbc, hca, ?_, ?_⟩
        · calc
            ‖gmCubicS3Mode cutoff N W (b, (c, a))‖ =
                ‖gmCubicS3Mode cutoff N W (a, (b, c))‖ :=
              (norm_gmCubicS3Mode_cyclic cutoff N W a b c).symm
            _ = ‖gmCubicS3Mode cutoff N W m‖ := by rfl
        · constructor
          · dsimp only [a, b, c]
            simp [gmCubicSignedPermutations]
          · intro H hbox
            rw [mem_gmCubicFrequencyBox] at hbox ⊢
            dsimp only [a, b, c] at hbox ⊢
            omega
      · refine ⟨(-c, (-b, -a)), neg_ne_zero.mpr hc, neg_ne_zero.mpr hb,
          neg_ne_zero.mpr ha, ?_, ?_, ?_, ?_⟩
        · simpa only [Int.cast_neg, abs_neg] using hcb
        · simpa only [Int.cast_neg, abs_neg] using hba
        · calc
            ‖gmCubicS3Mode cutoff N W (-c, (-b, -a))‖ =
                ‖gmCubicS3Mode cutoff N W (b, (c, a))‖ :=
              norm_gmCubicS3Mode_swap12_neg cutoff N W b c a
            _ = ‖gmCubicS3Mode cutoff N W (a, (b, c))‖ :=
              (norm_gmCubicS3Mode_cyclic cutoff N W a b c).symm
            _ = ‖gmCubicS3Mode cutoff N W m‖ := by rfl
        · constructor
          · dsimp only [a, b, c]
            simp [gmCubicSignedPermutations]
          · intro H hbox
            rw [mem_gmCubicFrequencyBox] at hbox ⊢
            dsimp only [a, b, c] at hbox ⊢
            omega

/-- The finite nonzero source box occurring in (7.1). -/
noncomputable def gmCubicNonzeroFrequencyBox (H : ℕ) :
    Finset (ℤ × (ℤ × ℤ)) :=
  (gmCubicFrequencyBox H).filter fun m =>
    m.1 ≠ 0 ∧ m.2.1 ≠ 0 ∧ m.2.2 ≠ 0

/-- The ordered sixth of the nonzero source box. -/
noncomputable def gmCubicOrderedFrequencyBox (H : ℕ) :
    Finset (ℤ × (ℤ × ℤ)) :=
  (gmCubicNonzeroFrequencyBox H).filter fun m =>
    |(m.1 : ℝ)| ≤ |(m.2.1 : ℝ)| ∧
      |(m.2.1 : ℝ)| ≤ |(m.2.2 : ℝ)|

@[simp]
theorem mem_gmCubicNonzeroFrequencyBox {H : ℕ} {m : ℤ × (ℤ × ℤ)} :
    m ∈ gmCubicNonzeroFrequencyBox H ↔
      m ∈ gmCubicFrequencyBox H ∧
        m.1 ≠ 0 ∧ m.2.1 ≠ 0 ∧ m.2.2 ≠ 0 := by
  simp [gmCubicNonzeroFrequencyBox]

@[simp]
theorem mem_gmCubicOrderedFrequencyBox {H : ℕ} {m : ℤ × (ℤ × ℤ)} :
    m ∈ gmCubicOrderedFrequencyBox H ↔
      m ∈ gmCubicNonzeroFrequencyBox H ∧
      |(m.1 : ℝ)| ≤ |(m.2.1 : ℝ)| ∧
      |(m.2.1 : ℝ)| ≤ |(m.2.2 : ℝ)| := by
  simp [gmCubicOrderedFrequencyBox]

theorem norm_gmCubicS3Mode_eq_of_mem_signedPermutations
    (cutoff : GMSmoothCutoff) (N : ℕ) (W : Finset ℝ)
    {m p : ℤ × (ℤ × ℤ)} (hp : p ∈ gmCubicSignedPermutations m) :
    ‖gmCubicS3Mode cutoff N W p‖ =
      ‖gmCubicS3Mode cutoff N W m‖ := by
  simp only [gmCubicSignedPermutations, Finset.mem_insert,
    Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · rfl
  · exact (norm_gmCubicS3Mode_cyclic cutoff N W m.1 m.2.1 m.2.2).symm
  · exact (norm_gmCubicS3Mode_cyclic_two cutoff N W m.1 m.2.1 m.2.2).symm
  · exact norm_gmCubicS3Mode_swap12_neg cutoff N W m.1 m.2.1 m.2.2
  · calc
      ‖gmCubicS3Mode cutoff N W (-m.1, (-m.2.2, -m.2.1))‖ =
          ‖gmCubicS3Mode cutoff N W (m.2.2, (m.1, m.2.1))‖ :=
        norm_gmCubicS3Mode_swap12_neg cutoff N W m.2.2 m.1 m.2.1
      _ = ‖gmCubicS3Mode cutoff N W m‖ :=
        (norm_gmCubicS3Mode_cyclic_two cutoff N W
          m.1 m.2.1 m.2.2).symm
  · calc
      ‖gmCubicS3Mode cutoff N W (-m.2.2, (-m.2.1, -m.1))‖ =
          ‖gmCubicS3Mode cutoff N W (m.2.1, (m.2.2, m.1))‖ :=
        norm_gmCubicS3Mode_swap12_neg cutoff N W m.2.1 m.2.2 m.1
      _ = ‖gmCubicS3Mode cutoff N W m‖ :=
        (norm_gmCubicS3Mode_cyclic cutoff N W m.1 m.2.1 m.2.2).symm

theorem gmCubicSignedPermutations_card_le_six (m : ℤ × (ℤ × ℤ)) :
    (gmCubicSignedPermutations m).card ≤ 6 := by
  exact Finset.card_le_six

theorem sum_norm_gmCubicSignedPermutations_le
    (cutoff : GMSmoothCutoff) (N : ℕ) (W : Finset ℝ)
    (m : ℤ × (ℤ × ℤ)) :
    (∑ p ∈ gmCubicSignedPermutations m,
      ‖gmCubicS3Mode cutoff N W p‖) ≤
        6 * ‖gmCubicS3Mode cutoff N W m‖ := by
  have hcard : ((gmCubicSignedPermutations m).card : ℝ) ≤ 6 := by
    exact_mod_cast gmCubicSignedPermutations_card_le_six m
  calc
    (∑ p ∈ gmCubicSignedPermutations m,
        ‖gmCubicS3Mode cutoff N W p‖) =
        ∑ p ∈ gmCubicSignedPermutations m,
          ‖gmCubicS3Mode cutoff N W m‖ := by
      apply Finset.sum_congr rfl
      intro p hp
      exact norm_gmCubicS3Mode_eq_of_mem_signedPermutations cutoff N W hp
    _ = (gmCubicSignedPermutations m).card *
          ‖gmCubicS3Mode cutoff N W m‖ := by simp
    _ ≤ 6 * ‖gmCubicS3Mode cutoff N W m‖ := by
      gcongr

private theorem sum_union_le_sum_add
    {α : Type*} [DecidableEq α] (s t : Finset α) (f : α → ℝ)
    (hf : ∀ x, 0 ≤ f x) :
    ∑ x ∈ s ∪ t, f x ≤ (∑ x ∈ s, f x) + ∑ x ∈ t, f x := by
  have hdisj : Disjoint s (t \ s) := by
    exact Finset.disjoint_sdiff
  have hunion : s ∪ (t \ s) = s ∪ t := by ext x; simp
  rw [← hunion, Finset.sum_union hdisj]
  have hs : (∑ x ∈ t \ s, f x) ≤ ∑ x ∈ t, f x :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.sdiff_subset) (by
    intro x hxt hxs
    exact hf x)
  simpa only [add_comm] using (add_le_add_left hs (∑ x ∈ s, f x))

private theorem sum_biUnion_le_sum_sum
    {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (s : Finset ι) (t : ι → Finset α) (f : α → ℝ)
    (hf : ∀ x, 0 ≤ f x) :
    (∑ x ∈ s.biUnion t, f x) ≤
      ∑ i ∈ s, ∑ x ∈ t i, f x := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert hi]
      exact (sum_union_le_sum_add (t i) (s.biUnion t) f hf).trans (by
        simpa only [add_comm] using
          (add_le_add_left ih (∑ x ∈ t i, f x)))

/-- Exact finite sixfold reduction of the complete nonzero frequency box to
ordered triples.  Both sides contain the actual cubic modes; the factor six
is the proved cover multiplicity. -/
theorem sum_norm_gmCubicNonzeroFrequencyBox_le_ordered
    (cutoff : GMSmoothCutoff) (N H : ℕ) (W : Finset ℝ) :
    (∑ m ∈ gmCubicNonzeroFrequencyBox H,
      ‖gmCubicS3Mode cutoff N W m‖) ≤
        6 * ∑ m ∈ gmCubicOrderedFrequencyBox H,
          ‖gmCubicS3Mode cutoff N W m‖ := by
  let U := (gmCubicOrderedFrequencyBox H).biUnion gmCubicSignedPermutations
  have hsub : gmCubicNonzeroFrequencyBox H ⊆ U := by
    intro m hm
    have hm' := (mem_gmCubicNonzeroFrequencyBox.mp hm)
    obtain ⟨n, hn1, hn2, hn3, h12, h23, hnorm, hmem, hbox⟩ :=
      exists_ordered_gmCubicS3Mode cutoff N W m hm'.2.1 hm'.2.2.1 hm'.2.2.2
    have hnord : n ∈ gmCubicOrderedFrequencyBox H := by
      rw [mem_gmCubicOrderedFrequencyBox, mem_gmCubicNonzeroFrequencyBox]
      exact ⟨⟨hbox H hm'.1, hn1, hn2, hn3⟩, h12, h23⟩
    exact Finset.mem_biUnion.mpr ⟨n, hnord, hmem⟩
  calc
    (∑ m ∈ gmCubicNonzeroFrequencyBox H,
        ‖gmCubicS3Mode cutoff N W m‖) ≤
        ∑ m ∈ U, ‖gmCubicS3Mode cutoff N W m‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (by
        intro m hmU hm
        positivity)
    _ ≤ ∑ n ∈ gmCubicOrderedFrequencyBox H,
          ∑ m ∈ gmCubicSignedPermutations n,
            ‖gmCubicS3Mode cutoff N W m‖ := by
      exact sum_biUnion_le_sum_sum _ _ _ (fun _ => norm_nonneg _)
    _ ≤ ∑ n ∈ gmCubicOrderedFrequencyBox H,
          6 * ‖gmCubicS3Mode cutoff N W n‖ := by
      gcongr with n hn
      exact sum_norm_gmCubicSignedPermutations_le cutoff N W n
    _ = 6 * ∑ n ∈ gmCubicOrderedFrequencyBox H,
          ‖gmCubicS3Mode cutoff N W n‖ := by
      rw [Finset.mul_sum]

theorem gmCubicS3Mode_eq_zero_of_first_frequency_eq_zero
    (cutoff : GMSmoothCutoff) (N : ℕ) (W : Finset ℝ)
    {m : ℤ × (ℤ × ℤ)} (hm : m.1 = 0) :
    gmCubicS3Mode cutoff N W m = 0 := by
  unfold gmCubicS3Mode gmNonzeroScaledTraceMode
  simp [hm]

theorem gmCubicS3Mode_eq_zero_of_second_frequency_eq_zero
    (cutoff : GMSmoothCutoff) (N : ℕ) (W : Finset ℝ)
    {m : ℤ × (ℤ × ℤ)} (hm : m.2.1 = 0) :
    gmCubicS3Mode cutoff N W m = 0 := by
  unfold gmCubicS3Mode gmNonzeroScaledTraceMode
  simp [hm]

theorem gmCubicS3Mode_eq_zero_of_third_frequency_eq_zero
    (cutoff : GMSmoothCutoff) (N : ℕ) (W : Finset ℝ)
    {m : ℤ × (ℤ × ℤ)} (hm : m.2.2 = 0) :
    gmCubicS3Mode cutoff N W m = 0 := by
  unfold gmCubicS3Mode gmNonzeroScaledTraceMode
  simp [hm]

theorem gmCubicS3Truncated_eq_sum_nonzero
    (cutoff : GMSmoothCutoff) (N H : ℕ) (W : Finset ℝ) :
    gmCubicS3Truncated cutoff N H W =
      ∑ m ∈ gmCubicNonzeroFrequencyBox H,
        gmCubicS3Mode cutoff N W m := by
  unfold gmCubicS3Truncated
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro m hmBox hmNot
  simp only [Finset.mem_filter, hmBox, true_and, not_and_or] at hmNot
  rcases hmNot with hm1 | hm23
  · exact gmCubicS3Mode_eq_zero_of_first_frequency_eq_zero cutoff N W
      (not_ne_iff.mp hm1)
  · rcases hm23 with hm2 | hm3
    · exact gmCubicS3Mode_eq_zero_of_second_frequency_eq_zero cutoff N W
        (not_ne_iff.mp hm2)
    · exact gmCubicS3Mode_eq_zero_of_third_frequency_eq_zero cutoff N W
        (not_ne_iff.mp hm3)

theorem norm_gmCubicS3Truncated_le_ordered
    (cutoff : GMSmoothCutoff) (N H : ℕ) (W : Finset ℝ) :
    ‖gmCubicS3Truncated cutoff N H W‖ ≤
      6 * ∑ m ∈ gmCubicOrderedFrequencyBox H,
        ‖gmCubicS3Mode cutoff N W m‖ := by
  rw [gmCubicS3Truncated_eq_sum_nonzero]
  exact (norm_sum_le _ _).trans
    (sum_norm_gmCubicNonzeroFrequencyBox_le_ordered cutoff N H W)

/-- Equation (7.1) followed by the exact sixfold ordered-frequency
reduction.  This theorem starts from the literal `gmCubicS3`, retains the
complete finite source box, and charges the complete omitted series to the
proved `T⁻¹⁰⁰` error. -/
theorem norm_gmCubicS3_le_ordered_source_box
    (cutoff : GMSmoothCutoff) (η : ℝ) (hη : 0 < η) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ) (W : Finset ℝ) {T : ℝ},
      0 < N → 1 ≤ T → IsSeparated 1 W → InBaseInterval T W →
      ‖gmCubicS3 cutoff N W‖ ≤
        6 * ∑ m ∈ gmCubicOrderedFrequencyBox
            (gmCubicFrequencyRadius η T N),
          ‖gmCubicS3Mode cutoff N W m‖ + K / T ^ 100 := by
  obtain ⟨K, hK, htrunc⟩ :=
    gmCubicS3_source_truncation_pow_100 cutoff η hη
  refine ⟨K, hK, ?_⟩
  intro N W T hN hT hSep hBase
  let H := gmCubicFrequencyRadius η T N
  let S := gmCubicS3 cutoff N W
  let F := gmCubicS3Truncated cutoff N H W
  have hdiff : ‖S - F‖ ≤ K / T ^ 100 :=
    htrunc N W hN hT hSep hBase
  have hF := norm_gmCubicS3Truncated_le_ordered cutoff N H W
  calc
    ‖S‖ = ‖F + (S - F)‖ := by ring_nf
    _ ≤ ‖F‖ + ‖S - F‖ := norm_add_le _ _
    _ ≤ 6 * ∑ m ∈ gmCubicOrderedFrequencyBox H,
          ‖gmCubicS3Mode cutoff N W m‖ + K / T ^ 100 :=
      add_le_add hF hdiff

/-! ## Balanced ordered frequencies -/

/-- The balanced ordered part of the source-frequency box.  This is the
finite set retained after the negligible alternative in Proposition 7.1:
the second and third absolute frequencies are comparable with the explicit
source constant `5`. -/
noncomputable def gmCubicBalancedOrderedFrequencyBox (H : ℕ) :
    Finset (ℤ × (ℤ × ℤ)) :=
  (gmCubicOrderedFrequencyBox H).filter fun m =>
    |(m.2.2 : ℝ)| ≤ 5 * |(m.2.1 : ℝ)|

/-- The complementary ordered frequencies, which Proposition 7.1 makes
negligible one mode at a time. -/
noncomputable def gmCubicUnbalancedOrderedFrequencyBox (H : ℕ) :
    Finset (ℤ × (ℤ × ℤ)) :=
  (gmCubicOrderedFrequencyBox H).filter fun m =>
    5 * |(m.2.1 : ℝ)| < |(m.2.2 : ℝ)|

@[simp]
theorem mem_gmCubicBalancedOrderedFrequencyBox
    {H : ℕ} {m : ℤ × (ℤ × ℤ)} :
    m ∈ gmCubicBalancedOrderedFrequencyBox H ↔
      m ∈ gmCubicOrderedFrequencyBox H ∧
        |(m.2.2 : ℝ)| ≤ 5 * |(m.2.1 : ℝ)| := by
  simp [gmCubicBalancedOrderedFrequencyBox]

@[simp]
theorem mem_gmCubicUnbalancedOrderedFrequencyBox
    {H : ℕ} {m : ℤ × (ℤ × ℤ)} :
    m ∈ gmCubicUnbalancedOrderedFrequencyBox H ↔
      m ∈ gmCubicOrderedFrequencyBox H ∧
        5 * |(m.2.1 : ℝ)| < |(m.2.2 : ℝ)| := by
  simp [gmCubicUnbalancedOrderedFrequencyBox]

/-- Exact finite balanced/unbalanced partition of the ordered frequency
box.  No asymptotic estimate has entered at this point. -/
theorem sum_norm_gmCubicOrderedFrequencyBox_eq_balanced_add_unbalanced
    (cutoff : GMSmoothCutoff) (N H : ℕ) (W : Finset ℝ) :
    (∑ m ∈ gmCubicOrderedFrequencyBox H,
        ‖gmCubicS3Mode cutoff N W m‖) =
      (∑ m ∈ gmCubicBalancedOrderedFrequencyBox H,
        ‖gmCubicS3Mode cutoff N W m‖) +
      ∑ m ∈ gmCubicUnbalancedOrderedFrequencyBox H,
        ‖gmCubicS3Mode cutoff N W m‖ := by
  rw [← Finset.sum_filter_add_sum_filter_not
    (s := gmCubicOrderedFrequencyBox H)
    (p := fun m : ℤ × (ℤ × ℤ) =>
      |(m.2.2 : ℝ)| ≤ 5 * |(m.2.1 : ℝ)|)
    (f := fun m => ‖gmCubicS3Mode cutoff N W m‖)]
  congr 2
  ext m
  simp

/-- Summed negligible alternative in Proposition 7.1.  The finite
cardinality factor is retained explicitly here; the next scale lemma absorbs
it into the `T⁻¹⁰⁰` budget at the source truncation radius. -/
theorem sum_norm_gmCubicUnbalancedOrderedFrequencyBox_le
    (cutoff : GMSmoothCutoff) (η : ℝ) (hηpos : 0 < η)
    (hηupper : η ≤ 2 / 3) :
    ∃ C : ℝ, 0 < C ∧ ∀ {T : ℝ} {N H : ℕ} {W : Finset ℝ},
      1 ≤ T → 0 < N → (N : ℝ) ≤ T →
      T ^ (2 / 3 : ℝ) ≤ (N : ℝ) →
      IsSeparated 1 W → InBaseInterval T W →
      (∑ m ∈ gmCubicUnbalancedOrderedFrequencyBox H,
        ‖gmCubicS3Mode cutoff N W m‖) ≤
        ((gmCubicUnbalancedOrderedFrequencyBox H).card : ℝ) *
          (C / T ^ 200) := by
  obtain ⟨C, hC, hmode⟩ :=
    gmCubicS3Mode_unbalanced_prop7_1 cutoff η hηpos hηupper
  refine ⟨C, hC, ?_⟩
  intro T N H W hT hN hNT hNlower hSep hBase
  calc
    (∑ m ∈ gmCubicUnbalancedOrderedFrequencyBox H,
        ‖gmCubicS3Mode cutoff N W m‖) ≤
        ∑ _m ∈ gmCubicUnbalancedOrderedFrequencyBox H,
          C / T ^ 200 := by
      gcongr with m hm
      have hm' := mem_gmCubicUnbalancedOrderedFrequencyBox.mp hm
      have hord := mem_gmCubicOrderedFrequencyBox.mp hm'.1
      have hnz := mem_gmCubicNonzeroFrequencyBox.mp hord.1
      exact hmode hT hN hNT hNlower hSep hBase
        hnz.2.1 hnz.2.2.1 hnz.2.2.2 hord.2.1 hm'.2
    _ = ((gmCubicUnbalancedOrderedFrequencyBox H).card : ℝ) *
          (C / T ^ 200) := by simp

/-- Exact cardinality of the symmetric three-frequency box. -/
theorem card_gmCubicFrequencyBox (H : ℕ) :
    (gmCubicFrequencyBox H).card = (2 * H + 1) ^ 3 := by
  have hcard : (Finset.Icc (-(H : ℤ)) (H : ℤ)).card = 2 * H + 1 := by
    rw [Int.card_Icc]
    rw [show (H : ℤ) + 1 - -(H : ℤ) = ((2 * H + 1 : ℕ) : ℤ) by
      push_cast
      ring]
    exact Int.toNat_natCast _
  simp [gmCubicFrequencyBox, hcard, pow_succ]
  ring

theorem card_gmCubicUnbalancedOrderedFrequencyBox_le (H : ℕ) :
    (gmCubicUnbalancedOrderedFrequencyBox H).card ≤ (2 * H + 1) ^ 3 := by
  calc
    (gmCubicUnbalancedOrderedFrequencyBox H).card ≤
        (gmCubicOrderedFrequencyBox H).card := Finset.card_filter_le _ _
    _ ≤ (gmCubicNonzeroFrequencyBox H).card := Finset.card_filter_le _ _
    _ ≤ (gmCubicFrequencyBox H).card := Finset.card_filter_le _ _
    _ = (2 * H + 1) ^ 3 := card_gmCubicFrequencyBox H

theorem gmCubicFrequencyRadius_cast_lt_rpow_add_one
    {η T : ℝ} {N : ℕ} (hT : 0 < T) (hN : 0 < N) :
    (gmCubicFrequencyRadius η T N : ℝ) < T ^ (1 + η) + 1 := by
  have hNOne : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hscale : 0 ≤ T ^ (1 + η) := (Real.rpow_pos_of_pos hT _).le
  have hratio : T ^ (1 + η) / (N : ℝ) ≤ T ^ (1 + η) :=
    div_le_self hscale hNOne
  have hceil := Nat.ceil_lt_add_one
    (show 0 ≤ T ^ (1 + η) / (N : ℝ) by positivity)
  exact hceil.trans_le (by linarith)

theorem two_frequencyRadius_add_one_le_five_rpow
    {η T : ℝ} {N : ℕ} (hT : 1 ≤ T) (hη : 0 ≤ η) (hN : 0 < N) :
    ((2 * gmCubicFrequencyRadius η T N + 1 : ℕ) : ℝ) ≤
      5 * T ^ (1 + η) := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hrad := gmCubicFrequencyRadius_cast_lt_rpow_add_one
    (η := η) hTpos hN
  have hscaleOne : (1 : ℝ) ≤ T ^ (1 + η) := by
    apply Real.one_le_rpow hT
    linarith
  have hcast : ((2 * gmCubicFrequencyRadius η T N + 1 : ℕ) : ℝ) =
      2 * (gmCubicFrequencyRadius η T N : ℝ) + 1 := by norm_num
  rw [hcast]
  calc
    2 * (gmCubicFrequencyRadius η T N : ℝ) + 1 ≤
        2 * (T ^ (1 + η) + 1) + 1 := by linarith
    _ ≤ 5 * T ^ (1 + η) := by linarith

theorem card_gmCubicUnbalanced_sourceRadius_le
    {η T : ℝ} {N : ℕ} (hT : 1 ≤ T) (hηpos : 0 < η)
    (hηupper : η ≤ 2 / 3) (hN : 0 < N) :
    ((gmCubicUnbalancedOrderedFrequencyBox
      (gmCubicFrequencyRadius η T N)).card : ℝ) ≤ 125 * T ^ 5 := by
  let H := gmCubicFrequencyRadius η T N
  have hcardNat := card_gmCubicUnbalancedOrderedFrequencyBox_le H
  have hcard :
      ((gmCubicUnbalancedOrderedFrequencyBox H).card : ℝ) ≤
        (((2 * H + 1) ^ 3 : ℕ) : ℝ) := by exact_mod_cast hcardNat
  have hradius := two_frequencyRadius_add_one_le_five_rpow
    (T := T) (N := N) hT hηpos.le hN
  have hpow : (((2 * H + 1) ^ 3 : ℕ) : ℝ) ≤
      (5 * T ^ (1 + η)) ^ 3 := by
    norm_num only [Nat.cast_pow]
    exact pow_le_pow_left₀ (by positivity) hradius 3
  have hexp : 3 * (1 + η) ≤ 5 := by linarith
  have hscale : (T ^ (1 + η)) ^ 3 ≤ T ^ (5 : ℕ) := by
    calc
      (T ^ (1 + η)) ^ 3 = T ^ ((1 + η) * (3 : ℝ)) := by
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul (by positivity : 0 ≤ T)]
        norm_num
      _ ≤ T ^ (5 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hT (by nlinarith)
      _ = T ^ (5 : ℕ) := by norm_num [Real.rpow_natCast]
  calc
    ((gmCubicUnbalancedOrderedFrequencyBox H).card : ℝ) ≤
        (((2 * H + 1) ^ 3 : ℕ) : ℝ) := hcard
    _ ≤ (5 * T ^ (1 + η)) ^ 3 := hpow
    _ = 125 * (T ^ (1 + η)) ^ 3 := by ring
    _ ≤ 125 * T ^ 5 := by gcongr

theorem gmCubicUnbalanced_card_error_absorbed
    {η T C : ℝ} {N : ℕ} (hT : 1 ≤ T) (hηpos : 0 < η)
    (hηupper : η ≤ 2 / 3) (hN : 0 < N) (hC : 0 ≤ C) :
    ((gmCubicUnbalancedOrderedFrequencyBox
        (gmCubicFrequencyRadius η T N)).card : ℝ) *
          (C / T ^ 200) ≤ 125 * C / T ^ 100 := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hcard := card_gmCubicUnbalanced_sourceRadius_le
    (T := T) (N := N) hT hηpos hηupper hN
  have hnum :
      ((gmCubicUnbalancedOrderedFrequencyBox
        (gmCubicFrequencyRadius η T N)).card : ℝ) * C ≤
          (125 * T ^ 5) * C := mul_le_mul_of_nonneg_right hcard hC
  calc
    ((gmCubicUnbalancedOrderedFrequencyBox
        (gmCubicFrequencyRadius η T N)).card : ℝ) *
          (C / T ^ 200) =
        (((gmCubicUnbalancedOrderedFrequencyBox
          (gmCubicFrequencyRadius η T N)).card : ℝ) * C) /
            T ^ 200 := by ring
    _ ≤ ((125 * T ^ 5) * C) / T ^ 200 :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ 125 * C / T ^ 100 := by
      rw [div_le_div_iff₀ (pow_pos hTpos 200) (pow_pos hTpos 100)]
      calc
        ((125 * T ^ 5) * C) * T ^ 100 =
            125 * C * T ^ 105 := by
          rw [show T ^ 105 = T ^ 5 * T ^ 100 by
            rw [← pow_add]]
          ring
        _ ≤ 125 * C * T ^ 200 := by
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ hT (by omega : 105 ≤ 200)) (by positivity)
        _ = (125 * C) * T ^ 200 := by ring

/-- The complete ordered source sum after Proposition 7.1: only balanced
frequencies remain, and all unbalanced modes have been absorbed into one
uniform `T⁻¹⁰⁰` error. -/
theorem sum_norm_gmCubicOrdered_sourceRadius_le_balanced
    (cutoff : GMSmoothCutoff) (η : ℝ) (hηpos : 0 < η)
    (hηupper : η ≤ 2 / 3) :
    ∃ K : ℝ, 0 < K ∧ ∀ {T : ℝ} {N : ℕ} {W : Finset ℝ},
      1 ≤ T → 0 < N → (N : ℝ) ≤ T →
      T ^ (2 / 3 : ℝ) ≤ (N : ℝ) →
      IsSeparated 1 W → InBaseInterval T W →
      (∑ m ∈ gmCubicOrderedFrequencyBox
          (gmCubicFrequencyRadius η T N),
        ‖gmCubicS3Mode cutoff N W m‖) ≤
        (∑ m ∈ gmCubicBalancedOrderedFrequencyBox
          (gmCubicFrequencyRadius η T N),
          ‖gmCubicS3Mode cutoff N W m‖) + K / T ^ 100 := by
  obtain ⟨C, hC, hunbalanced⟩ :=
    sum_norm_gmCubicUnbalancedOrderedFrequencyBox_le
      cutoff η hηpos hηupper
  refine ⟨125 * C, by positivity, ?_⟩
  intro T N W hT hN hNT hNlower hSep hBase
  let H := gmCubicFrequencyRadius η T N
  rw [sum_norm_gmCubicOrderedFrequencyBox_eq_balanced_add_unbalanced]
  gcongr
  exact (hunbalanced hT hN hNT hNlower hSep hBase).trans
    (gmCubicUnbalanced_card_error_absorbed hT hηpos hηupper hN hC.le)

/-- Equations (7.1) and Proposition 7.1 assembled at the actual cubic
trace: the full `S₃` is bounded by the balanced ordered source box plus a
single uniform `T⁻¹⁰⁰` remainder. -/
theorem norm_gmCubicS3_le_balanced_source_box
    (cutoff : GMSmoothCutoff) (η : ℝ) (hηpos : 0 < η)
    (hηupper : η ≤ 2 / 3) :
    ∃ K : ℝ, 0 < K ∧ ∀ {T : ℝ} {N : ℕ} {W : Finset ℝ},
      1 ≤ T → 0 < N → (N : ℝ) ≤ T →
      T ^ (2 / 3 : ℝ) ≤ (N : ℝ) →
      IsSeparated 1 W → InBaseInterval T W →
      ‖gmCubicS3 cutoff N W‖ ≤
        6 * (∑ m ∈ gmCubicBalancedOrderedFrequencyBox
          (gmCubicFrequencyRadius η T N),
          ‖gmCubicS3Mode cutoff N W m‖) + K / T ^ 100 := by
  obtain ⟨K₁, hK₁, hsource⟩ :=
    norm_gmCubicS3_le_ordered_source_box cutoff η hηpos
  obtain ⟨K₂, hK₂, hbalanced⟩ :=
    sum_norm_gmCubicOrdered_sourceRadius_le_balanced
      cutoff η hηpos hηupper
  refine ⟨K₁ + 6 * K₂, by positivity, ?_⟩
  intro T N W hT hN hNT hNlower hSep hBase
  have hs := hsource N W hN hT hSep hBase
  have hb := hbalanced hT hN hNT hNlower hSep hBase
  calc
    ‖gmCubicS3 cutoff N W‖ ≤
        6 * (∑ m ∈ gmCubicOrderedFrequencyBox
          (gmCubicFrequencyRadius η T N),
          ‖gmCubicS3Mode cutoff N W m‖) + K₁ / T ^ 100 := hs
    _ ≤ 6 * ((∑ m ∈ gmCubicBalancedOrderedFrequencyBox
          (gmCubicFrequencyRadius η T N),
          ‖gmCubicS3Mode cutoff N W m‖) + K₂ / T ^ 100) +
          K₁ / T ^ 100 := by gcongr
    _ = 6 * (∑ m ∈ gmCubicBalancedOrderedFrequencyBox
          (gmCubicFrequencyRadius η T N),
          ‖gmCubicS3Mode cutoff N W m‖) +
          (K₁ + 6 * K₂) / T ^ 100 := by ring

/-! ## Dyadic selection for Proposition 7.2 -/

/-- A dyadic block of the balanced ordered frequency box.  The first
frequency has scale `2^r`; the comparable second and third frequencies have
scale `2^s`. -/
noncomputable def gmCubicDyadicFrequencyBlock (H r s : ℕ) :
    Finset (ℤ × (ℤ × ℤ)) :=
  (gmCubicBalancedOrderedFrequencyBox H).filter fun m =>
    2 ^ r ≤ m.1.natAbs ∧ m.1.natAbs < 2 ^ (r + 1) ∧
    2 ^ s ≤ m.2.1.natAbs ∧ m.2.1.natAbs < 2 ^ (s + 1)

@[simp]
theorem mem_gmCubicDyadicFrequencyBlock
    {H r s : ℕ} {m : ℤ × (ℤ × ℤ)} :
    m ∈ gmCubicDyadicFrequencyBlock H r s ↔
      m ∈ gmCubicBalancedOrderedFrequencyBox H ∧
      2 ^ r ≤ m.1.natAbs ∧ m.1.natAbs < 2 ^ (r + 1) ∧
      2 ^ s ≤ m.2.1.natAbs ∧ m.2.1.natAbs < 2 ^ (s + 1) := by
  simp [gmCubicDyadicFrequencyBlock]

theorem natAbs_frequencies_le_of_mem_gmCubicFrequencyBox
    {H : ℕ} {m : ℤ × (ℤ × ℤ)} (hm : m ∈ gmCubicFrequencyBox H) :
    m.1.natAbs ≤ H ∧ m.2.1.natAbs ≤ H ∧ m.2.2.natAbs ≤ H := by
  rw [mem_gmCubicFrequencyBox] at hm
  have h1 : |m.1| ≤ (H : ℤ) := abs_le.mpr ⟨hm.1, hm.2.1⟩
  have h2 : |m.2.1| ≤ (H : ℤ) := abs_le.mpr ⟨hm.2.2.1, hm.2.2.2.1⟩
  have h3 : |m.2.2| ≤ (H : ℤ) := abs_le.mpr ⟨hm.2.2.2.2.1, hm.2.2.2.2.2⟩
  constructor
  · rw [← Int.natCast_natAbs] at h1
    exact_mod_cast h1
  constructor
  · rw [← Int.natCast_natAbs] at h2
    exact_mod_cast h2
  · rw [← Int.natCast_natAbs] at h3
    exact_mod_cast h3

/-- Every balanced nonzero frequency triple belongs to the dyadic block
indexed by the binary logarithms of its first two absolute frequencies. -/
theorem exists_gmCubicDyadicFrequencyBlock
    {H : ℕ} {m : ℤ × (ℤ × ℤ)}
    (hm : m ∈ gmCubicBalancedOrderedFrequencyBox H) :
    ∃ r ∈ Finset.range (Nat.log 2 H + 1),
      ∃ s ∈ Finset.range (Nat.log 2 H + 1),
        m ∈ gmCubicDyadicFrequencyBlock H r s := by
  have hmord := mem_gmCubicBalancedOrderedFrequencyBox.mp hm
  have hmnonzero := mem_gmCubicOrderedFrequencyBox.mp hmord.1
  have hmbox := mem_gmCubicNonzeroFrequencyBox.mp hmnonzero.1
  have hle := natAbs_frequencies_le_of_mem_gmCubicFrequencyBox hmbox.1
  let r := Nat.log 2 m.1.natAbs
  let s := Nat.log 2 m.2.1.natAbs
  have hm1abs : m.1.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hmbox.2.1
  have hm2abs : m.2.1.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hmbox.2.2.1
  have hr : r ∈ Finset.range (Nat.log 2 H + 1) := by
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (Nat.log_mono_right hle.1)
  have hs : s ∈ Finset.range (Nat.log 2 H + 1) := by
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (Nat.log_mono_right hle.2.1)
  refine ⟨r, hr, s, hs, ?_⟩
  rw [mem_gmCubicDyadicFrequencyBlock]
  refine ⟨hm, Nat.pow_log_le_self 2 hm1abs, ?_,
    Nat.pow_log_le_self 2 hm2abs, ?_⟩
  · simpa only [r, Nat.succ_eq_add_one] using
      Nat.lt_pow_succ_log_self (by omega : 1 < 2) m.1.natAbs
  · simpa only [s, Nat.succ_eq_add_one] using
      Nat.lt_pow_succ_log_self (by omega : 1 < 2) m.2.1.natAbs

/-- Ordered pairs of dyadic exponents needed for the two source scales in
Proposition 7.2. -/
def gmCubicDyadicIndexPairs (H : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (Nat.log 2 H + 1)) ×ˢ
    (Finset.range (Nat.log 2 H + 1))).filter fun p => p.1 ≤ p.2

@[simp]
theorem mem_gmCubicDyadicIndexPairs {H : ℕ} {p : ℕ × ℕ} :
    p ∈ gmCubicDyadicIndexPairs H ↔
      p.1 < Nat.log 2 H + 1 ∧ p.2 < Nat.log 2 H + 1 ∧ p.1 ≤ p.2 := by
  simp [gmCubicDyadicIndexPairs, and_assoc]

theorem gmCubicDyadicIndexPairs_nonempty (H : ℕ) :
    (gmCubicDyadicIndexPairs H).Nonempty := by
  refine ⟨(0, 0), ?_⟩
  simp

theorem gmCubicDyadicIndexPairs_card_le (H : ℕ) :
    (gmCubicDyadicIndexPairs H).card ≤ (Nat.log 2 H + 1) ^ 2 := by
  calc
    (gmCubicDyadicIndexPairs H).card ≤
        ((Finset.range (Nat.log 2 H + 1)) ×ˢ
          (Finset.range (Nat.log 2 H + 1))).card := Finset.card_filter_le _ _
    _ = (Nat.log 2 H + 1) ^ 2 := by simp [pow_two]

theorem exists_gmCubicOrderedDyadicFrequencyBlock
    {H : ℕ} {m : ℤ × (ℤ × ℤ)}
    (hm : m ∈ gmCubicBalancedOrderedFrequencyBox H) :
    ∃ p ∈ gmCubicDyadicIndexPairs H,
      m ∈ gmCubicDyadicFrequencyBlock H p.1 p.2 := by
  obtain ⟨r, hr, s, hs, hblock⟩ := exists_gmCubicDyadicFrequencyBlock hm
  have hmord := mem_gmCubicBalancedOrderedFrequencyBox.mp hm
  have hord := mem_gmCubicOrderedFrequencyBox.mp hmord.1
  have habs : m.1.natAbs ≤ m.2.1.natAbs := by
    rw [← Nat.cast_le (α := ℝ), Nat.cast_natAbs, Nat.cast_natAbs,
      Int.cast_abs, Int.cast_abs]
    exact hord.2.1
  have hrs : r ≤ s := by
    by_contra hrs
    have hsr : s + 1 ≤ r := by omega
    have hpowers : 2 ^ (s + 1) ≤ 2 ^ r :=
      Nat.pow_le_pow_right (by omega) hsr
    have hmem := mem_gmCubicDyadicFrequencyBlock.mp hblock
    omega
  refine ⟨(r, s), ?_, hblock⟩
  rw [mem_gmCubicDyadicIndexPairs]
  exact ⟨Finset.mem_range.mp hr, Finset.mem_range.mp hs, hrs⟩

/-- Exact dyadic pigeonhole for the balanced ordered source sum.  It
produces the two dyadic scales used in (7.5)--(7.6), with `r ≤ s` derived
from the ordered frequencies rather than assumed. -/
theorem exists_dominant_gmCubicDyadicFrequencyBlock
    (cutoff : GMSmoothCutoff) (N H : ℕ) (W : Finset ℝ) :
    ∃ p ∈ gmCubicDyadicIndexPairs H,
      (∑ m ∈ gmCubicBalancedOrderedFrequencyBox H,
        ‖gmCubicS3Mode cutoff N W m‖) ≤
      ((Nat.log 2 H + 1 : ℕ) : ℝ) ^ 2 *
        ∑ m ∈ gmCubicDyadicFrequencyBlock H p.1 p.2,
          ‖gmCubicS3Mode cutoff N W m‖ := by
  let P := gmCubicDyadicIndexPairs H
  let B : (ℕ × ℕ) → Finset (ℤ × (ℤ × ℤ)) := fun p =>
    gmCubicDyadicFrequencyBlock H p.1 p.2
  let F : (ℕ × ℕ) → ℝ := fun p =>
    ∑ m ∈ B p, ‖gmCubicS3Mode cutoff N W m‖
  have hcover : gmCubicBalancedOrderedFrequencyBox H ⊆ P.biUnion B := by
    intro m hm
    obtain ⟨p, hp, hmp⟩ := exists_gmCubicOrderedDyadicFrequencyBlock hm
    exact Finset.mem_biUnion.mpr ⟨p, hp, hmp⟩
  have hsumCover :
      (∑ m ∈ gmCubicBalancedOrderedFrequencyBox H,
          ‖gmCubicS3Mode cutoff N W m‖) ≤
        ∑ p ∈ P, F p := by
    calc
      (∑ m ∈ gmCubicBalancedOrderedFrequencyBox H,
          ‖gmCubicS3Mode cutoff N W m‖) ≤
          ∑ m ∈ P.biUnion B, ‖gmCubicS3Mode cutoff N W m‖ :=
        Finset.sum_le_sum_of_subset_of_nonneg hcover (by
          intro m hmU hm
          positivity)
      _ ≤ ∑ p ∈ P, ∑ m ∈ B p,
          ‖gmCubicS3Mode cutoff N W m‖ :=
        sum_biUnion_le_sum_sum P B _ (fun _ => norm_nonneg _)
      _ = ∑ p ∈ P, F p := rfl
  obtain ⟨p, hp, hpmax⟩ :=
    Finset.exists_max_image P F (gmCubicDyadicIndexPairs_nonempty H)
  refine ⟨p, hp, hsumCover.trans ?_⟩
  have hcardNat := gmCubicDyadicIndexPairs_card_le H
  have hcard : (P.card : ℝ) ≤ ((Nat.log 2 H + 1 : ℕ) : ℝ) ^ 2 := by
    exact_mod_cast hcardNat
  calc
    (∑ q ∈ P, F q) ≤ ∑ _q ∈ P, F p := by
      gcongr with q hq
      exact hpmax q hq
    _ = (P.card : ℝ) * F p := by simp
    _ ≤ ((Nat.log 2 H + 1 : ℕ) : ℝ) ^ 2 * F p := by
      gcongr

/-- The full cubic trace reduced to one ordered balanced dyadic block.  This
is the finite dyadic-selection part of Guth--Maynard Proposition 7.2, still
written with the exact frequency modes before the smoothing estimate. -/
theorem norm_gmCubicS3_le_one_dyadic_frequency_block
    (cutoff : GMSmoothCutoff) (η : ℝ) (hηpos : 0 < η)
    (hηupper : η ≤ 2 / 3) :
    ∃ K : ℝ, 0 < K ∧ ∀ {T : ℝ} {N : ℕ} {W : Finset ℝ},
      1 ≤ T → 0 < N → (N : ℝ) ≤ T →
      T ^ (2 / 3 : ℝ) ≤ (N : ℝ) →
      IsSeparated 1 W → InBaseInterval T W →
      ∃ p ∈ gmCubicDyadicIndexPairs (gmCubicFrequencyRadius η T N),
        ‖gmCubicS3 cutoff N W‖ ≤
          6 * ((Nat.log 2 (gmCubicFrequencyRadius η T N) + 1 : ℕ) : ℝ) ^ 2 *
            (∑ m ∈ gmCubicDyadicFrequencyBlock
              (gmCubicFrequencyRadius η T N) p.1 p.2,
              ‖gmCubicS3Mode cutoff N W m‖) + K / T ^ 100 := by
  obtain ⟨K, hK, hbalanced⟩ :=
    norm_gmCubicS3_le_balanced_source_box cutoff η hηpos hηupper
  refine ⟨K, hK, ?_⟩
  intro T N W hT hN hNT hNlower hSep hBase
  obtain ⟨p, hp, hpdom⟩ := exists_dominant_gmCubicDyadicFrequencyBlock
    cutoff N (gmCubicFrequencyRadius η T N) W
  refine ⟨p, hp, ?_⟩
  calc
    ‖gmCubicS3 cutoff N W‖ ≤
        6 * (∑ m ∈ gmCubicBalancedOrderedFrequencyBox
          (gmCubicFrequencyRadius η T N),
          ‖gmCubicS3Mode cutoff N W m‖) + K / T ^ 100 :=
      hbalanced hT hN hNT hNlower hSep hBase
    _ ≤ 6 * (((Nat.log 2 (gmCubicFrequencyRadius η T N) + 1 : ℕ) : ℝ) ^ 2 *
          (∑ m ∈ gmCubicDyadicFrequencyBlock
            (gmCubicFrequencyRadius η T N) p.1 p.2,
            ‖gmCubicS3Mode cutoff N W m‖)) + K / T ^ 100 := by
      exact add_le_add (mul_le_mul_of_nonneg_left hpdom
        (by norm_num : (0 : ℝ) ≤ 6)) le_rfl
    _ = 6 * ((Nat.log 2 (gmCubicFrequencyRadius η T N) + 1 : ℕ) : ℝ) ^ 2 *
          (∑ m ∈ gmCubicDyadicFrequencyBlock
            (gmCubicFrequencyRadius η T N) p.1 p.2,
            ‖gmCubicS3Mode cutoff N W m‖) + K / T ^ 100 := by ring

/-! ## The source smoother from equation (7.5) -/

/-- A fixed compactly supported nonnegative bump which is one on `[-1,1]`
and supported in `(-2,2)`.  It is obtained from the audited unit DFI bump by
one fixed dilation, so all derivative constants are scale-independent. -/
noncomputable def gmCubicLocalBump (x : ℝ) : ℝ :=
  dfiUnitRedundantBump (x / 2)

theorem gmCubicLocalBump_nonneg (x : ℝ) : 0 ≤ gmCubicLocalBump x :=
  dfiUnitRedundantBump.nonneg

theorem gmCubicLocalBump_one {x : ℝ} (hx : |x| ≤ 1) :
    gmCubicLocalBump x = 1 := by
  unfold gmCubicLocalBump
  apply dfiUnitRedundantBump.one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq]
  rw [sub_zero, show dfiUnitRedundantBump.rIn = (1 / 2 : ℝ) by rfl]
  rw [abs_div]
  norm_num
  linarith

/-- A fixed positive-axis bump which is one throughout `[1/4,4]` and is
compactly supported in `(1/8,33/8)`.  This uniformly majorizes every ratio
range produced from `[1/2,2]²` in Proposition 7.2. -/
noncomputable def gmCubicRatioBump : ContDiffBump (17 / 8 : ℝ) :=
  ⟨15 / 8, 2, by norm_num, by norm_num⟩

theorem gmCubicRatioBump_one {x : ℝ}
    (hx : x ∈ Set.Icc (1 / 4 : ℝ) 4) : gmCubicRatioBump x = 1 := by
  apply gmCubicRatioBump.one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq]
  change |x - 17 / 8| ≤ 15 / 8
  rw [abs_le]
  constructor <;> linarith [hx.1, hx.2]

theorem gmCubicRatioBump_nonneg (x : ℝ) : 0 ≤ gmCubicRatioBump x :=
  gmCubicRatioBump.nonneg

/-- The physical convolution scale in (7.5), with the fixed factor `2`
needed after the source change of variables `v₂ ↦ v₂ / v₁` on
`v₁ ∈ [1/2,2]`, and the explicit `T^η` enlargement used for the
quantitative cancellation slab. -/
noncomputable def gmCubicSmoothingScale
    (η T : ℝ) (N M : ℕ) : ℝ :=
  (N : ℝ) * (M : ℝ) / (2 * T ^ η)

theorem gmCubicSmoothingScale_pos
    {η T : ℝ} {N M : ℕ} (hT : 0 < T) (hN : 0 < N) (hM : 0 < M) :
    0 < gmCubicSmoothingScale η T N M := by
  unfold gmCubicSmoothingScale
  positivity

theorem continuousOn_gmR_compl_zero (W : Finset ℝ) :
    ContinuousOn (gmR W) ({0} : Set ℝ)ᶜ := by
  intro v hv
  exact (continuousAt_gmR W (by simpa using hv)).continuousWithinAt

theorem measurable_gmR (W : Finset ℝ) : Measurable (gmR W) :=
  measurable_of_continuousOn_compl_singleton 0
    (continuousOn_gmR_compl_zero W)

theorem norm_gmR_le_card_all (W : Finset ℝ) (v : ℝ) :
    ‖gmR W v‖ ≤ W.card := by
  by_cases hv : v = 0
  · subst v
    rw [gmR]
    calc
      ‖∑ t ∈ W, (((|0| : ℝ) : ℂ) ^ ((t : ℂ) * I))‖ ≤
          ∑ t ∈ W, ‖(((|0| : ℝ) : ℂ) ^ ((t : ℂ) * I))‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _t ∈ W, (1 : ℝ) := by
        gcongr with t ht
        by_cases ht0 : t = 0
        · subst t
          simp
        · have hexp : ((t : ℂ) * I) ≠ 0 := mul_ne_zero (by exact_mod_cast ht0) I_ne_zero
          simp [Complex.zero_cpow hexp]
      _ = W.card := by simp
  · exact norm_gmR_le_card W v hv

theorem gmCubicLocalBump_le_one (x : ℝ) : gmCubicLocalBump x ≤ 1 :=
  dfiUnitRedundantBump.le_one

theorem gmCubicRatioBump_le_one (x : ℝ) : gmCubicRatioBump x ≤ 1 :=
  gmCubicRatioBump.le_one

theorem gmCubicRatioBump_eq_zero_of_not_mem_Icc
    {x : ℝ} (hx : x ∉ Set.Icc (1 / 8 : ℝ) (33 / 8)) :
    gmCubicRatioBump x = 0 := by
  by_contra hne
  have hsupp : x ∈ Function.support gmCubicRatioBump := hne
  rw [gmCubicRatioBump.support_eq] at hsupp
  rw [Metric.mem_ball, Real.dist_eq] at hsupp
  change |x - 17 / 8| < 2 at hsupp
  have hxIcc : x ∈ Set.Icc (1 / 8 : ℝ) (33 / 8) := by
    rw [Set.mem_Icc]
    rcases abs_lt.mp hsupp with ⟨hleft, hright⟩
    constructor <;> linarith
  exact hx hxIcc

/-- The real nonnegative integrand in the square defining the source
smoother. -/
noncomputable def gmCubicSmoothedRIntegrand
    (η T : ℝ) (N M : ℕ) (W : Finset ℝ) (v u : ℝ) : ℝ :=
  gmCubicSmoothingScale η T N M *
    gmCubicLocalBump (gmCubicSmoothingScale η T N M * (v - u)) *
    gmCubicRatioBump u * ‖gmR W u‖ ^ 2

theorem measurable_gmCubicSmoothedRIntegrand
    (η T : ℝ) (N M : ℕ) (W : Finset ℝ) (v : ℝ) :
    Measurable (gmCubicSmoothedRIntegrand η T N M W v) := by
  have hlinear : Measurable (fun u : ℝ =>
      gmCubicSmoothingScale η T N M * (v - u)) :=
    measurable_const.mul (measurable_const.sub measurable_id)
  have hlocalContinuous : Continuous gmCubicLocalBump := by
    unfold gmCubicLocalBump
    exact dfiUnitRedundantBump.continuous.comp (continuous_id.div_const 2)
  have hlocal : Measurable (fun u : ℝ =>
      gmCubicLocalBump (gmCubicSmoothingScale η T N M * (v - u))) :=
    hlocalContinuous.measurable.comp hlinear
  have hratio : Measurable (fun u : ℝ => gmCubicRatioBump u) :=
    gmCubicRatioBump.continuous.measurable
  have hR : Measurable (fun u : ℝ => ‖gmR W u‖ ^ 2) :=
    (measurable_gmR W).norm.pow_const 2
  exact ((measurable_const.mul hlocal).mul hratio).mul hR

theorem gmCubicSmoothedRIntegrand_nonneg
    {η T : ℝ} {N M : ℕ} (W : Finset ℝ) (v u : ℝ)
    (hscale : 0 ≤ gmCubicSmoothingScale η T N M) :
    0 ≤ gmCubicSmoothedRIntegrand η T N M W v u := by
  unfold gmCubicSmoothedRIntegrand
  exact mul_nonneg (mul_nonneg (mul_nonneg hscale
    (gmCubicLocalBump_nonneg _)) (gmCubicRatioBump_nonneg _)) (sq_nonneg _)

theorem gmCubicSmoothedRIntegrand_le
    {η T : ℝ} {N M : ℕ} (W : Finset ℝ) (v u : ℝ)
    (hscale : 0 ≤ gmCubicSmoothingScale η T N M) :
    gmCubicSmoothedRIntegrand η T N M W v u ≤
      gmCubicSmoothingScale η T N M * (W.card : ℝ) ^ 2 := by
  unfold gmCubicSmoothedRIntegrand
  have hR := norm_gmR_le_card_all W u
  calc
    gmCubicSmoothingScale η T N M *
        gmCubicLocalBump (gmCubicSmoothingScale η T N M * (v - u)) *
        gmCubicRatioBump u * ‖gmR W u‖ ^ 2 ≤
      gmCubicSmoothingScale η T N M * 1 * 1 * (W.card : ℝ) ^ 2 := by
        gcongr
        · exact gmCubicRatioBump_nonneg _
        · exact gmCubicLocalBump_le_one _
        · exact gmCubicRatioBump_le_one _
    _ = gmCubicSmoothingScale η T N M * (W.card : ℝ) ^ 2 := by ring

theorem gmCubicSmoothedRIntegrand_eq_zero_of_not_mem_Icc
    {η T : ℝ} {N M : ℕ} (W : Finset ℝ) (v : ℝ) {u : ℝ}
    (hu : u ∉ Set.Icc (1 / 8 : ℝ) (33 / 8)) :
    gmCubicSmoothedRIntegrand η T N M W v u = 0 := by
  unfold gmCubicSmoothedRIntegrand
  rw [gmCubicRatioBump_eq_zero_of_not_mem_Icc hu]
  ring

theorem integrable_gmCubicSmoothedRIntegrand
    {η T : ℝ} {N M : ℕ} (W : Finset ℝ) (v : ℝ)
    (hscale : 0 ≤ gmCubicSmoothingScale η T N M) :
    Integrable (gmCubicSmoothedRIntegrand η T N M W v) := by
  let c : ℝ := gmCubicSmoothingScale η T N M * (W.card : ℝ) ^ 2
  let g : ℝ → ℝ := Set.indicator (Set.Icc (1 / 8 : ℝ) (33 / 8)) (fun _ => c)
  have hgOn : IntegrableOn (fun _ : ℝ => c) (Set.Icc (1 / 8 : ℝ) (33 / 8)) :=
    continuousOn_const.integrableOn_compact isCompact_Icc
  have hg : Integrable g := by
    exact hgOn.integrable_indicator measurableSet_Icc
  apply hg.mono' (measurable_gmCubicSmoothedRIntegrand
    η T N M W v).aestronglyMeasurable
  filter_upwards with u
  by_cases hu : u ∈ Set.Icc (1 / 8 : ℝ) (33 / 8)
  · have hgu : g u = c := by
      dsimp only [g]
      exact Set.indicator_of_mem hu _
    rw [hgu]
    rw [Real.norm_eq_abs, abs_of_nonneg
      (gmCubicSmoothedRIntegrand_nonneg W v u hscale)]
    exact gmCubicSmoothedRIntegrand_le W v u hscale
  · rw [gmCubicSmoothedRIntegrand_eq_zero_of_not_mem_Icc W v hu]
    have hgu : g u = 0 := by
      dsimp only [g]
      exact Set.indicator_of_notMem hu _
    rw [hgu]
    simp

/-- The width-`1/B` interval on which the fixed local bump is identically
one, intersected with the ratio support used in Proposition 7.2. -/
def gmCubicSmoothingNeighborhood (B v : ℝ) : Set ℝ :=
  Set.Icc (v - 1 / B) (v + 1 / B) ∩ Set.Icc (1 / 4 : ℝ) 4

theorem gmCubicLocalBump_one_on_smoothingNeighborhood
    {B v u : ℝ} (hB : 0 < B) (hu : u ∈ gmCubicSmoothingNeighborhood B v) :
    gmCubicLocalBump (B * (v - u)) = 1 := by
  apply gmCubicLocalBump_one
  have hwidth : |v - u| ≤ 1 / B := by
    rw [abs_le]
    constructor <;> linarith [hu.1.1, hu.1.2]
  rw [abs_mul, abs_of_pos hB]
  calc
    B * |v - u| ≤ B * (1 / B) := mul_le_mul_of_nonneg_left hwidth hB.le
    _ = 1 := by field_simp

theorem gmCubicSmoothedRIntegrand_eq_on_neighborhood
    {η T : ℝ} {N M : ℕ} (W : Finset ℝ) (v : ℝ) {u : ℝ}
    (hscale : 0 < gmCubicSmoothingScale η T N M)
    (hu : u ∈ gmCubicSmoothingNeighborhood
      (gmCubicSmoothingScale η T N M) v) :
    gmCubicSmoothedRIntegrand η T N M W v u =
      gmCubicSmoothingScale η T N M * ‖gmR W u‖ ^ 2 := by
  unfold gmCubicSmoothedRIntegrand
  rw [gmCubicLocalBump_one_on_smoothingNeighborhood hscale hu,
    gmCubicRatioBump_one hu.2]
  ring

theorem continuousOn_norm_gmR_sq (W : Finset ℝ) :
    ContinuousOn (fun u : ℝ => ‖gmR W u‖ ^ 2) (Set.Icc (1 / 4 : ℝ) 4) := by
  intro u hu
  exact ((continuousAt_gmR W (by linarith [hu.1])).norm.pow 2).continuousWithinAt

theorem integrableOn_norm_gmR_sq_smoothingNeighborhood
    (W : Finset ℝ) {B v : ℝ} :
    IntegrableOn (fun u : ℝ => ‖gmR W u‖ ^ 2)
      (gmCubicSmoothingNeighborhood B v) := by
  apply ((continuousOn_norm_gmR_sq W).mono (fun _ hu => hu.2)).integrableOn_compact
  exact isCompact_Icc.inter isCompact_Icc

/-- The exact nonnegative convolution under the square root in (7.5). -/
noncomputable def gmCubicSmoothedRSq
    (η T : ℝ) (N M : ℕ) (W : Finset ℝ) (v : ℝ) : ℝ :=
  ∫ u : ℝ, gmCubicSmoothedRIntegrand η T N M W v u

/-- Guth--Maynard's `\widetilde R` from equation (7.5). -/
noncomputable def gmCubicSmoothedR
    (η T : ℝ) (N M : ℕ) (W : Finset ℝ) (v : ℝ) : ℝ :=
  Real.sqrt (gmCubicSmoothedRSq η T N M W v)

theorem gmCubicSmoothedRSq_nonneg
    {η T : ℝ} {N M : ℕ} (W : Finset ℝ) (v : ℝ)
    (hscale : 0 ≤ gmCubicSmoothingScale η T N M) :
    0 ≤ gmCubicSmoothedRSq η T N M W v := by
  unfold gmCubicSmoothedRSq
  apply integral_nonneg
  intro u
  unfold gmCubicSmoothedRIntegrand
  exact mul_nonneg (mul_nonneg (mul_nonneg hscale
    (gmCubicLocalBump_nonneg _)) (gmCubicRatioBump_nonneg _)) (sq_nonneg _)

theorem gmCubicSmoothedR_sq
    {η T : ℝ} {N M : ℕ} (W : Finset ℝ) (v : ℝ)
    (hscale : 0 ≤ gmCubicSmoothingScale η T N M) :
    gmCubicSmoothedR η T N M W v ^ 2 =
      gmCubicSmoothedRSq η T N M W v := by
  unfold gmCubicSmoothedR
  exact Real.sq_sqrt (gmCubicSmoothedRSq_nonneg W v hscale)

/-- The defining local `L²` majorant of equation (7.5).  This is the exact
bridge used twice after Cauchy--Schwarz in the proof of Proposition 7.2. -/
theorem gmCubicSmoothingNeighborhood_integral_le_smoothedRSq
    {η T : ℝ} {N M : ℕ} (W : Finset ℝ) (v : ℝ)
    (hscale : 0 < gmCubicSmoothingScale η T N M) :
    gmCubicSmoothingScale η T N M *
        (∫ u in gmCubicSmoothingNeighborhood
          (gmCubicSmoothingScale η T N M) v, ‖gmR W u‖ ^ 2) ≤
      gmCubicSmoothedRSq η T N M W v := by
  have hintegrand := integrable_gmCubicSmoothedRIntegrand W v hscale.le
  have heq :
      (∫ u in gmCubicSmoothingNeighborhood
          (gmCubicSmoothingScale η T N M) v,
        gmCubicSmoothedRIntegrand η T N M W v u) =
      gmCubicSmoothingScale η T N M *
        (∫ u in gmCubicSmoothingNeighborhood
          (gmCubicSmoothingScale η T N M) v, ‖gmR W u‖ ^ 2) := by
    calc
      (∫ u in gmCubicSmoothingNeighborhood
          (gmCubicSmoothingScale η T N M) v,
        gmCubicSmoothedRIntegrand η T N M W v u) =
          ∫ u in gmCubicSmoothingNeighborhood
            (gmCubicSmoothingScale η T N M) v,
            gmCubicSmoothingScale η T N M * ‖gmR W u‖ ^ 2 := by
              apply MeasureTheory.setIntegral_congr_fun
                (measurableSet_Icc.inter measurableSet_Icc)
              intro u hu
              exact gmCubicSmoothedRIntegrand_eq_on_neighborhood W v hscale hu
      _ = gmCubicSmoothingScale η T N M *
          (∫ u in gmCubicSmoothingNeighborhood
            (gmCubicSmoothingScale η T N M) v, ‖gmR W u‖ ^ 2) := by
              rw [MeasureTheory.integral_const_mul]
  rw [← heq]
  exact MeasureTheory.setIntegral_le_integral hintegrand
    (ae_of_all _ fun u => gmCubicSmoothedRIntegrand_nonneg W v u hscale.le)

/-! ### Slicing the Proposition 7.1 cancellation slab -/

/-- The literal `v₂`-slice of the cancellation slab at a fixed `v₁`. -/
def gmCubicCancellationSlice (η T : ℝ) (N : ℕ)
    (m : ℤ × (ℤ × ℤ)) (v₁ : ℝ) : Set ℝ :=
  Set.Icc (1 / 2 : ℝ) 2 ∩
    {v₂ | |(m.1 : ℝ) * v₁ + (m.2.1 : ℝ) * v₂ + (m.2.2 : ℝ)| ≤
      T ^ η / (N : ℝ)}

theorem measurableSet_gmCubicCancellationSlice
    (η T : ℝ) (N : ℕ) (m : ℤ × (ℤ × ℤ)) (v₁ : ℝ) :
    MeasurableSet (gmCubicCancellationSlice η T N m v₁) := by
  apply measurableSet_Icc.inter
  exact measurableSet_le
    (((measurable_const.mul measurable_const).add
      (measurable_const.mul measurable_id)).add measurable_const).abs
    measurable_const

/-- Fubini disintegration of the exact two-dimensional cancellation
mass into the source `v₁` integral and its moving `v₂` slice. -/
theorem gmCubicCancellationMass_eq_iterated
    (η T : ℝ) (N : ℕ) (W : Finset ℝ) (m : ℤ × (ℤ × ℤ)) :
    gmCubicCancellationMass η T N W m =
      ∫ v₁ in Set.Icc (1 / 2 : ℝ) 2,
        ∫ v₂ in gmCubicCancellationSlice η T N m v₁,
          gmCubicRAmplitude W (v₁, v₂) := by
  let S := gmCubicCancellationSlab η T N m
  let F : ℝ × ℝ → ℝ := fun q => gmCubicRAmplitude W q
  have hInt : Integrable (S.indicator F) (volume.prod volume) := by
    have h := IntegrableOn.integrable_indicator
      (integrableOn_gmCubicRAmplitude_cancellationSlab η T N W m)
      (measurableSet_gmCubicCancellationSlab η T N m)
    simpa only [Measure.volume_eq_prod, S, F] using h
  have hpoint : ∀ v₁ : ℝ,
      (∫ v₂ : ℝ, S.indicator F (v₁, v₂)) =
        (Set.Icc (1 / 2 : ℝ) 2).indicator
          (fun x => ∫ v₂ in gmCubicCancellationSlice η T N m x,
            gmCubicRAmplitude W (x, v₂)) v₁ := by
    intro v₁
    by_cases hv₁ : v₁ ∈ Set.Icc (1 / 2 : ℝ) 2
    · rw [Set.indicator_of_mem hv₁]
      rw [← MeasureTheory.integral_indicator
        (measurableSet_gmCubicCancellationSlice η T N m v₁)]
      apply MeasureTheory.integral_congr_ae
      filter_upwards with v₂
      by_cases hv₂ : v₂ ∈ gmCubicCancellationSlice η T N m v₁
      · rw [Set.indicator_of_mem hv₂]
        apply Set.indicator_of_mem
        exact ⟨⟨hv₁, hv₂.1⟩, hv₂.2⟩
      · rw [Set.indicator_of_notMem hv₂]
        apply Set.indicator_of_notMem
        intro hS
        exact hv₂ ⟨hS.1.2, hS.2⟩
    · rw [Set.indicator_of_notMem hv₁]
      apply MeasureTheory.integral_eq_zero_of_ae
      filter_upwards with v₂
      apply Set.indicator_of_notMem
      intro hS
      exact hv₁ hS.1.1
  have hFubini := MeasureTheory.integral_prod (S.indicator F) hInt
  calc
    gmCubicCancellationMass η T N W m =
        ∫ q : ℝ × ℝ, S.indicator F q := by
      unfold gmCubicCancellationMass
      rw [MeasureTheory.integral_indicator
        (measurableSet_gmCubicCancellationSlab η T N m)]
    _ = ∫ v₁ : ℝ, ∫ v₂ : ℝ, S.indicator F (v₁, v₂) := hFubini
    _ = ∫ v₁ : ℝ, (Set.Icc (1 / 2 : ℝ) 2).indicator
          (fun x => ∫ v₂ in gmCubicCancellationSlice η T N m x,
            gmCubicRAmplitude W (x, v₂)) v₁ := by
      apply MeasureTheory.integral_congr_ae
      exact ae_of_all _ hpoint
    _ = ∫ v₁ in Set.Icc (1 / 2 : ℝ) 2,
          ∫ v₂ in gmCubicCancellationSlice η T N m v₁,
            gmCubicRAmplitude W (v₁, v₂) := by
      rw [MeasureTheory.integral_indicator measurableSet_Icc]

/-- The affine center of a `v₂` cancellation slice. -/
noncomputable def gmCubicCancellationCenter
    (m : ℤ × (ℤ × ℤ)) (v₁ : ℝ) : ℝ :=
  -((m.1 : ℝ) * v₁ + (m.2.2 : ℝ)) / (m.2.1 : ℝ)

/-- The center after the source substitution `v₂ ↦ v₂ / v₁`. -/
noncomputable def gmCubicReflectedCancellationCenter
    (m : ℤ × (ℤ × ℤ)) (v₁ : ℝ) : ℝ :=
  gmCubicCancellationCenter m v₁ / v₁

theorem gmCubicCancellationSlice_abs_sub_center_le
    {η T : ℝ} {N : ℕ} {m : ℤ × (ℤ × ℤ)} {v₁ v₂ : ℝ}
    (hm₂ : m.2.1 ≠ 0) (hv₂ : v₂ ∈ gmCubicCancellationSlice η T N m v₁) :
    |v₂ - gmCubicCancellationCenter m v₁| ≤
      T ^ η / (N : ℝ) / |(m.2.1 : ℝ)| := by
  have hm₂R : (m.2.1 : ℝ) ≠ 0 := by exact_mod_cast hm₂
  rw [le_div_iff₀ (abs_pos.mpr hm₂R)]
  rw [← abs_mul]
  have hid :
      (v₂ - gmCubicCancellationCenter m v₁) * (m.2.1 : ℝ) =
        (m.1 : ℝ) * v₁ + (m.2.1 : ℝ) * v₂ + (m.2.2 : ℝ) := by
    unfold gmCubicCancellationCenter
    field_simp
    ring
  rw [hid]
  exact hv₂.2

theorem gmCubicCancellationRadius_le_smoothingRadius
    {η T : ℝ} {N M : ℕ} {m₂ : ℤ}
    (hT : 0 < T) (hN : 0 < N) (hM : 0 < M)
    (hm₂ : (M : ℝ) ≤ |(m₂ : ℝ)|) :
    T ^ η / (N : ℝ) / |(m₂ : ℝ)| ≤
      1 / gmCubicSmoothingScale η T N M := by
  have hpow : 0 < T ^ η := Real.rpow_pos_of_pos hT η
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  have hMR : 0 < (M : ℝ) := by exact_mod_cast hM
  have hm₂pos : 0 < |(m₂ : ℝ)| := lt_of_lt_of_le hMR hm₂
  have hden : (N : ℝ) * (M : ℝ) ≤ (N : ℝ) * |(m₂ : ℝ)| := by
    gcongr
  have hfirst :
      T ^ η / ((N : ℝ) * |(m₂ : ℝ)|) ≤
        T ^ η / ((N : ℝ) * (M : ℝ)) :=
    div_le_div_of_nonneg_left hpow.le (mul_pos hNR hMR) hden
  calc
    T ^ η / (N : ℝ) / |(m₂ : ℝ)| =
        T ^ η / ((N : ℝ) * |(m₂ : ℝ)|) := by ring
    _ ≤ T ^ η / ((N : ℝ) * (M : ℝ)) := hfirst
    _ ≤ 2 * T ^ η / ((N : ℝ) * (M : ℝ)) := by
      apply div_le_div_of_nonneg_right _ (mul_pos hNR hMR).le
      nlinarith
    _ = 1 / gmCubicSmoothingScale η T N M := by
      unfold gmCubicSmoothingScale
      field_simp

theorem gmCubicCancellationSlice_subset_smoothingNeighborhood
    {η T : ℝ} {N M : ℕ} {m : ℤ × (ℤ × ℤ)} {v₁ : ℝ}
    (hT : 0 < T) (hN : 0 < N) (hM : 0 < M) (hm₂ : m.2.1 ≠ 0)
    (hMle : (M : ℝ) ≤ |(m.2.1 : ℝ)|) :
    gmCubicCancellationSlice η T N m v₁ ⊆
      gmCubicSmoothingNeighborhood (gmCubicSmoothingScale η T N M)
        (gmCubicCancellationCenter m v₁) := by
  intro v₂ hv₂
  have hrad := gmCubicCancellationRadius_le_smoothingRadius
    (η := η) (m₂ := m.2.1) hT hN hM hMle
  have hdist := (gmCubicCancellationSlice_abs_sub_center_le hm₂ hv₂).trans hrad
  refine ⟨?_, ?_⟩
  · rw [Set.mem_Icc]
    rw [abs_le] at hdist
    constructor <;> linarith [hdist.1, hdist.2]
  · constructor <;> linarith [hv₂.1.1, hv₂.1.2]

theorem measurableSet_gmCubicSmoothingNeighborhood (B v : ℝ) :
    MeasurableSet (gmCubicSmoothingNeighborhood B v) :=
  measurableSet_Icc.inter measurableSet_Icc

/-- The non-reflected `v₂` square mass in a cancellation slice is
majorized by the equation-(7.5) smoother at its affine center. -/
theorem integral_cancellationSlice_norm_gmR_sq_le_smoothedRSq_div
    {η T : ℝ} {N M : ℕ} (W : Finset ℝ) {m : ℤ × (ℤ × ℤ)} {v₁ : ℝ}
    (hT : 0 < T) (hN : 0 < N) (hM : 0 < M) (hm₂ : m.2.1 ≠ 0)
    (hMle : (M : ℝ) ≤ |(m.2.1 : ℝ)|) :
    (∫ v₂ in gmCubicCancellationSlice η T N m v₁, ‖gmR W v₂‖ ^ 2) ≤
      gmCubicSmoothedRSq η T N M W (gmCubicCancellationCenter m v₁) /
        gmCubicSmoothingScale η T N M := by
  let B := gmCubicSmoothingScale η T N M
  let c := gmCubicCancellationCenter m v₁
  have hB : 0 < B := gmCubicSmoothingScale_pos hT hN hM
  have hsub : gmCubicCancellationSlice η T N m v₁ ⊆
      gmCubicSmoothingNeighborhood B c := by
    simpa only [B, c] using
      gmCubicCancellationSlice_subset_smoothingNeighborhood
        hT hN hM hm₂ hMle
  have hmono :
      (∫ v₂ in gmCubicCancellationSlice η T N m v₁,
          ‖gmR W v₂‖ ^ 2) ≤
        ∫ v₂ in gmCubicSmoothingNeighborhood B c,
          ‖gmR W v₂‖ ^ 2 := by
    apply MeasureTheory.setIntegral_mono_set
      (integrableOn_norm_gmR_sq_smoothingNeighborhood W)
    · exact Filter.Eventually.of_forall fun _ => sq_nonneg _
    · exact hsub.eventuallyLE
  have hmajor := gmCubicSmoothingNeighborhood_integral_le_smoothedRSq
    (W := W) (v := c) hB
  rw [le_div_iff₀ hB]
  simpa only [mul_comm, B, c] using
    (mul_le_mul_of_nonneg_left hmono hB.le).trans hmajor

theorem gmCubicCancellationRadius_le_half_smoothingRadius
    {η T : ℝ} {N M : ℕ} {m₂ : ℤ}
    (hT : 0 < T) (hN : 0 < N) (hM : 0 < M)
    (hm₂ : (M : ℝ) ≤ |(m₂ : ℝ)|) :
    T ^ η / (N : ℝ) / |(m₂ : ℝ)| ≤
      (1 / 2 : ℝ) * (1 / gmCubicSmoothingScale η T N M) := by
  have hpow : 0 < T ^ η := Real.rpow_pos_of_pos hT η
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  have hMR : 0 < (M : ℝ) := by exact_mod_cast hM
  have hden : (N : ℝ) * (M : ℝ) ≤ (N : ℝ) * |(m₂ : ℝ)| := by
    gcongr
  calc
    T ^ η / (N : ℝ) / |(m₂ : ℝ)| =
        T ^ η / ((N : ℝ) * |(m₂ : ℝ)|) := by ring
    _ ≤ T ^ η / ((N : ℝ) * (M : ℝ)) :=
      div_le_div_of_nonneg_left hpow.le (mul_pos hNR hMR) hden
    _ = (1 / 2 : ℝ) * (1 / gmCubicSmoothingScale η T N M) := by
      unfold gmCubicSmoothingScale
      field_simp

/-- After `v₂ ↦ v₂/v₁`, every cancellation slice is still
inside the same fixed equation-(7.5) smoothing radius. -/
theorem gmCubicCancellationSlice_subset_reflected_preimage
    {η T : ℝ} {N M : ℕ} {m : ℤ × (ℤ × ℤ)} {v₁ : ℝ}
    (hT : 0 < T) (hN : 0 < N) (hM : 0 < M) (hm₂ : m.2.1 ≠ 0)
    (hMle : (M : ℝ) ≤ |(m.2.1 : ℝ)|)
    (hv₁ : v₁ ∈ Set.Icc (1 / 2 : ℝ) 2) :
    gmCubicCancellationSlice η T N m v₁ ⊆
      (fun v₂ : ℝ => v₂ / v₁) ⁻¹'
        gmCubicSmoothingNeighborhood (gmCubicSmoothingScale η T N M)
          (gmCubicReflectedCancellationCenter m v₁) := by
  intro v₂ hv₂
  have hv₁pos : 0 < v₁ := lt_of_lt_of_le (by norm_num) hv₁.1
  have hB : 0 < gmCubicSmoothingScale η T N M :=
    gmCubicSmoothingScale_pos hT hN hM
  have hhalf := (gmCubicCancellationSlice_abs_sub_center_le hm₂ hv₂).trans
    (gmCubicCancellationRadius_le_half_smoothingRadius
      (η := η) (m₂ := m.2.1) hT hN hM hMle)
  have hdist :
      |v₂ / v₁ - gmCubicReflectedCancellationCenter m v₁| ≤
        1 / gmCubicSmoothingScale η T N M := by
    unfold gmCubicReflectedCancellationCenter
    rw [← sub_div, abs_div, abs_of_pos hv₁pos]
    rw [div_le_iff₀ hv₁pos]
    have hinvB : 0 < 1 / gmCubicSmoothingScale η T N M := by positivity
    calc
      |v₂ - gmCubicCancellationCenter m v₁| ≤
          (1 / 2 : ℝ) * (1 / gmCubicSmoothingScale η T N M) := hhalf
      _ ≤ (1 / gmCubicSmoothingScale η T N M) * v₁ := by
        simpa only [mul_comm] using
          mul_le_mul_of_nonneg_left hv₁.1 hinvB.le
  refine ⟨?_, ?_⟩
  · rw [Set.mem_Icc]
    rw [abs_le] at hdist
    constructor <;> linarith [hdist.1, hdist.2]
  · have hv₂pos : 0 < v₂ := lt_of_lt_of_le (by norm_num) hv₂.1.1
    rw [Set.mem_Icc]
    constructor
    · rw [le_div_iff₀ hv₁pos]
      nlinarith [hv₂.1.1, hv₁.2]
    · rw [div_le_iff₀ hv₁pos]
      nlinarith [hv₂.1.2, hv₁.1]

/-- Set-integral form of the one-dimensional dilation formula used in
the first Cauchy--Schwarz factor of Proposition 7.2. -/
theorem setIntegral_preimage_div
    (f : ℝ → ℝ) (s : Set ℝ) (hs : MeasurableSet s) (a : ℝ) :
    (∫ x in (fun y : ℝ => y / a) ⁻¹' s, f (x / a)) =
      |a| * ∫ u in s, f u := by
  have hchange := Measure.integral_comp_div (s.indicator f) a
  calc
    (∫ x in (fun y : ℝ => y / a) ⁻¹' s, f (x / a)) =
        ∫ x : ℝ, ((fun y : ℝ => y / a) ⁻¹' s).indicator
          (fun y => f (y / a)) x := by
      exact (MeasureTheory.integral_indicator
        (hs.preimage (measurable_id.div_const a))).symm
    _ = ∫ x : ℝ, s.indicator f (x / a) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      by_cases hx : x / a ∈ s <;> simp [hx]
    _ = |a| * ∫ u : ℝ, s.indicator f u := by
      simpa [smul_eq_mul] using hchange
    _ = |a| * ∫ u in s, f u := by rw [MeasureTheory.integral_indicator hs]

/-- The reflected `v₂/v₁` square mass in a cancellation slice is
majorized by the same source smoother, with only the Jacobian factor
`v₁ ≤ 2`. -/
theorem integral_cancellationSlice_norm_gmR_div_sq_le
    {η T : ℝ} {N M : ℕ} (W : Finset ℝ) {m : ℤ × (ℤ × ℤ)} {v₁ : ℝ}
    (hT : 0 < T) (hN : 0 < N) (hM : 0 < M) (hm₂ : m.2.1 ≠ 0)
    (hMle : (M : ℝ) ≤ |(m.2.1 : ℝ)|)
    (hv₁ : v₁ ∈ Set.Icc (1 / 2 : ℝ) 2) :
    (∫ v₂ in gmCubicCancellationSlice η T N m v₁,
        ‖gmR W (v₂ / v₁)‖ ^ 2) ≤
      2 * (gmCubicSmoothedRSq η T N M W
        (gmCubicReflectedCancellationCenter m v₁) /
          gmCubicSmoothingScale η T N M) := by
  let B := gmCubicSmoothingScale η T N M
  let c := gmCubicReflectedCancellationCenter m v₁
  let U := gmCubicSmoothingNeighborhood B c
  let P := (fun v₂ : ℝ => v₂ / v₁) ⁻¹' U
  let f : ℝ → ℝ := fun u => ‖gmR W u‖ ^ 2
  have hv₁pos : 0 < v₁ := lt_of_lt_of_le (by norm_num) hv₁.1
  have hv₁ne : v₁ ≠ 0 := hv₁pos.ne'
  have hB : 0 < B := gmCubicSmoothingScale_pos hT hN hM
  have hUmeas : MeasurableSet U := measurableSet_gmCubicSmoothingNeighborhood B c
  have hPmeas : MeasurableSet P :=
    hUmeas.preimage (measurable_id.div_const v₁)
  have hsub : gmCubicCancellationSlice η T N m v₁ ⊆ P := by
    simpa only [B, c, U, P] using
      gmCubicCancellationSlice_subset_reflected_preimage
        hT hN hM hm₂ hMle hv₁
  have hUInt : IntegrableOn f U := by
    simpa only [f, U, B, c] using
      integrableOn_norm_gmR_sq_smoothingNeighborhood
        W (B := B) (v := c)
  have hUIndicator : Integrable (U.indicator f) :=
    hUInt.integrable_indicator hUmeas
  have hComp : Integrable (fun x : ℝ => U.indicator f (x / v₁)) :=
    hUIndicator.comp_div hv₁ne
  have hPIndicator : Integrable (P.indicator (fun x => f (x / v₁))) := by
    apply hComp.congr
    exact ae_of_all _ fun x => by
      by_cases hx : x / v₁ ∈ U <;> simp [P, hx]
  have hPInt : IntegrableOn (fun x => f (x / v₁)) P :=
    (integrable_indicator_iff hPmeas).mp hPIndicator
  have hmono :
      (∫ v₂ in gmCubicCancellationSlice η T N m v₁,
          f (v₂ / v₁)) ≤
        ∫ v₂ in P, f (v₂ / v₁) := by
    apply MeasureTheory.setIntegral_mono_set hPInt
    · exact Filter.Eventually.of_forall fun _ => sq_nonneg _
    · exact hsub.eventuallyLE
  have hchange :
      (∫ v₂ in P, f (v₂ / v₁)) =
        v₁ * ∫ u in U, f u := by
    have h := setIntegral_preimage_div f U hUmeas v₁
    simpa only [P, abs_of_pos hv₁pos] using h
  have hlocalNonneg : 0 ≤ ∫ u in U, f u := by
    apply MeasureTheory.integral_nonneg_of_ae
    exact Filter.Eventually.of_forall fun _ => sq_nonneg _
  have hmajor := gmCubicSmoothingNeighborhood_integral_le_smoothedRSq
    (W := W) (v := c) hB
  have hlocal :
      (∫ u in U, f u) ≤
        gmCubicSmoothedRSq η T N M W c / B := by
    rw [le_div_iff₀ hB]
    simpa only [f, U, B, c, mul_comm] using hmajor
  calc
    (∫ v₂ in gmCubicCancellationSlice η T N m v₁,
        ‖gmR W (v₂ / v₁)‖ ^ 2) =
        ∫ v₂ in gmCubicCancellationSlice η T N m v₁,
          f (v₂ / v₁) := rfl
    _ ≤ ∫ v₂ in P, f (v₂ / v₁) := hmono
    _ = v₁ * ∫ u in U, f u := hchange
    _ ≤ 2 * ∫ u in U, f u := by
      exact mul_le_mul_of_nonneg_right hv₁.2 hlocalNonneg
    _ ≤ 2 * (gmCubicSmoothedRSq η T N M W c / B) := by
      gcongr
    _ = 2 * (gmCubicSmoothedRSq η T N M W
        (gmCubicReflectedCancellationCenter m v₁) /
          gmCubicSmoothingScale η T N M) := rfl

theorem norm_gmR_one_div
    (W : Finset ℝ) {v : ℝ} (hv : v ≠ 0) :
    ‖gmR W (1 / v)‖ = ‖gmR W v‖ := by
  have hinv : 1 / v ≠ 0 := one_div_ne_zero hv
  rw [gmR_eq_gmRPhase_log hinv, gmR_eq_gmRPhase_log hv]
  have hlog : Real.log |1 / v| = -Real.log |v| := by
    rw [abs_div, abs_one, one_div]
    exact Real.log_inv |v|
  rw [hlog, norm_gmRPhase_neg]

/-- Cauchy--Schwarz on the literal moving `v₂` slice in (7.6). -/
theorem integral_cancellationSlice_norm_mul_le_sqrt
    (η T : ℝ) (N : ℕ) (W : Finset ℝ) (m : ℤ × (ℤ × ℤ))
    {v₁ : ℝ} (hv₁ : v₁ ∈ Set.Icc (1 / 2 : ℝ) 2) :
    (∫ v₂ in gmCubicCancellationSlice η T N m v₁,
        ‖gmR W (v₂ / v₁)‖ * ‖gmR W v₂‖) ≤
      Real.sqrt (∫ v₂ in gmCubicCancellationSlice η T N m v₁,
          ‖gmR W (v₂ / v₁)‖ ^ 2) *
        Real.sqrt (∫ v₂ in gmCubicCancellationSlice η T N m v₁,
          ‖gmR W v₂‖ ^ 2) := by
  let s := gmCubicCancellationSlice η T N m v₁
  let μ : Measure ℝ := volume.restrict s
  let f : ℝ → ℝ := fun v₂ => ‖gmR W (v₂ / v₁)‖
  let g : ℝ → ℝ := fun v₂ => ‖gmR W v₂‖
  have hv₁pos : 0 < v₁ := lt_of_lt_of_le (by norm_num) hv₁.1
  have hv₁ne : v₁ ≠ 0 := hv₁pos.ne'
  have hfCont : ContinuousOn f (Set.Icc (1 / 2 : ℝ) 2) := by
    intro v₂ hv₂
    have hv₂pos : 0 < v₂ := lt_of_lt_of_le (by norm_num) hv₂.1
    have hratio : v₂ / v₁ ≠ 0 := div_ne_zero hv₂pos.ne' hv₁ne
    have hcomp : ContinuousAt (fun x : ℝ => gmR W (x / v₁)) v₂ :=
      (continuousAt_gmR W hratio).tendsto.comp
        (continuousAt_id.div_const v₁).tendsto
    exact hcomp.norm.continuousWithinAt
  have hgCont : ContinuousOn g (Set.Icc (1 / 2 : ℝ) 2) := by
    intro v₂ hv₂
    exact (continuousAt_gmR W
      (lt_of_lt_of_le (by norm_num) hv₂.1).ne').norm.continuousWithinAt
  have hf2Int : Integrable (fun v₂ => f v₂ ^ 2) μ := by
    change IntegrableOn (fun v₂ => f v₂ ^ 2) s
    exact ((hfCont.pow 2).integrableOn_compact isCompact_Icc).mono_set inter_subset_left
  have hg2Int : Integrable (fun v₂ => g v₂ ^ 2) μ := by
    change IntegrableOn (fun v₂ => g v₂ ^ 2) s
    exact ((hgCont.pow 2).integrableOn_compact isCompact_Icc).mono_set inter_subset_left
  have hfMeas : Measurable f := by
    exact ((measurable_gmR W).comp (measurable_id.div_const v₁)).norm
  have hgMeas : Measurable g := by
    exact (measurable_gmR W).norm
  have hfMem : MemLp f (ENNReal.ofReal (2 : ℝ)) μ := by
    have h : MemLp f 2 μ :=
      (memLp_two_iff_integrable_sq hfMeas.aestronglyMeasurable).2 hf2Int
    simpa using h
  have hgMem : MemLp g (ENNReal.ofReal (2 : ℝ)) μ := by
    have h : MemLp g 2 μ :=
      (memLp_two_iff_integrable_sq hgMeas.aestronglyMeasurable).2 hg2Int
    simpa using h
  have hpq : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hHolder := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (Filter.Eventually.of_forall fun x => norm_nonneg _)
    (Filter.Eventually.of_forall fun x => norm_nonneg _) hfMem hgMem
  dsimp only [μ, f, g, s] at hHolder
  simpa only [Real.sqrt_eq_rpow, one_div, Real.rpow_two] using hHolder

/-- The exact post-Cauchy--Schwarz majorant before extracting the common
`1/(NM)` scale in Proposition 7.2. -/
noncomputable def gmCubicRawSmoothedSliceMajorant
    (η T : ℝ) (N M : ℕ) (W : Finset ℝ)
    (m : ℤ × (ℤ × ℤ)) (v₁ : ℝ) : ℝ :=
  ‖gmR W v₁‖ *
    Real.sqrt (2 * (gmCubicSmoothedRSq η T N M W
      (gmCubicReflectedCancellationCenter m v₁) /
        gmCubicSmoothingScale η T N M)) *
    Real.sqrt (gmCubicSmoothedRSq η T N M W
      (gmCubicCancellationCenter m v₁) /
        gmCubicSmoothingScale η T N M)

theorem integral_cancellationSlice_amplitude_le_rawSmoothed
    {η T : ℝ} {N M : ℕ} (W : Finset ℝ) {m : ℤ × (ℤ × ℤ)} {v₁ : ℝ}
    (hT : 0 < T) (hN : 0 < N) (hM : 0 < M) (hm₂ : m.2.1 ≠ 0)
    (hMle : (M : ℝ) ≤ |(m.2.1 : ℝ)|)
    (hv₁ : v₁ ∈ Set.Icc (1 / 2 : ℝ) 2) :
    (∫ v₂ in gmCubicCancellationSlice η T N m v₁,
        gmCubicRAmplitude W (v₁, v₂)) ≤
      gmCubicRawSmoothedSliceMajorant η T N M W m v₁ := by
  let A := ∫ v₂ in gmCubicCancellationSlice η T N m v₁,
    ‖gmR W (v₂ / v₁)‖ ^ 2
  let D := ∫ v₂ in gmCubicCancellationSlice η T N m v₁,
    ‖gmR W v₂‖ ^ 2
  let X := gmCubicSmoothedRSq η T N M W
    (gmCubicReflectedCancellationCenter m v₁) /
      gmCubicSmoothingScale η T N M
  let Y := gmCubicSmoothedRSq η T N M W
    (gmCubicCancellationCenter m v₁) /
      gmCubicSmoothingScale η T N M
  have hA : A ≤ 2 * X := by
    simpa only [A, X] using integral_cancellationSlice_norm_gmR_div_sq_le
      W hT hN hM hm₂ hMle hv₁
  have hD : D ≤ Y := by
    simpa only [D, Y] using integral_cancellationSlice_norm_gmR_sq_le_smoothedRSq_div
      W hT hN hM hm₂ hMle
  have hRewrite :
      (∫ v₂ in gmCubicCancellationSlice η T N m v₁,
          gmCubicRAmplitude W (v₁, v₂)) =
        ‖gmR W v₁‖ *
          ∫ v₂ in gmCubicCancellationSlice η T N m v₁,
            ‖gmR W (v₂ / v₁)‖ * ‖gmR W v₂‖ := by
    calc
      (∫ v₂ in gmCubicCancellationSlice η T N m v₁,
          gmCubicRAmplitude W (v₁, v₂)) =
          ∫ v₂ in gmCubicCancellationSlice η T N m v₁,
            ‖gmR W v₁‖ *
              (‖gmR W (v₂ / v₁)‖ * ‖gmR W v₂‖) := by
        apply MeasureTheory.setIntegral_congr_fun
          (measurableSet_gmCubicCancellationSlice η T N m v₁)
        intro v₂ hv₂
        unfold gmCubicRAmplitude
        change ‖gmR W v₁‖ * ‖gmR W (v₂ / v₁)‖ * ‖gmR W (1 / v₂)‖ =
          ‖gmR W v₁‖ * (‖gmR W (v₂ / v₁)‖ * ‖gmR W v₂‖)
        rw [norm_gmR_one_div W
          (lt_of_lt_of_le (by norm_num) hv₂.1.1).ne']
        ring
      _ = ‖gmR W v₁‖ *
          ∫ v₂ in gmCubicCancellationSlice η T N m v₁,
            ‖gmR W (v₂ / v₁)‖ * ‖gmR W v₂‖ := by
        rw [MeasureTheory.integral_const_mul]
  have hCS := integral_cancellationSlice_norm_mul_le_sqrt
    η T N W m hv₁
  have hInner :
      (∫ v₂ in gmCubicCancellationSlice η T N m v₁,
          ‖gmR W (v₂ / v₁)‖ * ‖gmR W v₂‖) ≤
        Real.sqrt (2 * X) * Real.sqrt Y := by
    calc
      (∫ v₂ in gmCubicCancellationSlice η T N m v₁,
          ‖gmR W (v₂ / v₁)‖ * ‖gmR W v₂‖) ≤
          Real.sqrt A * Real.sqrt D := hCS
      _ ≤ Real.sqrt (2 * X) * Real.sqrt Y := by
        exact mul_le_mul (Real.sqrt_le_sqrt hA) (Real.sqrt_le_sqrt hD)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  rw [hRewrite]
  unfold gmCubicRawSmoothedSliceMajorant
  calc
    ‖gmR W v₁‖ *
        (∫ v₂ in gmCubicCancellationSlice η T N m v₁,
          ‖gmR W (v₂ / v₁)‖ * ‖gmR W v₂‖) ≤
        ‖gmR W v₁‖ * (Real.sqrt (2 * X) * Real.sqrt Y) :=
      mul_le_mul_of_nonneg_left hInner (norm_nonneg _)
    _ = ‖gmR W v₁‖ * Real.sqrt (2 * (gmCubicSmoothedRSq η T N M W
          (gmCubicReflectedCancellationCenter m v₁) /
            gmCubicSmoothingScale η T N M)) *
        Real.sqrt (gmCubicSmoothedRSq η T N M W
          (gmCubicCancellationCenter m v₁) /
            gmCubicSmoothingScale η T N M) := by
      dsimp only [X, Y]
      ring

/-- The two square-root losses from the slice Cauchy--Schwarz argument
extract the single reciprocal smoothing scale required in (7.6).  The
fixed factor `2` harmlessly majorizes the exact Jacobian factor
`sqrt 2`. -/
theorem sqrt_two_mul_div_mul_sqrt_div_le
    {B X Y : ℝ} (hB : 0 < B) (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    Real.sqrt (2 * (X / B)) * Real.sqrt (Y / B) ≤
      (2 / B) * (Real.sqrt X * Real.sqrt Y) := by
  have hsqrtB : 0 < Real.sqrt B := Real.sqrt_pos.2 hB
  have hsqrtBne : Real.sqrt B ≠ 0 := hsqrtB.ne'
  have hsqrtTwo : Real.sqrt (2 : ℝ) ≤ 2 := by
    have hsqrtTwoNonneg : 0 ≤ Real.sqrt (2 : ℝ) := Real.sqrt_nonneg _
    have hsqrtTwoSq : Real.sqrt (2 : ℝ) ^ 2 = 2 :=
      Real.sq_sqrt (by norm_num)
    nlinarith
  rw [show 2 * (X / B) = (2 * X) / B by ring,
    Real.sqrt_div (mul_nonneg (by norm_num) hX) B,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
    Real.sqrt_div hY B]
  have hsqrtBmul : Real.sqrt B * Real.sqrt B = B :=
    Real.mul_self_sqrt hB.le
  rw [div_mul_div_comm]
  rw [div_le_iff₀ (mul_pos hsqrtB hsqrtB)]
  rw [hsqrtBmul]
  calc
    (Real.sqrt 2 * Real.sqrt X) * Real.sqrt Y ≤
        (2 * Real.sqrt X) * Real.sqrt Y := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hsqrtTwo (Real.sqrt_nonneg X))
        (Real.sqrt_nonneg Y)
    _ = (2 / B * (Real.sqrt X * Real.sqrt Y)) * B := by
      field_simp

/-- Equation (7.6)'s pointwise source integrand. -/
noncomputable def gmCubicSmoothedModeIntegrand
    (η T : ℝ) (N M : ℕ) (W : Finset ℝ)
    (m : ℤ × (ℤ × ℤ)) (v₁ : ℝ) : ℝ :=
  ‖gmR W v₁‖ *
    gmCubicSmoothedR η T N M W
      (gmCubicReflectedCancellationCenter m v₁) *
    gmCubicSmoothedR η T N M W
      (gmCubicCancellationCenter m v₁)

theorem gmCubicRawSmoothedSliceMajorant_le
    {η T : ℝ} {N M : ℕ} (W : Finset ℝ)
    (m : ℤ × (ℤ × ℤ)) (v₁ : ℝ)
    (hT : 0 < T) (hN : 0 < N) (hM : 0 < M) :
    gmCubicRawSmoothedSliceMajorant η T N M W m v₁ ≤
      (2 / gmCubicSmoothingScale η T N M) *
        gmCubicSmoothedModeIntegrand η T N M W m v₁ := by
  let B := gmCubicSmoothingScale η T N M
  let X := gmCubicSmoothedRSq η T N M W
    (gmCubicReflectedCancellationCenter m v₁)
  let Y := gmCubicSmoothedRSq η T N M W
    (gmCubicCancellationCenter m v₁)
  have hB : 0 < B := gmCubicSmoothingScale_pos hT hN hM
  have hX : 0 ≤ X := gmCubicSmoothedRSq_nonneg W _ hB.le
  have hY : 0 ≤ Y := gmCubicSmoothedRSq_nonneg W _ hB.le
  have hsqrt := sqrt_two_mul_div_mul_sqrt_div_le hB hX hY
  unfold gmCubicRawSmoothedSliceMajorant gmCubicSmoothedModeIntegrand
  dsimp only [B, X, Y] at hsqrt ⊢
  unfold gmCubicSmoothedR
  calc
    ‖gmR W v₁‖ *
        Real.sqrt (2 *
          (gmCubicSmoothedRSq η T N M W
            (gmCubicReflectedCancellationCenter m v₁) /
              gmCubicSmoothingScale η T N M)) *
        Real.sqrt
          (gmCubicSmoothedRSq η T N M W
            (gmCubicCancellationCenter m v₁) /
              gmCubicSmoothingScale η T N M) =
      ‖gmR W v₁‖ *
        (Real.sqrt (2 *
          (gmCubicSmoothedRSq η T N M W
            (gmCubicReflectedCancellationCenter m v₁) /
              gmCubicSmoothingScale η T N M)) *
        Real.sqrt
          (gmCubicSmoothedRSq η T N M W
            (gmCubicCancellationCenter m v₁) /
              gmCubicSmoothingScale η T N M)) := by ring
    _ ≤
      ‖gmR W v₁‖ *
        ((2 / gmCubicSmoothingScale η T N M) *
          (Real.sqrt
              (gmCubicSmoothedRSq η T N M W
                (gmCubicReflectedCancellationCenter m v₁)) *
            Real.sqrt
              (gmCubicSmoothedRSq η T N M W
                (gmCubicCancellationCenter m v₁)))) := by
        exact mul_le_mul_of_nonneg_left hsqrt
          (show 0 ≤ ‖gmR W v₁‖ from norm_nonneg _)
    _ = (2 / gmCubicSmoothingScale η T N M) *
        (‖gmR W v₁‖ *
          Real.sqrt
            (gmCubicSmoothedRSq η T N M W
              (gmCubicReflectedCancellationCenter m v₁)) *
          Real.sqrt
            (gmCubicSmoothedRSq η T N M W
              (gmCubicCancellationCenter m v₁))) := by ring

theorem measurable_gmCubicSmoothedRIntegrand_uncurry
    (η T : ℝ) (N M : ℕ) (W : Finset ℝ) :
    Measurable (fun p : ℝ × ℝ =>
      gmCubicSmoothedRIntegrand η T N M W p.1 p.2) := by
  have hlinear : Measurable (fun p : ℝ × ℝ =>
      gmCubicSmoothingScale η T N M * (p.1 - p.2)) :=
    measurable_const.mul (measurable_fst.sub measurable_snd)
  have hlocalContinuous : Continuous gmCubicLocalBump := by
    unfold gmCubicLocalBump
    exact dfiUnitRedundantBump.continuous.comp (continuous_id.div_const 2)
  have hlocal : Measurable (fun p : ℝ × ℝ =>
      gmCubicLocalBump
        (gmCubicSmoothingScale η T N M * (p.1 - p.2))) :=
    hlocalContinuous.measurable.comp hlinear
  have hratio : Measurable (fun p : ℝ × ℝ => gmCubicRatioBump p.2) :=
    gmCubicRatioBump.continuous.measurable.comp measurable_snd
  have hR : Measurable (fun p : ℝ × ℝ => ‖gmR W p.2‖ ^ 2) :=
    ((measurable_gmR W).comp measurable_snd).norm.pow_const 2
  exact ((measurable_const.mul hlocal).mul hratio).mul hR

theorem measurable_gmCubicSmoothedRSq
    (η T : ℝ) (N M : ℕ) (W : Finset ℝ) :
    Measurable (gmCubicSmoothedRSq η T N M W) := by
  have hjoint : StronglyMeasurable (fun p : ℝ × ℝ =>
      gmCubicSmoothedRIntegrand η T N M W p.1 p.2) :=
    (measurable_gmCubicSmoothedRIntegrand_uncurry η T N M W).stronglyMeasurable
  exact hjoint.integral_prod_right'.measurable

theorem measurable_gmCubicSmoothedR
    (η T : ℝ) (N M : ℕ) (W : Finset ℝ) :
    Measurable (gmCubicSmoothedR η T N M W) := by
  unfold gmCubicSmoothedR
  exact Real.continuous_sqrt.measurable.comp
    (measurable_gmCubicSmoothedRSq η T N M W)

theorem gmCubicSmoothedRSq_le
    {η T : ℝ} {N M : ℕ} (W : Finset ℝ) (v : ℝ)
    (hscale : 0 ≤ gmCubicSmoothingScale η T N M) :
    gmCubicSmoothedRSq η T N M W v ≤
      gmCubicSmoothingScale η T N M * (W.card : ℝ) ^ 2 * 4 := by
  let c : ℝ := gmCubicSmoothingScale η T N M * (W.card : ℝ) ^ 2
  let g : ℝ → ℝ := Set.indicator (Set.Icc (1 / 8 : ℝ) (33 / 8)) (fun _ => c)
  have hf := integrable_gmCubicSmoothedRIntegrand W v hscale
  have hgOn : IntegrableOn (fun _ : ℝ => c) (Set.Icc (1 / 8 : ℝ) (33 / 8)) :=
    continuousOn_const.integrableOn_compact isCompact_Icc
  have hg : Integrable g := hgOn.integrable_indicator measurableSet_Icc
  have hpoint : ∀ u : ℝ,
      gmCubicSmoothedRIntegrand η T N M W v u ≤ g u := by
    intro u
    by_cases hu : u ∈ Set.Icc (1 / 8 : ℝ) (33 / 8)
    · have hgu : g u = c := by
        dsimp only [g]
        exact Set.indicator_of_mem hu _
      rw [hgu]
      exact gmCubicSmoothedRIntegrand_le W v u hscale
    · rw [gmCubicSmoothedRIntegrand_eq_zero_of_not_mem_Icc W v hu]
      have hgu : g u = 0 := by
        dsimp only [g]
        exact Set.indicator_of_notMem hu _
      rw [hgu]
  calc
    gmCubicSmoothedRSq η T N M W v =
        ∫ u : ℝ, gmCubicSmoothedRIntegrand η T N M W v u := rfl
    _ ≤ ∫ u : ℝ, g u := integral_mono hf hg hpoint
    _ = c * 4 := by
      simp [g, c, max_def]
      norm_num
      ring
    _ = gmCubicSmoothingScale η T N M * (W.card : ℝ) ^ 2 *
        4 := rfl

theorem measurable_gmCubicSmoothedModeIntegrand
    (η T : ℝ) (N M : ℕ) (W : Finset ℝ)
    (m : ℤ × (ℤ × ℤ)) :
    Measurable (gmCubicSmoothedModeIntegrand η T N M W m) := by
  have hcenter : Measurable (gmCubicCancellationCenter m) := by
    unfold gmCubicCancellationCenter
    exact ((measurable_const.mul measurable_id).add measurable_const).neg.div_const _
  have hreflected : Measurable (gmCubicReflectedCancellationCenter m) := by
    unfold gmCubicReflectedCancellationCenter
    exact hcenter.div measurable_id
  unfold gmCubicSmoothedModeIntegrand
  exact (((measurable_gmR W).norm.mul
    ((measurable_gmCubicSmoothedR η T N M W).comp hreflected)).mul
      ((measurable_gmCubicSmoothedR η T N M W).comp hcenter))

theorem gmCubicSmoothedModeIntegrand_nonneg
    (η T : ℝ) (N M : ℕ) (W : Finset ℝ)
    (m : ℤ × (ℤ × ℤ)) (v₁ : ℝ) :
    0 ≤ gmCubicSmoothedModeIntegrand η T N M W m v₁ := by
  unfold gmCubicSmoothedModeIntegrand gmCubicSmoothedR
  positivity

theorem integrableOn_gmCubicSmoothedModeIntegrand
    {η T : ℝ} {N M : ℕ} (W : Finset ℝ)
    (m : ℤ × (ℤ × ℤ)) (hscale : 0 ≤ gmCubicSmoothingScale η T N M) :
    IntegrableOn (gmCubicSmoothedModeIntegrand η T N M W m)
      (Set.Icc (1 / 2 : ℝ) 2) := by
  let C : ℝ := (W.card : ℝ) *
    (Real.sqrt
      (gmCubicSmoothingScale η T N M * (W.card : ℝ) ^ 2 * 4)) ^ 2
  apply IntegrableOn.of_bound measure_Icc_lt_top
    (measurable_gmCubicSmoothedModeIntegrand η T N M W m).aestronglyMeasurable.restrict
    C
  filter_upwards with v₁
  rw [Real.norm_eq_abs, abs_of_nonneg
    (gmCubicSmoothedModeIntegrand_nonneg η T N M W m v₁)]
  unfold gmCubicSmoothedModeIntegrand gmCubicSmoothedR
  have href := gmCubicSmoothedRSq_le W
    (gmCubicReflectedCancellationCenter m v₁) hscale
  have hcenter := gmCubicSmoothedRSq_le W
    (gmCubicCancellationCenter m v₁) hscale
  have hR := norm_gmR_le_card_all W v₁
  dsimp only [C]
  let S := Real.sqrt
    (gmCubicSmoothingScale η T N M * (W.card : ℝ) ^ 2 * 4)
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  have hRefS : Real.sqrt
      (gmCubicSmoothedRSq η T N M W
        (gmCubicReflectedCancellationCenter m v₁)) ≤ S :=
    Real.sqrt_le_sqrt href
  have hCenterS : Real.sqrt
      (gmCubicSmoothedRSq η T N M W
        (gmCubicCancellationCenter m v₁)) ≤ S :=
    Real.sqrt_le_sqrt hcenter
  calc
    ‖gmR W v₁‖ *
        Real.sqrt (gmCubicSmoothedRSq η T N M W
          (gmCubicReflectedCancellationCenter m v₁)) *
        Real.sqrt (gmCubicSmoothedRSq η T N M W
          (gmCubicCancellationCenter m v₁)) ≤
      (W.card : ℝ) * S * S := by
        exact mul_le_mul
          (mul_le_mul hR hRefS (Real.sqrt_nonneg _) (Nat.cast_nonneg _))
          hCenterS (Real.sqrt_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hS)
    _ = (W.card : ℝ) * S ^ 2 := by ring

/-- The one-dimensional smoothed integral on the right side of (7.6). -/
noncomputable def gmCubicSmoothedModeIntegral
    (η T : ℝ) (N M : ℕ) (W : Finset ℝ)
    (m : ℤ × (ℤ × ℤ)) : ℝ :=
  ∫ v₁ in Set.Icc (1 / 2 : ℝ) 2,
    gmCubicSmoothedModeIntegrand η T N M W m v₁

theorem gmCubicSmoothedModeIntegral_nonneg
    (η T : ℝ) (N M : ℕ) (W : Finset ℝ)
    (m : ℤ × (ℤ × ℤ)) :
    0 ≤ gmCubicSmoothedModeIntegral η T N M W m := by
  unfold gmCubicSmoothedModeIntegral
  apply MeasureTheory.integral_nonneg_of_ae
  exact Filter.Eventually.of_forall fun v₁ =>
    gmCubicSmoothedModeIntegrand_nonneg η T N M W m v₁

/-- Source equation (7.6), retaining its exact moving cancellation slice,
both local square smoothers, and the reflected Jacobian. -/
theorem gmCubicCancellationMass_le_smoothedModeIntegral
    {η T : ℝ} {N M : ℕ} (W : Finset ℝ) {m : ℤ × (ℤ × ℤ)}
    (hT : 0 < T) (hN : 0 < N) (hM : 0 < M)
    (hm₂ : m.2.1 ≠ 0) (hMle : (M : ℝ) ≤ |(m.2.1 : ℝ)|) :
    gmCubicCancellationMass η T N W m ≤
      (2 / gmCubicSmoothingScale η T N M) *
        gmCubicSmoothedModeIntegral η T N M W m := by
  have hB : 0 < gmCubicSmoothingScale η T N M :=
    gmCubicSmoothingScale_pos hT hN hM
  have hsourceInt := integrableOn_gmCubicSmoothedModeIntegrand W m hB.le
  rw [gmCubicCancellationMass_eq_iterated]
  calc
    (∫ v₁ in Set.Icc (1 / 2 : ℝ) 2,
        ∫ v₂ in gmCubicCancellationSlice η T N m v₁,
          gmCubicRAmplitude W (v₁, v₂)) ≤
      ∫ v₁ in Set.Icc (1 / 2 : ℝ) 2,
        (2 / gmCubicSmoothingScale η T N M) *
          gmCubicSmoothedModeIntegrand η T N M W m v₁ := by
      apply MeasureTheory.integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall fun v₁ => by
          apply MeasureTheory.integral_nonneg_of_ae
          exact Filter.Eventually.of_forall fun v₂ =>
            gmCubicRAmplitude_nonneg W (v₁, v₂)
      · exact hsourceInt.const_mul _
      · filter_upwards [ae_restrict_mem measurableSet_Icc] with v₁ hv₁
        calc
          (∫ v₂ in gmCubicCancellationSlice η T N m v₁,
              gmCubicRAmplitude W (v₁, v₂)) ≤
            gmCubicRawSmoothedSliceMajorant η T N M W m v₁ :=
              integral_cancellationSlice_amplitude_le_rawSmoothed
                W hT hN hM hm₂ hMle hv₁
          _ ≤ (2 / gmCubicSmoothingScale η T N M) *
              gmCubicSmoothedModeIntegrand η T N M W m v₁ :=
                gmCubicRawSmoothedSliceMajorant_le W m v₁ hT hN hM
    _ = (2 / gmCubicSmoothingScale η T N M) *
        gmCubicSmoothedModeIntegral η T N M W m := by
      rw [MeasureTheory.integral_const_mul]
      rfl

theorem two_div_gmCubicSmoothingScale
    {η T : ℝ} {N M : ℕ} (hT : 0 < T) (hN : 0 < N) (hM : 0 < M) :
    2 / gmCubicSmoothingScale η T N M =
      4 * T ^ η / ((N : ℝ) * (M : ℝ)) := by
  unfold gmCubicSmoothingScale
  have hTpow : T ^ η ≠ 0 := (Real.rpow_pos_of_pos hT η).ne'
  have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hMreal : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  field_simp
  ring

/-- Proposition 7.2 for one member of the selected dyadic frequency
block.  In particular, the `N³` from Proposition 7.1 and the physical
smoothing width combine to the source coefficient `T^η N²/M`. -/
theorem gmCubicS3Mode_prop7_2
    (cutoff : GMSmoothCutoff) (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ {T : ℝ} {N H r s : ℕ} {W : Finset ℝ}
      {m : ℤ × (ℤ × ℤ)},
      1 ≤ T → 0 < N → (N : ℝ) ≤ T →
      IsSeparated 1 W → InBaseInterval T W →
      m ∈ gmCubicDyadicFrequencyBlock H r s →
      ‖gmCubicS3Mode cutoff N W m‖ ≤
        C * T ^ η * (N : ℝ) ^ 2 / (2 ^ s : ℕ) *
            gmCubicSmoothedModeIntegral η T N (2 ^ s) W m +
          C / T ^ 200 := by
  obtain ⟨C₀, hC₀, hMode⟩ := gmCubicS3Mode_prop7_1 cutoff η hη
  let C := 4 * C₀
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro T N H r s W m hT hN hNT hSep hBase hm
  have hmBlock := mem_gmCubicDyadicFrequencyBlock.mp hm
  have hmOrdered := mem_gmCubicBalancedOrderedFrequencyBox.mp hmBlock.1
  have hmNonzero := mem_gmCubicOrderedFrequencyBox.mp hmOrdered.1
  have hmNZ := mem_gmCubicNonzeroFrequencyBox.mp hmNonzero.1
  have hM : 0 < 2 ^ s := pow_pos (by omega : 0 < (2 : ℕ)) _
  have hMleNat : 2 ^ s ≤ m.2.1.natAbs := hmBlock.2.2.2.1
  have hMle : ((2 ^ s : ℕ) : ℝ) ≤ |(m.2.1 : ℝ)| := by
    rw [show |(m.2.1 : ℝ)| = (m.2.1.natAbs : ℝ) by
      simp only [Nat.cast_natAbs, Int.cast_abs]]
    exact_mod_cast hMleNat
  have hMass := gmCubicCancellationMass_le_smoothedModeIntegral
    (η := η) W (lt_of_lt_of_le zero_lt_one hT) hN hM hmNZ.2.2.1 hMle
  have hModeBound := hMode hT hN hNT hSep hBase
    hmNZ.2.1 hmNZ.2.2.1 hmNZ.2.2.2
  have hMassNonneg := gmCubicCancellationMass_nonneg η T N W m
  have hIntegralNonneg := gmCubicSmoothedModeIntegral_nonneg
    η T N (2 ^ s) W m
  have hScaleNonneg :
      0 ≤ 2 / gmCubicSmoothingScale η T N (2 ^ s) := by
    exact div_nonneg (by norm_num)
      (gmCubicSmoothingScale_pos
        (lt_of_lt_of_le zero_lt_one hT) hN hM).le
  calc
    ‖gmCubicS3Mode cutoff N W m‖ ≤
        C₀ * (N : ℝ) ^ 3 * gmCubicCancellationMass η T N W m +
          C₀ / T ^ 200 := hModeBound
    _ ≤ C₀ * (N : ℝ) ^ 3 *
          ((2 / gmCubicSmoothingScale η T N (2 ^ s)) *
            gmCubicSmoothedModeIntegral η T N (2 ^ s) W m) +
          C₀ / T ^ 200 := by
      gcongr
    _ = C * T ^ η * (N : ℝ) ^ 2 / (2 ^ s : ℕ) *
          gmCubicSmoothedModeIntegral η T N (2 ^ s) W m +
          C₀ / T ^ 200 := by
      rw [two_div_gmCubicSmoothingScale
        (lt_of_lt_of_le zero_lt_one hT) hN hM]
      dsimp only [C]
      have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
      have hMreal : ((2 ^ s : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
      field_simp
    _ ≤ C * T ^ η * (N : ℝ) ^ 2 / (2 ^ s : ℕ) *
          gmCubicSmoothedModeIntegral η T N (2 ^ s) W m +
          C / T ^ 200 := by
      exact add_le_add le_rfl
        (div_le_div_of_nonneg_right
          (le_mul_of_one_le_left hC₀.le (by norm_num : (1 : ℝ) ≤ 4))
          (by positivity))

theorem card_gmCubicDyadicFrequencyBlock_le
    (H r s : ℕ) :
    (gmCubicDyadicFrequencyBlock H r s).card ≤ (2 * H + 1) ^ 3 := by
  calc
    (gmCubicDyadicFrequencyBlock H r s).card ≤
        (gmCubicBalancedOrderedFrequencyBox H).card := Finset.card_filter_le _ _
    _ ≤ (gmCubicOrderedFrequencyBox H).card := Finset.card_filter_le _ _
    _ ≤ (gmCubicNonzeroFrequencyBox H).card := Finset.card_filter_le _ _
    _ ≤ (gmCubicFrequencyBox H).card := Finset.card_filter_le _ _
    _ = (2 * H + 1) ^ 3 := card_gmCubicFrequencyBox H

theorem card_gmCubicDyadicFrequencyBlock_sourceRadius_le
    {η T : ℝ} {N r s : ℕ} (hT : 1 ≤ T) (hη : 0 ≤ η)
    (hηupper : η ≤ 2 / 3) (hN : 0 < N) :
    ((gmCubicDyadicFrequencyBlock
      (gmCubicFrequencyRadius η T N) r s).card : ℝ) ≤ 125 * T ^ 5 := by
  let H := gmCubicFrequencyRadius η T N
  have hcardNat := card_gmCubicDyadicFrequencyBlock_le H r s
  have hcard :
      ((gmCubicDyadicFrequencyBlock H r s).card : ℝ) ≤
        (((2 * H + 1) ^ 3 : ℕ) : ℝ) := by exact_mod_cast hcardNat
  have hradius := two_frequencyRadius_add_one_le_five_rpow
    (T := T) (N := N) hT hη hN
  have hpow : (((2 * H + 1) ^ 3 : ℕ) : ℝ) ≤
      (5 * T ^ (1 + η)) ^ 3 := by
    norm_num only [Nat.cast_pow]
    exact pow_le_pow_left₀ (by positivity) hradius 3
  have hexp : 3 * (1 + η) ≤ 5 := by linarith
  have hscale : (T ^ (1 + η)) ^ 3 ≤ T ^ (5 : ℕ) := by
    calc
      (T ^ (1 + η)) ^ 3 = T ^ ((1 + η) * (3 : ℝ)) := by
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul (by positivity : 0 ≤ T)]
        norm_num
      _ ≤ T ^ (5 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hT (by nlinarith)
      _ = T ^ (5 : ℕ) := by norm_num [Real.rpow_natCast]
  calc
    ((gmCubicDyadicFrequencyBlock H r s).card : ℝ) ≤
        (((2 * H + 1) ^ 3 : ℕ) : ℝ) := hcard
    _ ≤ (5 * T ^ (1 + η)) ^ 3 := hpow
    _ = 125 * (T ^ (1 + η)) ^ 3 := by ring
    _ ≤ 125 * T ^ 5 := by gcongr

theorem gmCubicDyadicLogFactor_le
    {η T : ℝ} {N : ℕ} (hT : 1 ≤ T)
    (hηupper : η ≤ 2 / 3) (hN : 0 < N) :
    (((Nat.log 2 (gmCubicFrequencyRadius η T N) + 1 : ℕ) : ℝ)) ≤
      3 * T ^ 2 := by
  let H := gmCubicFrequencyRadius η T N
  have hlogNat : Nat.log 2 H + 1 ≤ H + 1 :=
    Nat.add_le_add_right (Nat.log_le_self 2 H) 1
  have hlogCast : (((Nat.log 2 H + 1 : ℕ) : ℝ)) ≤ (H : ℝ) + 1 := by
    exact_mod_cast hlogNat
  have hradius := gmCubicFrequencyRadius_cast_lt_rpow_add_one
    (η := η) (T := T) (N := N) (lt_of_lt_of_le zero_lt_one hT) hN
  have hpow : T ^ (1 + η) ≤ T ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hT (by linarith)
  have hTtwo : T ^ (2 : ℝ) = T ^ (2 : ℕ) := by
    norm_num [Real.rpow_natCast]
  calc
    (((Nat.log 2 H + 1 : ℕ) : ℝ)) ≤ (H : ℝ) + 1 := hlogCast
    _ ≤ T ^ (1 + η) + 2 := by linarith
    _ ≤ T ^ (2 : ℝ) + 2 := by linarith
    _ = T ^ 2 + 2 := by rw [hTtwo]
    _ ≤ 3 * T ^ 2 := by nlinarith [sq_nonneg (T - 1)]

/-- Proposition 7.2 with every dyadic and far-frequency loss still
displayed explicitly.  Later epsilon bookkeeping may absorb the binary
logarithm and the finite block error, but no asymptotic notation is hidden
in this source-facing statement. -/
theorem gmCubicS3_prop7_2_explicit
    (cutoff : GMSmoothCutoff) (η : ℝ) (hηpos : 0 < η)
    (hηupper : η ≤ 2 / 3) :
    ∃ K C : ℝ, 0 < K ∧ 0 < C ∧
      ∀ {T : ℝ} {N : ℕ} {W : Finset ℝ},
      1 ≤ T → 0 < N → (N : ℝ) ≤ T →
      T ^ (2 / 3 : ℝ) ≤ (N : ℝ) →
      IsSeparated 1 W → InBaseInterval T W →
      ∃ p ∈ gmCubicDyadicIndexPairs (gmCubicFrequencyRadius η T N),
        ‖gmCubicS3 cutoff N W‖ ≤
          6 * (((Nat.log 2 (gmCubicFrequencyRadius η T N) + 1 : ℕ) : ℝ)) ^ 2 *
            (C * T ^ η * (N : ℝ) ^ 2 / (2 ^ p.2 : ℕ) *
                (∑ m ∈ gmCubicDyadicFrequencyBlock
                  (gmCubicFrequencyRadius η T N) p.1 p.2,
                  gmCubicSmoothedModeIntegral η T N (2 ^ p.2) W m) +
              ((gmCubicDyadicFrequencyBlock
                (gmCubicFrequencyRadius η T N) p.1 p.2).card : ℝ) *
                (C / T ^ 200)) +
            K / T ^ 100 := by
  obtain ⟨K, hK, hselect⟩ :=
    norm_gmCubicS3_le_one_dyadic_frequency_block
      cutoff η hηpos hηupper
  obtain ⟨C, hC, hmode⟩ := gmCubicS3Mode_prop7_2 cutoff η hηpos
  refine ⟨K, C, hK, hC, ?_⟩
  intro T N W hT hN hNT hNlower hSep hBase
  obtain ⟨p, hp, hpbound⟩ :=
    hselect hT hN hNT hNlower hSep hBase
  refine ⟨p, hp, ?_⟩
  let B := gmCubicDyadicFrequencyBlock
    (gmCubicFrequencyRadius η T N) p.1 p.2
  have hsum :
      (∑ m ∈ B, ‖gmCubicS3Mode cutoff N W m‖) ≤
        ∑ m ∈ B,
          (C * T ^ η * (N : ℝ) ^ 2 / (2 ^ p.2 : ℕ) *
              gmCubicSmoothedModeIntegral η T N (2 ^ p.2) W m +
            C / T ^ 200) := by
    apply Finset.sum_le_sum
    intro m hm
    exact hmode hT hN hNT hSep hBase hm
  have hsumRewrite :
      (∑ m ∈ B,
          (C * T ^ η * (N : ℝ) ^ 2 / (2 ^ p.2 : ℕ) *
              gmCubicSmoothedModeIntegral η T N (2 ^ p.2) W m +
            C / T ^ 200)) =
        C * T ^ η * (N : ℝ) ^ 2 / (2 ^ p.2 : ℕ) *
            (∑ m ∈ B,
              gmCubicSmoothedModeIntegral η T N (2 ^ p.2) W m) +
          (B.card : ℝ) * (C / T ^ 200) := by
    rw [Finset.sum_add_distrib]
    rw [Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]
  calc
    ‖gmCubicS3 cutoff N W‖ ≤
        6 * (((Nat.log 2 (gmCubicFrequencyRadius η T N) + 1 : ℕ) : ℝ)) ^ 2 *
          (∑ m ∈ B, ‖gmCubicS3Mode cutoff N W m‖) + K / T ^ 100 :=
      hpbound
    _ ≤ 6 * (((Nat.log 2 (gmCubicFrequencyRadius η T N) + 1 : ℕ) : ℝ)) ^ 2 *
          (∑ m ∈ B,
            (C * T ^ η * (N : ℝ) ^ 2 / (2 ^ p.2 : ℕ) *
                gmCubicSmoothedModeIntegral η T N (2 ^ p.2) W m +
              C / T ^ 200)) + K / T ^ 100 := by
      gcongr
    _ = 6 * (((Nat.log 2 (gmCubicFrequencyRadius η T N) + 1 : ℕ) : ℝ)) ^ 2 *
          (C * T ^ η * (N : ℝ) ^ 2 / (2 ^ p.2 : ℕ) *
              (∑ m ∈ B,
                gmCubicSmoothedModeIntegral η T N (2 ^ p.2) W m) +
            (B.card : ℝ) * (C / T ^ 200)) + K / T ^ 100 := by
      rw [hsumRewrite]
    _ = _ := rfl

/-! ## Lemma 8.3 for the source smoother -/

theorem gmCubicLocalBump_eq_zero_of_two_le_abs
    {x : ℝ} (hx : 2 ≤ |x|) : gmCubicLocalBump x = 0 := by
  by_contra hne
  have hsupp : x / 2 ∈ Function.support dfiUnitRedundantBump := by
    simpa only [gmCubicLocalBump] using hne
  rw [dfiUnitRedundantBump.support_eq, Metric.mem_ball, Real.dist_eq] at hsupp
  simp only [sub_zero, show dfiUnitRedundantBump.rOut = (1 : ℝ) by rfl] at hsupp
  have habs : |x / 2| = |x| / 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [habs] at hsupp
  linarith

/-- The `gmCubicSmoothingSupport` definition used by the source-facing construction in `LargeValuesS3`. -/
def gmCubicSmoothingSupport (B v : ℝ) : Set ℝ :=
  Set.Icc (v - 2 / B) (v + 2 / B) ∩ Set.Icc (1 / 8 : ℝ) (33 / 8)

theorem measurableSet_gmCubicSmoothingSupport (B v : ℝ) :
    MeasurableSet (gmCubicSmoothingSupport B v) :=
  measurableSet_Icc.inter measurableSet_Icc

theorem gmCubicSmoothedRIntegrand_eq_zero_of_not_mem_support
    {η T : ℝ} {N M : ℕ} (W : Finset ℝ) (v : ℝ) {u : ℝ}
    (hB : 0 < gmCubicSmoothingScale η T N M)
    (hu : u ∉ gmCubicSmoothingSupport
      (gmCubicSmoothingScale η T N M) v) :
    gmCubicSmoothedRIntegrand η T N M W v u = 0 := by
  by_cases hratio : u ∈ Set.Icc (1 / 8 : ℝ) (33 / 8)
  · have hnotWidth : u ∉ Set.Icc
        (v - 2 / gmCubicSmoothingScale η T N M)
        (v + 2 / gmCubicSmoothingScale η T N M) := by
      intro hwidth
      exact hu ⟨hwidth, hratio⟩
    have habs : 2 ≤
        |gmCubicSmoothingScale η T N M * (v - u)| := by
      rw [abs_mul, abs_of_pos hB]
      rw [Set.mem_Icc] at hnotWidth
      have hwidth : 2 / gmCubicSmoothingScale η T N M ≤ |v - u| := by
        by_cases hleft :
            v - 2 / gmCubicSmoothingScale η T N M ≤ u
        · have hright :
              v + 2 / gmCubicSmoothingScale η T N M < u :=
            lt_of_not_ge fun huUpper => hnotWidth ⟨hleft, huUpper⟩
          have hdist : 2 / gmCubicSmoothingScale η T N M < -(v - u) := by
            linarith
          exact hdist.le.trans (neg_le_abs (v - u))
        · have hleft' : u <
              v - 2 / gmCubicSmoothingScale η T N M := lt_of_not_ge hleft
          have hdist : 2 / gmCubicSmoothingScale η T N M < v - u := by
            linarith
          exact hdist.le.trans (le_abs_self (v - u))
      have hmul := mul_le_mul_of_nonneg_left hwidth hB.le
      field_simp [hB.ne'] at hmul
      exact hmul
    unfold gmCubicSmoothedRIntegrand
    rw [gmCubicLocalBump_eq_zero_of_two_le_abs habs]
    ring
  · exact gmCubicSmoothedRIntegrand_eq_zero_of_not_mem_Icc W v hratio

theorem gmCubicSmoothedRSq_eq_setIntegral_support
    {η T : ℝ} {N M : ℕ} (W : Finset ℝ) (v : ℝ)
    (hB : 0 < gmCubicSmoothingScale η T N M) :
    gmCubicSmoothedRSq η T N M W v =
      ∫ u in gmCubicSmoothingSupport
        (gmCubicSmoothingScale η T N M) v,
        gmCubicSmoothedRIntegrand η T N M W v u := by
  unfold gmCubicSmoothedRSq
  rw [← MeasureTheory.integral_indicator
    (measurableSet_gmCubicSmoothingSupport _ _)]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with u
  by_cases hu : u ∈ gmCubicSmoothingSupport
      (gmCubicSmoothingScale η T N M) v
  · rw [Set.indicator_of_mem hu]
  · rw [Set.indicator_of_notMem hu,
      gmCubicSmoothedRIntegrand_eq_zero_of_not_mem_support W v hB hu]

theorem measureReal_gmCubicSmoothingSupport_le
    {B v : ℝ} (hB : 0 < B) :
    (volume (gmCubicSmoothingSupport B v)).toReal ≤ 4 / B := by
  have hsubset : gmCubicSmoothingSupport B v ⊆
      Set.Icc (v - 2 / B) (v + 2 / B) := inter_subset_left
  have hmeasure := measure_mono (μ := volume) hsubset
  have hfinite : volume (Set.Icc (v - 2 / B) (v + 2 / B)) ≠ (⊤ : ENNReal) :=
    measure_Icc_lt_top.ne
  have hreal := ENNReal.toReal_mono hfinite hmeasure
  calc
    (volume (gmCubicSmoothingSupport B v)).toReal ≤
        (volume (Set.Icc (v - 2 / B) (v + 2 / B))).toReal := hreal
    _ = 4 / B := by
      rw [Real.volume_Icc, ENNReal.toReal_ofReal]
      · ring
      · rw [show v + 2 / B - (v - 2 / B) = 4 / B by ring]
        positivity

theorem gmCubicSmoothedRSq_sq_le_localFourth
    {η T : ℝ} {N M : ℕ} (W : Finset ℝ) (v : ℝ)
    (hB : 0 < gmCubicSmoothingScale η T N M) :
    gmCubicSmoothedRSq η T N M W v ^ 2 ≤
      4 * gmCubicSmoothingScale η T N M *
        (∫ u in gmCubicSmoothingSupport
          (gmCubicSmoothingScale η T N M) v, ‖gmR W u‖ ^ 4) := by
  let B := gmCubicSmoothingScale η T N M
  let s := gmCubicSmoothingSupport B v
  let μ : Measure ℝ := volume.restrict s
  let f : ℝ → ℝ := fun u => ‖gmR W u‖ ^ 2
  have hsMeas : MeasurableSet s := measurableSet_gmCubicSmoothingSupport B v
  have hsSubset : s ⊆ Set.Icc (1 / 8 : ℝ) (33 / 8) := inter_subset_right
  have hsFinite : volume s < (⊤ : ENNReal) :=
    lt_of_le_of_lt (measure_mono hsSubset) measure_Icc_lt_top
  have hfMeas : Measurable f := (measurable_gmR W).norm.pow_const 2
  have hfInt : IntegrableOn f s := by
    apply IntegrableOn.of_bound hsFinite hfMeas.aestronglyMeasurable.restrict
      ((W.card : ℝ) ^ 2)
    filter_upwards with u
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_gmR_le_card_all W u) 2
  have hf2Int : IntegrableOn (fun u => f u ^ 2) s := by
    apply IntegrableOn.of_bound hsFinite
      (hfMeas.pow_const 2).aestronglyMeasurable.restrict
      ((W.card : ℝ) ^ 4)
    filter_upwards with u
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    dsimp only [f]
    nlinarith [pow_le_pow_left₀ (norm_nonneg (gmR W u))
      (norm_gmR_le_card_all W u) 2, sq_nonneg ((W.card : ℝ) ^ 2 - ‖gmR W u‖ ^ 2)]
  have hintegrand := integrable_gmCubicSmoothedRIntegrand W v hB.le
  have hRSqLe : gmCubicSmoothedRSq η T N M W v ≤ B * ∫ u in s, f u := by
    rw [gmCubicSmoothedRSq_eq_setIntegral_support W v hB]
    calc
      (∫ u in s, gmCubicSmoothedRIntegrand η T N M W v u) ≤
          ∫ u in s, B * f u := by
        apply MeasureTheory.integral_mono_ae hintegrand.integrableOn
          (hfInt.const_mul B)
        filter_upwards with u
        unfold gmCubicSmoothedRIntegrand f B
        have hlocal0 := gmCubicLocalBump_nonneg (gmCubicSmoothingScale η T N M * (v - u))
        have hratio0 := gmCubicRatioBump_nonneg u
        have hlocal1 := gmCubicLocalBump_le_one
          (gmCubicSmoothingScale η T N M * (v - u))
        have hratio1 := gmCubicRatioBump_le_one u
        calc
          gmCubicSmoothingScale η T N M *
              gmCubicLocalBump (gmCubicSmoothingScale η T N M * (v - u)) *
              gmCubicRatioBump u * ‖gmR W u‖ ^ 2 ≤
            gmCubicSmoothingScale η T N M * 1 * 1 * ‖gmR W u‖ ^ 2 := by
              gcongr
          _ = gmCubicSmoothingScale η T N M * ‖gmR W u‖ ^ 2 := by ring
      _ = B * ∫ u in s, f u := by rw [MeasureTheory.integral_const_mul]
  have hone2Int : Integrable (fun _u : ℝ => (1 : ℝ) ^ 2) μ := by
    change IntegrableOn (fun _u : ℝ => (1 : ℝ) ^ 2) s
    exact continuousOn_const.integrableOn_compact
      (isCompact_Icc.inter isCompact_Icc)
  have hf2Int' : Integrable (fun u => f u ^ 2) μ := hf2Int
  have honeMem : MemLp (fun _u : ℝ => (1 : ℝ))
      (ENNReal.ofReal (2 : ℝ)) μ := by
    have h : MemLp (fun _u : ℝ => (1 : ℝ)) 2 μ :=
      (memLp_two_iff_integrable_sq stronglyMeasurable_const.aestronglyMeasurable).2
        hone2Int
    simpa using h
  have hfMem : MemLp f (ENNReal.ofReal (2 : ℝ)) μ := by
    have h : MemLp f 2 μ :=
      (memLp_two_iff_integrable_sq hfMeas.aestronglyMeasurable).2 hf2Int'
    simpa using h
  have hpq : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hHolder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := μ) (f := fun _u : ℝ => (1 : ℝ)) (g := f) hpq
    (Filter.Eventually.of_forall fun _ => by norm_num)
    (Filter.Eventually.of_forall fun u => sq_nonneg ‖gmR W u‖)
    honeMem hfMem
  have hCS : (∫ u in s, f u) ≤
      Real.sqrt (volume s).toReal * Real.sqrt (∫ u in s, f u ^ 2) := by
    dsimp only [μ] at hHolder
    simpa only [one_mul, mul_one, one_pow, integral_const, smul_eq_mul,
      measureReal_def, Measure.restrict_apply_univ, Real.sqrt_eq_rpow,
      one_div, Real.rpow_two] using hHolder
  have hA0 : 0 ≤ ∫ u in s, f u := by
    apply MeasureTheory.integral_nonneg_of_ae
    exact Filter.Eventually.of_forall fun u => sq_nonneg ‖gmR W u‖
  have hD0 : 0 ≤ ∫ u in s, f u ^ 2 := by
    apply MeasureTheory.integral_nonneg_of_ae
    exact Filter.Eventually.of_forall fun u => sq_nonneg (f u)
  have hQ0 : 0 ≤ (volume s).toReal := ENNReal.toReal_nonneg
  have hCSsq : (∫ u in s, f u) ^ 2 ≤
      (volume s).toReal * (∫ u in s, f u ^ 2) := by
    have hqSq := Real.sq_sqrt hQ0
    have hdSq := Real.sq_sqrt hD0
    nlinarith [sq_nonneg
      (Real.sqrt (volume s).toReal * Real.sqrt (∫ u in s, f u ^ 2) -
        ∫ u in s, f u)]
  have hmeasure := measureReal_gmCubicSmoothingSupport_le (B := B) (v := v) hB
  have hB0 : 0 ≤ B := hB.le
  have hRSq0 := gmCubicSmoothedRSq_nonneg W v hB.le
  calc
    gmCubicSmoothedRSq η T N M W v ^ 2 ≤
        (B * ∫ u in s, f u) ^ 2 := by nlinarith
    _ = B ^ 2 * (∫ u in s, f u) ^ 2 := by ring
    _ ≤ B ^ 2 * ((volume s).toReal * ∫ u in s, f u ^ 2) := by
      gcongr
    _ ≤ B ^ 2 * ((4 / B) * ∫ u in s, f u ^ 2) := by
      gcongr
    _ = 4 * B * (∫ u in s, ‖gmR W u‖ ^ 4) := by
      dsimp only [f, s, B]
      field_simp [hB.ne']

/-- The `gmCubicSmoothingIncidence` definition used by the source-facing construction in `LargeValuesS3`. -/
def gmCubicSmoothingIncidence (B : ℝ) : Set (ℝ × ℝ) :=
  {p | p.2 ∈ gmCubicSmoothingSupport B p.1}

theorem measurableSet_gmCubicSmoothingIncidence (B : ℝ) :
    MeasurableSet (gmCubicSmoothingIncidence B) := by
  have h₁ : MeasurableSet {p : ℝ × ℝ | p.1 - 2 / B ≤ p.2} :=
    measurableSet_le
      (measurable_fst.sub (measurable_const : Measurable fun _ : ℝ × ℝ => 2 / B))
      measurable_snd
  have h₂ : MeasurableSet {p : ℝ × ℝ | p.2 ≤ p.1 + 2 / B} :=
    measurableSet_le measurable_snd
      (measurable_fst.add (measurable_const : Measurable fun _ : ℝ × ℝ => 2 / B))
  have h₃ : MeasurableSet {p : ℝ × ℝ | 1 / 8 ≤ p.2} :=
    measurableSet_le (measurable_const : Measurable fun _ : ℝ × ℝ => (1 / 8 : ℝ))
      measurable_snd
  have h₄ : MeasurableSet {p : ℝ × ℝ | p.2 ≤ 33 / 8} :=
    measurableSet_le measurable_snd
      (measurable_const : Measurable fun _ : ℝ × ℝ => (33 / 8 : ℝ))
  have h : MeasurableSet {p : ℝ × ℝ |
      (p.1 - 2 / B ≤ p.2 ∧ p.2 ≤ p.1 + 2 / B) ∧
        (1 / 8 ≤ p.2 ∧ p.2 ≤ 33 / 8)} := (h₁.inter h₂).inter (h₃.inter h₄)
  simpa [gmCubicSmoothingIncidence, gmCubicSmoothingSupport] using h

/-- The `gmCubicLocalFourthKernel` definition used by the source-facing construction in `LargeValuesS3`. -/
noncomputable def gmCubicLocalFourthKernel
    (B : ℝ) (W : Finset ℝ) (p : ℝ × ℝ) : ℝ :=
  (gmCubicSmoothingIncidence B).indicator (fun q => ‖gmR W q.2‖ ^ 4) p

theorem measurable_gmCubicLocalFourthKernel (B : ℝ) (W : Finset ℝ) :
    Measurable (gmCubicLocalFourthKernel B W) := by
  unfold gmCubicLocalFourthKernel
  exact (((measurable_gmR W).comp measurable_snd).norm.pow_const 4).indicator
    (measurableSet_gmCubicSmoothingIncidence B)

theorem integrable_gmCubicLocalFourthKernel
    {B : ℝ} (W : Finset ℝ) :
    Integrable (gmCubicLocalFourthKernel B W) (volume.prod volume) := by
  let Q : Set (ℝ × ℝ) :=
    Set.Icc (1 / 8 - 2 / B) (33 / 8 + 2 / B) ×ˢ
      Set.Icc (1 / 8 : ℝ) (33 / 8)
  let C : ℝ := (W.card : ℝ) ^ 4
  let g : ℝ × ℝ → ℝ := Q.indicator (fun _ => C)
  have hQCompact : IsCompact Q := isCompact_Icc.prod isCompact_Icc
  have hQMeas : MeasurableSet Q := measurableSet_Icc.prod measurableSet_Icc
  have hgOn : IntegrableOn (fun _ : ℝ × ℝ => C) Q (volume.prod volume) :=
    continuousOn_const.integrableOn_compact hQCompact
  have hg : Integrable g (volume.prod volume) :=
    hgOn.integrable_indicator hQMeas
  apply hg.mono' (measurable_gmCubicLocalFourthKernel B W).aestronglyMeasurable
  filter_upwards with p
  by_cases hp : p ∈ gmCubicSmoothingIncidence B
  · change p.2 ∈ gmCubicSmoothingSupport B p.1 at hp
    rcases hp with ⟨hwidth, hratio⟩
    have hp : p ∈ gmCubicSmoothingIncidence B := ⟨hwidth, hratio⟩
    have hpQ : p ∈ Q := by
      refine ⟨?_, hratio⟩
      constructor
      · linarith [hwidth.2, hratio.1]
      · linarith [hwidth.1, hratio.2]
    rw [show gmCubicLocalFourthKernel B W p = ‖gmR W p.2‖ ^ 4 by
      simp [gmCubicLocalFourthKernel, hp]]
    rw [show g p = C by simp [g, hpQ]]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ ‖gmR W p.2‖ ^ 4)]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_gmR_le_card_all W p.2) 4
  · rw [show gmCubicLocalFourthKernel B W p = 0 by
      simp [gmCubicLocalFourthKernel, hp]]
    by_cases hpQ : p ∈ Q <;> simp [g, hpQ, C]

theorem integral_gmCubicLocalFourthKernel_right
    {B : ℝ} (W : Finset ℝ) (v : ℝ) :
    (∫ u : ℝ, gmCubicLocalFourthKernel B W (v, u)) =
      ∫ u in gmCubicSmoothingSupport B v, ‖gmR W u‖ ^ 4 := by
  rw [← MeasureTheory.integral_indicator
    (measurableSet_gmCubicSmoothingSupport B v)]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with u
  by_cases hu : u ∈ gmCubicSmoothingSupport B v <;>
    simp [gmCubicLocalFourthKernel, gmCubicSmoothingIncidence, hu]

theorem integral_gmCubicLocalFourthKernel_left
    {B : ℝ} (W : Finset ℝ) (hB : 0 < B) (u : ℝ) :
    (∫ v : ℝ, gmCubicLocalFourthKernel B W (v, u)) =
      if u ∈ Set.Icc (1 / 8 : ℝ) (33 / 8) then
        (4 / B) * ‖gmR W u‖ ^ 4 else 0 := by
  by_cases hu : u ∈ Set.Icc (1 / 8 : ℝ) (33 / 8)
  · rw [if_pos hu]
    let J := Set.Icc (u - 2 / B) (u + 2 / B)
    have hpoint : ∀ v : ℝ,
        gmCubicLocalFourthKernel B W (v, u) =
          J.indicator (fun _ => ‖gmR W u‖ ^ 4) v := by
      intro v
      have hequiv : u ∈ gmCubicSmoothingSupport B v ↔ v ∈ J := by
        unfold gmCubicSmoothingSupport J
        simp only [Set.mem_inter_iff, Set.mem_Icc]
        constructor
        · intro h
          constructor <;> linarith [h.1.1, h.1.2]
        · intro h
          exact ⟨⟨by linarith [h.1], by linarith [h.2]⟩, hu⟩
      by_cases hv : v ∈ J
      · simp [gmCubicLocalFourthKernel, gmCubicSmoothingIncidence,
          hv, hequiv.mpr hv]
      · have hn : (v, u) ∉ gmCubicSmoothingIncidence B := by
          intro h
          exact hv (hequiv.mp h)
        rw [show gmCubicLocalFourthKernel B W (v, u) = 0 by
          simp [gmCubicLocalFourthKernel, hn]]
        simp [hv]
    calc
      (∫ v : ℝ, gmCubicLocalFourthKernel B W (v, u)) =
          ∫ v : ℝ, J.indicator (fun _ => ‖gmR W u‖ ^ 4) v := by
            apply MeasureTheory.integral_congr_ae
            exact Filter.Eventually.of_forall hpoint
      _ = ∫ v in J, ‖gmR W u‖ ^ 4 := by
            rw [MeasureTheory.integral_indicator measurableSet_Icc]
      _ = (4 / B) * ‖gmR W u‖ ^ 4 := by
            have hlen : (volume J).toReal = 4 / B := by
              simp only [J, Real.volume_Icc]
              rw [show u + 2 / B - (u - 2 / B) = 4 / B by ring]
              have h4B : 0 ≤ 4 / B := by positivity
              simp [h4B]
            rw [MeasureTheory.setIntegral_const]
            rw [measureReal_def, hlen, smul_eq_mul]
  · rw [if_neg hu]
    apply MeasureTheory.integral_eq_zero_of_ae
    filter_upwards with v
    have hn : (v, u) ∉ gmCubicSmoothingIncidence B := by
      intro h
      exact hu h.2
    simp [gmCubicLocalFourthKernel, hn]

theorem integral_localFourth_eq
    {B : ℝ} (W : Finset ℝ) (hB : 0 < B) :
    (∫ v : ℝ, ∫ u in gmCubicSmoothingSupport B v, ‖gmR W u‖ ^ 4) =
      (4 / B) * ∫ u in Set.Icc (1 / 8 : ℝ) (33 / 8), ‖gmR W u‖ ^ 4 := by
  have hInt := integrable_gmCubicLocalFourthKernel (B := B) W
  calc
    (∫ v : ℝ, ∫ u in gmCubicSmoothingSupport B v, ‖gmR W u‖ ^ 4) =
        ∫ v : ℝ, ∫ u : ℝ, gmCubicLocalFourthKernel B W (v, u) := by
          apply MeasureTheory.integral_congr_ae
          exact Filter.Eventually.of_forall fun v =>
            (integral_gmCubicLocalFourthKernel_right W v).symm
    _ = ∫ u : ℝ, ∫ v : ℝ, gmCubicLocalFourthKernel B W (v, u) :=
      MeasureTheory.integral_integral_swap
        (f := fun v u => gmCubicLocalFourthKernel B W (v, u)) hInt
    _ = ∫ u : ℝ, (Set.Icc (1 / 8 : ℝ) (33 / 8)).indicator
          (fun x => (4 / B) * ‖gmR W x‖ ^ 4) u := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with u
      rw [integral_gmCubicLocalFourthKernel_left W hB u]
      by_cases hu : u ∈ Set.Icc (1 / 8 : ℝ) (33 / 8)
      · rw [if_pos hu, Set.indicator_of_mem hu]
      · rw [if_neg hu, Set.indicator_of_notMem hu]
    _ = ∫ u in Set.Icc (1 / 8 : ℝ) (33 / 8),
          (4 / B) * ‖gmR W u‖ ^ 4 := by
      rw [MeasureTheory.integral_indicator measurableSet_Icc]
    _ = (4 / B) * ∫ u in Set.Icc (1 / 8 : ℝ) (33 / 8),
          ‖gmR W u‖ ^ 4 := by rw [MeasureTheory.integral_const_mul]

/-- The global fourth moment of the source smoother is controlled by the
unweighted multiplicative fourth moment.  This is the exact Fubini--Cauchy
Schwarz content of Guth--Maynard Lemma 8.3 before converting `u` to
logarithmic coordinates. -/
theorem integral_gmCubicSmoothedR_fourth_le
    {η T : ℝ} {N M : ℕ} (W : Finset ℝ)
    (hB : 0 < gmCubicSmoothingScale η T N M) :
    (∫ v : ℝ, gmCubicSmoothedR η T N M W v ^ 4) ≤
      16 * ∫ u in Set.Icc (1 / 8 : ℝ) (33 / 8), ‖gmR W u‖ ^ 4 := by
  let B := gmCubicSmoothingScale η T N M
  let F : ℝ → ℝ := fun v =>
    ∫ u in gmCubicSmoothingSupport B v, ‖gmR W u‖ ^ 4
  have hkernel := integrable_gmCubicLocalFourthKernel (B := B) W
  have hFInt : Integrable F := by
    have hiter := hkernel.integral_prod_left
    apply hiter.congr
    filter_upwards with v
    exact integral_gmCubicLocalFourthKernel_right (B := B) W v
  have hmajorInt : Integrable (fun v => 4 * B * F v) := hFInt.const_mul (4 * B)
  have hnonneg : ∀ᵐ v : ℝ, 0 ≤ gmCubicSmoothedR η T N M W v ^ 4 :=
    Filter.Eventually.of_forall fun v => by positivity
  have hpoint : ∀ᵐ v : ℝ,
      gmCubicSmoothedR η T N M W v ^ 4 ≤ 4 * B * F v := by
    filter_upwards with v
    rw [show gmCubicSmoothedR η T N M W v ^ 4 =
        (gmCubicSmoothedR η T N M W v ^ 2) ^ 2 by ring]
    rw [gmCubicSmoothedR_sq W v hB.le]
    exact gmCubicSmoothedRSq_sq_le_localFourth W v hB
  have hmono := MeasureTheory.integral_mono_of_nonneg hnonneg hmajorInt hpoint
  calc
    (∫ v : ℝ, gmCubicSmoothedR η T N M W v ^ 4) ≤
        ∫ v : ℝ, 4 * B * F v := hmono
    _ = 4 * B * ∫ v : ℝ, F v := by rw [MeasureTheory.integral_const_mul]
    _ = 4 * B * ((4 / B) *
          ∫ u in Set.Icc (1 / 8 : ℝ) (33 / 8), ‖gmR W u‖ ^ 4) := by
      rw [integral_localFourth_eq W hB]
    _ = 16 * ∫ u in Set.Icc (1 / 8 : ℝ) (33 / 8), ‖gmR W u‖ ^ 4 := by
      dsimp only [B]
      field_simp [hB.ne']
      ring

theorem gmR_exp_eq_gmRPhase (W : Finset ℝ) (x : ℝ) :
    gmR W (Real.exp x) = gmRPhase W x := by
  rw [gmR_eq_gmRPhase_log (Real.exp_ne_zero x)]
  simp

/-- Exact logarithmic change of variables on the fixed ratio support of
the Proposition 7.2 smoother. -/
theorem setIntegral_norm_gmR_fourth_eq_logWeighted (W : Finset ℝ) :
    (∫ u in Set.Icc (1 / 8 : ℝ) (33 / 8), ‖gmR W u‖ ^ 4) =
      ∫ x in Real.log (1 / 8 : ℝ)..Real.log (33 / 8 : ℝ),
        ‖gmRPhase W x‖ ^ 4 * Real.exp x := by
  let a : ℝ := Real.log (1 / 8 : ℝ)
  let b : ℝ := Real.log (33 / 8 : ℝ)
  let g : ℝ → ℝ := fun u => ‖gmR W u‖ ^ 4
  have ha0 : (0 : ℝ) < 1 / 8 := by norm_num
  have hb0 : (0 : ℝ) < 33 / 8 := by norm_num
  have hab : a ≤ b := by
    dsimp only [a, b]
    exact Real.strictMonoOn_log.monotoneOn (Set.mem_Ioi.mpr ha0)
      (Set.mem_Ioi.mpr hb0) (by norm_num)
  have hgCont : ContinuousOn g (Real.exp '' Set.uIcc a b) := by
    rintro u ⟨x, hx, rfl⟩
    exact ((continuousAt_gmR W (Real.exp_ne_zero x)).norm.pow 4).continuousWithinAt
  have hsub := intervalIntegral.integral_comp_mul_deriv'
    (a := a) (b := b) (f := Real.exp) (f' := Real.exp) (g := g)
    (fun x _ => Real.hasDerivAt_exp x) Real.continuous_exp.continuousOn hgCont
  have hsub' :
      (∫ x in a..b, ‖gmRPhase W x‖ ^ 4 * Real.exp x) =
        ∫ u in (1 / 8 : ℝ)..(33 / 8 : ℝ), ‖gmR W u‖ ^ 4 := by
    calc
      (∫ x in a..b, ‖gmRPhase W x‖ ^ 4 * Real.exp x) =
          ∫ x in a..b, (g ∘ Real.exp) x * Real.exp x := by
        apply intervalIntegral.integral_congr
        intro x hx
        simp only [Function.comp_apply, g, gmR_exp_eq_gmRPhase]
      _ = ∫ u in Real.exp a..Real.exp b, g u := hsub
      _ = ∫ u in (1 / 8 : ℝ)..(33 / 8 : ℝ), ‖gmR W u‖ ^ 4 := by
        dsimp only [a, b, g]
        rw [Real.exp_log ha0, Real.exp_log hb0]
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (1 / 8 : ℝ) ≤ 33 / 8)]
  simpa only [a, b] using hsub'.symm

/-- Guth--Maynard Lemma 8.3 on the multiplicative interval used by the
source smoother, with its logarithmic loss absorbed into `T^ε`. -/
theorem setIntegral_norm_gmR_fourth_le_energy_epsilon
    {ε T : ℝ} {W : Finset ℝ} (hε : 0 < ε) (hT : 1 ≤ T)
    (hW : InBaseInterval T W) :
    (∫ u in Set.Icc (1 / 8 : ℝ) (33 / 8), ‖gmR W u‖ ^ 4) ≤
      (33 / 8) *
        (4 * |Real.log (33 / 8 : ℝ) - Real.log (1 / 8 : ℝ)| +
          8 * (1 + ε⁻¹) * 3 ^ ε) *
        T ^ ε * (ApproxAddEnergy 1 W : ℝ) := by
  let a : ℝ := Real.log (1 / 8 : ℝ)
  let b : ℝ := Real.log (33 / 8 : ℝ)
  let q : ℝ → ℝ := fun x => ‖gmRPhase W x‖ ^ 4
  have hb0 : (0 : ℝ) < 33 / 8 := by norm_num
  have hab : a ≤ b := by
    dsimp only [a, b]
    exact Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr (by norm_num : (0 : ℝ) < 1 / 8))
      (Set.mem_Ioi.mpr hb0) (by norm_num)
  have hqCont : Continuous q := continuous_norm_gmRPhase_pow W 4
  have hfInt : IntervalIntegrable (fun x => q x * Real.exp x) volume a b :=
    (hqCont.mul Real.continuous_exp).intervalIntegrable a b
  have hgInt : IntervalIntegrable (fun x => (33 / 8 : ℝ) * q x) volume a b :=
    (continuous_const.mul hqCont).intervalIntegrable a b
  have hweighted :
      (∫ x in a..b, q x * Real.exp x) ≤
        (33 / 8 : ℝ) * ∫ x in a..b, q x := by
    calc
      (∫ x in a..b, q x * Real.exp x) ≤
          ∫ x in a..b, (33 / 8 : ℝ) * q x := by
        apply intervalIntegral.integral_mono_on hab hfInt hgInt
        intro x hx
        have hexp : Real.exp x ≤ (33 / 8 : ℝ) := by
          rw [← Real.exp_log hb0]
          exact Real.exp_le_exp.mpr hx.2
        have hq0 : 0 ≤ q x := by positivity
        nlinarith
      _ = (33 / 8 : ℝ) * ∫ x in a..b, q x := by
        rw [intervalIntegral.integral_const_mul]
  have henergy := intervalIntegral_norm_gmRPhase_fourth_le_energy_epsilon
    hε hT hW a b hab
  rw [setIntegral_norm_gmR_fourth_eq_logWeighted W]
  change (∫ x in a..b, q x * Real.exp x) ≤ _
  calc
    (∫ x in a..b, q x * Real.exp x) ≤
        (33 / 8 : ℝ) * ∫ x in a..b, q x := hweighted
    _ ≤ (33 / 8 : ℝ) *
        ((4 * |b - a| + 8 * (1 + ε⁻¹) * 3 ^ ε) *
          T ^ ε * (ApproxAddEnergy 1 W : ℝ)) := by
      gcongr
    _ = _ := by
      dsimp only [a, b, q]
      ring

theorem integral_gmCubicSmoothedR_fourth_le_energy_epsilon
    {ε η T : ℝ} {N M : ℕ} {W : Finset ℝ}
    (hε : 0 < ε) (hT : 1 ≤ T) (hW : InBaseInterval T W)
    (hB : 0 < gmCubicSmoothingScale η T N M) :
    (∫ v : ℝ, gmCubicSmoothedR η T N M W v ^ 4) ≤
      66 *
        (4 * |Real.log (33 / 8 : ℝ) - Real.log (1 / 8 : ℝ)| +
          8 * (1 + ε⁻¹) * 3 ^ ε) *
        T ^ ε * (ApproxAddEnergy 1 W : ℝ) := by
  have hsmooth := integral_gmCubicSmoothedR_fourth_le W hB
  have henergy := setIntegral_norm_gmR_fourth_le_energy_epsilon hε hT hW
  calc
    (∫ v : ℝ, gmCubicSmoothedR η T N M W v ^ 4) ≤
        16 * ∫ u in Set.Icc (1 / 8 : ℝ) (33 / 8), ‖gmR W u‖ ^ 4 := hsmooth
    _ ≤ 16 * ((33 / 8) *
        (4 * |Real.log (33 / 8 : ℝ) - Real.log (1 / 8 : ℝ)| +
          8 * (1 + ε⁻¹) * 3 ^ ε) *
        T ^ ε * (ApproxAddEnergy 1 W : ℝ)) := by
      gcongr
    _ = _ := by ring

/-- The `L²-L⁴-L⁴` Hölder inequality in the precise nested-square-root
form used in Guth--Maynard Proposition 8.1. -/
theorem integral_triple_le_L2_L4_L4
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {A B C : α → ℝ}
    (hA0 : 0 ≤ᵐ[μ] A) (hB0 : 0 ≤ᵐ[μ] B) (hC0 : 0 ≤ᵐ[μ] C)
    (hA2 : MemLp A (ENNReal.ofReal 2) μ)
    (hB4 : MemLp B (ENNReal.ofReal 4) μ)
    (hC4 : MemLp C (ENNReal.ofReal 4) μ) :
    (∫ x, A x * B x * C x ∂μ) ≤
      (∫ x, A x ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) *
        (((∫ x, B x ^ (4 : ℝ) ∂μ) ^ (1 / (2 : ℝ))) *
          ((∫ x, C x ^ (4 : ℝ) ∂μ) ^ (1 / (2 : ℝ)))) ^
            (1 / (2 : ℝ)) := by
  have hpq : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hBC0 : 0 ≤ᵐ[μ] (fun x => B x * C x) := by
    filter_upwards [hB0, hC0] with x hxB hxC
    exact mul_nonneg hxB hxC
  have h442 : (4 : ℝ).HolderTriple 4 2 := by
    rw [Real.holderTriple_iff]
    norm_num
  letI : ENNReal.HolderTriple (ENNReal.ofReal 4) (ENNReal.ofReal 4)
      (ENNReal.ofReal 2) := h442.ennrealOfReal
  have hBC2 : MemLp (fun x => B x * C x) (ENNReal.ofReal 2) μ := by
    have h := hC4.mul' (r := ENNReal.ofReal 2) hB4
    simpa using h
  have hfirst := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    hA0 hBC0 hA2 hBC2
  have hBsq0 : 0 ≤ᵐ[μ] (fun x => B x ^ 2) :=
    Filter.Eventually.of_forall fun x => sq_nonneg (B x)
  have hCsq0 : 0 ≤ᵐ[μ] (fun x => C x ^ 2) :=
    Filter.Eventually.of_forall fun x => sq_nonneg (C x)
  have hBsq2 : MemLp (fun x => B x ^ 2) (ENNReal.ofReal 2) μ := by
    have h := hB4.mul' (r := ENNReal.ofReal 2) hB4
    simpa [pow_two] using h
  have hCsq2 : MemLp (fun x => C x ^ 2) (ENNReal.ofReal 2) μ := by
    have h := hC4.mul' (r := ENNReal.ofReal 2) hC4
    simpa [pow_two] using h
  have hsecond := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    hBsq0 hCsq0 hBsq2 hCsq2
  have hrepack :
      (∫ x, (B x * C x) ^ (2 : ℝ) ∂μ) =
        ∫ x, (B x ^ 2) * (C x ^ 2) ∂μ := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    norm_num [Real.rpow_two]
    ring
  have hbase :
      (∫ x, (B x * C x) ^ (2 : ℝ) ∂μ) ≤
        ((∫ x, B x ^ (4 : ℝ) ∂μ) ^ (1 / (2 : ℝ))) *
          ((∫ x, C x ^ (4 : ℝ) ∂μ) ^ (1 / (2 : ℝ))) := by
    calc
      (∫ x, (B x * C x) ^ (2 : ℝ) ∂μ) =
          ∫ x, (B x ^ 2) * (C x ^ 2) ∂μ := hrepack
      _ ≤ ((∫ x, (B x ^ 2) ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ))) *
          ((∫ x, (C x ^ 2) ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ))) := hsecond
      _ = ((∫ x, B x ^ (4 : ℝ) ∂μ) ^ (1 / (2 : ℝ))) *
          ((∫ x, C x ^ (4 : ℝ) ∂μ) ^ (1 / (2 : ℝ))) := by
        congr 1
        · congr 1
          apply MeasureTheory.integral_congr_ae
          filter_upwards with x
          norm_num [Real.rpow_two]
          ring
        · congr 1
          apply MeasureTheory.integral_congr_ae
          filter_upwards with x
          norm_num [Real.rpow_two]
          ring
  have hbase0 : 0 ≤ ∫ x, (B x * C x) ^ (2 : ℝ) ∂μ := by
    apply integral_nonneg_of_ae
    filter_upwards [hBC0] with x hx
    exact Real.rpow_nonneg hx 2
  have hpow := Real.rpow_le_rpow hbase0 hbase (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hAint0 : 0 ≤ ∫ x, A x ^ (2 : ℝ) ∂μ := by
    apply integral_nonneg_of_ae
    filter_upwards [hA0] with x hx
    exact Real.rpow_nonneg hx 2
  calc
    (∫ x, A x * B x * C x ∂μ) = ∫ x, A x * (B x * C x) ∂μ := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      ring
    _ ≤ (∫ x, A x ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) *
        (∫ x, (B x * C x) ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := hfirst
    _ ≤ (∫ x, A x ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) *
        (((∫ x, B x ^ (4 : ℝ) ∂μ) ^ (1 / (2 : ℝ))) *
          ((∫ x, C x ^ (4 : ℝ) ∂μ) ^ (1 / (2 : ℝ)))) ^
            (1 / (2 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left hpow
      exact Real.rpow_nonneg hAint0 _

/-- Guth--Maynard Lemma 8.2 before epsilon absorption: the second moment
on any fixed additive interval is a diagonal length term plus one harmonic
row sum for each separated ordinate. -/
theorem intervalIntegral_norm_gmRPhase_sq_le_harmonic
    {T : ℝ} {W : Finset ℝ} (hT : 1 ≤ T)
    (hSep : IsSeparated 1 W) (hBase : InBaseInterval T W)
    (a b : ℝ) (hab : a ≤ b) :
    (∫ x in a..b, ‖gmRPhase W x‖ ^ 2) ≤
      (W.card : ℝ) * |b - a| +
        4 * (W.card : ℝ) * (((harmonic ⌈T⌉₊ : ℚ) : ℝ)) := by
  let K : ℕ := ⌈T⌉₊
  have hKpos : 0 < K := by
    have hTK : T ≤ (K : ℝ) := Nat.le_ceil T
    exact_mod_cast (lt_of_lt_of_le (by linarith : (0 : ℝ) < 1) (hT.trans hTK))
  have hnonneg : 0 ≤ ∫ x in a..b, ‖gmRPhase W x‖ ^ 2 :=
    intervalIntegral.integral_nonneg hab fun x hx => sq_nonneg _
  have hexpand := ofReal_intervalIntegral_norm_gmRPhase_sq W a b
  have hnorm : (∫ x in a..b, ‖gmRPhase W x‖ ^ 2) =
      ‖∑ t ∈ W, ∑ u ∈ W, gmPhaseIntervalKernel a b (t - u)‖ := by
    rw [← hexpand]
    simp [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  have hrow : ∀ t ∈ W,
      (∑ u ∈ W, ‖gmPhaseIntervalKernel a b (t - u)‖) ≤
        |b - a| + 4 * (((harmonic K : ℚ) : ℝ)) := by
    intro t ht
    let S := {u ∈ W | u ≠ t}
    have hNear : {u ∈ W | u ≠ t ∧ |u - t| ≤ (K : ℝ)} = S := by
      ext u
      simp only [Finset.mem_filter, S]
      constructor
      · rintro ⟨hu, hut, hdist⟩
        exact ⟨hu, hut⟩
      · rintro ⟨hu, hut⟩
        refine ⟨hu, hut, ?_⟩
        have huI := hBase u hu
        have htI := hBase t ht
        have hdist : |u - t| ≤ T := by
          rw [abs_le]
          constructor <;> linarith [huI.1, huI.2, htI.1, htI.2]
        exact hdist.trans (Nat.le_ceil T)
    have hinv : (∑ u ∈ S, 1 / |u - t|) ≤
        2 * (((harmonic K : ℚ) : ℝ)) := by
      rw [← hNear]
      exact sum_inv_distance_near_le_harmonic K W t hSep ht
    calc
      (∑ u ∈ W, ‖gmPhaseIntervalKernel a b (t - u)‖) ≤
          ∑ u ∈ W, if u = t then |b - a| else 2 / |u - t| := by
        apply Finset.sum_le_sum
        intro u hu
        by_cases hut : u = t
        · subst u
          simp only [sub_self, if_pos]
          exact norm_gmPhaseIntervalKernel_le_length a b 0
        · rw [if_neg hut]
          have htu : t - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hut)
          simpa only [abs_sub_comm] using
            (norm_gmPhaseIntervalKernel_le_two_div (a := a) (b := b) htu)
      _ = |b - a| + 2 * (∑ u ∈ S, 1 / |u - t|) := by
        have hsplit :
            (∑ u ∈ W, if u = t then |b - a| else 2 / |u - t|) =
              (∑ u ∈ W, if u = t then |b - a| else 0) +
                ∑ u ∈ W, if u ≠ t then 2 / |u - t| else 0 := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro u hu
          by_cases hut : u = t <;> simp [hut]
        rw [hsplit, Finset.sum_ite_eq', if_pos ht]
        have hfilter :
            (∑ u ∈ W, if u ≠ t then 2 / |u - t| else 0) =
              ∑ u ∈ S, 2 / |u - t| := by
          rw [← Finset.sum_filter]
        rw [hfilter]
        simp_rw [div_eq_mul_inv, ← Finset.mul_sum]
        simp
      _ ≤ |b - a| + 2 * (2 * (((harmonic K : ℚ) : ℝ))) := by
        gcongr
      _ = |b - a| + 4 * (((harmonic K : ℚ) : ℝ)) := by ring
  rw [hnorm]
  calc
    ‖∑ t ∈ W, ∑ u ∈ W, gmPhaseIntervalKernel a b (t - u)‖ ≤
        ∑ t ∈ W, ‖∑ u ∈ W, gmPhaseIntervalKernel a b (t - u)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ t ∈ W, ∑ u ∈ W, ‖gmPhaseIntervalKernel a b (t - u)‖ := by
      gcongr with t ht
      exact norm_sum_le _ _
    _ ≤ ∑ _t ∈ W, (|b - a| + 4 * (((harmonic K : ℚ) : ℝ))) := by
      gcongr with t ht
      exact hrow t ht
    _ = (W.card : ℝ) * |b - a| +
        4 * (W.card : ℝ) * (((harmonic K : ℚ) : ℝ)) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    _ = _ := rfl

theorem intervalIntegral_norm_gmRPhase_sq_le_epsilon
    {ε T : ℝ} {W : Finset ℝ} (hε : 0 < ε) (hT : 1 ≤ T)
    (hSep : IsSeparated 1 W) (hBase : InBaseInterval T W)
    (a b : ℝ) (hab : a ≤ b) :
    (∫ x in a..b, ‖gmRPhase W x‖ ^ 2) ≤
      (|b - a| + 4 * (1 + ε⁻¹) * 2 ^ ε * T ^ ε) * (W.card : ℝ) := by
  let K : ℕ := ⌈T⌉₊
  have hraw := intervalIntegral_norm_gmRPhase_sq_le_harmonic
    hT hSep hBase a b hab
  have hKle : (K : ℝ) ≤ 2 * T := by
    have hceil : (K : ℝ) < T + 1 := Nat.ceil_lt_add_one (by positivity)
    linarith
  have hTwoT : (1 : ℝ) ≤ 2 * T := by linarith
  have hpowK : (K : ℝ) ^ ε ≤ (2 * T) ^ ε :=
    Real.rpow_le_rpow (by positivity) hKle hε.le
  have hpowOne : (1 : ℝ) ≤ (2 * T) ^ ε := by
    simpa using Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hTwoT hε.le
  have hmax : max 1 ((K : ℝ) ^ ε) ≤ (2 * T) ^ ε := max_le hpowOne hpowK
  have hharm := harmonic_le_epsilon_rpow hε K
  have hharm' : (((harmonic K : ℚ) : ℝ)) ≤
      (1 + ε⁻¹) * 2 ^ ε * T ^ ε := by
    calc
      (((harmonic K : ℚ) : ℝ)) ≤
          (1 + ε⁻¹) * max 1 ((K : ℝ) ^ ε) := hharm
      _ ≤ (1 + ε⁻¹) * (2 * T) ^ ε := by gcongr
      _ = (1 + ε⁻¹) * 2 ^ ε * T ^ ε := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2)
          (zero_lt_one.trans_le hT).le]
        ring
  calc
    (∫ x in a..b, ‖gmRPhase W x‖ ^ 2) ≤
        (W.card : ℝ) * |b - a| +
          4 * (W.card : ℝ) * (((harmonic K : ℚ) : ℝ)) := hraw
    _ ≤ (W.card : ℝ) * |b - a| +
          4 * (W.card : ℝ) * ((1 + ε⁻¹) * 2 ^ ε * T ^ ε) := by
      gcongr
    _ = (|b - a| + 4 * (1 + ε⁻¹) * 2 ^ ε * T ^ ε) *
          (W.card : ℝ) := by ring

theorem setIntegral_norm_gmR_sq_eq_logWeighted (W : Finset ℝ) :
    (∫ u in Set.Icc (1 / 2 : ℝ) 2, ‖gmR W u‖ ^ 2) =
      ∫ x in Real.log (1 / 2 : ℝ)..Real.log 2,
        ‖gmRPhase W x‖ ^ 2 * Real.exp x := by
  let a : ℝ := Real.log (1 / 2 : ℝ)
  let b : ℝ := Real.log 2
  let g : ℝ → ℝ := fun u => ‖gmR W u‖ ^ 2
  have ha0 : (0 : ℝ) < 1 / 2 := by norm_num
  have hb0 : (0 : ℝ) < 2 := by norm_num
  have hab : a ≤ b := by
    dsimp only [a, b]
    exact Real.strictMonoOn_log.monotoneOn (Set.mem_Ioi.mpr ha0)
      (Set.mem_Ioi.mpr hb0) (by norm_num)
  have hgCont : ContinuousOn g (Real.exp '' Set.uIcc a b) := by
    rintro u ⟨x, hx, rfl⟩
    exact ((continuousAt_gmR W (Real.exp_ne_zero x)).norm.pow 2).continuousWithinAt
  have hsub := intervalIntegral.integral_comp_mul_deriv'
    (a := a) (b := b) (f := Real.exp) (f' := Real.exp) (g := g)
    (fun x _ => Real.hasDerivAt_exp x) Real.continuous_exp.continuousOn hgCont
  have hsub' :
      (∫ x in a..b, ‖gmRPhase W x‖ ^ 2 * Real.exp x) =
        ∫ u in (1 / 2 : ℝ)..2, ‖gmR W u‖ ^ 2 := by
    calc
      (∫ x in a..b, ‖gmRPhase W x‖ ^ 2 * Real.exp x) =
          ∫ x in a..b, (g ∘ Real.exp) x * Real.exp x := by
        apply intervalIntegral.integral_congr
        intro x hx
        simp only [Function.comp_apply, g, gmR_exp_eq_gmRPhase]
      _ = ∫ u in Real.exp a..Real.exp b, g u := hsub
      _ = ∫ u in (1 / 2 : ℝ)..2, ‖gmR W u‖ ^ 2 := by
        dsimp only [a, b, g]
        rw [Real.exp_log ha0, Real.exp_log hb0]
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (1 / 2 : ℝ) ≤ 2)]
  simpa only [a, b] using hsub'.symm

theorem setIntegral_norm_gmR_sq_le_epsilon
    {ε T : ℝ} {W : Finset ℝ} (hε : 0 < ε) (hT : 1 ≤ T)
    (hSep : IsSeparated 1 W) (hBase : InBaseInterval T W) :
    (∫ u in Set.Icc (1 / 2 : ℝ) 2, ‖gmR W u‖ ^ 2) ≤
      2 * (|Real.log 2 - Real.log (1 / 2 : ℝ)| +
        4 * (1 + ε⁻¹) * 2 ^ ε * T ^ ε) * (W.card : ℝ) := by
  let a : ℝ := Real.log (1 / 2 : ℝ)
  let b : ℝ := Real.log 2
  let q : ℝ → ℝ := fun x => ‖gmRPhase W x‖ ^ 2
  have hb0 : (0 : ℝ) < 2 := by norm_num
  have hab : a ≤ b := by
    dsimp only [a, b]
    exact Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr (by norm_num : (0 : ℝ) < 1 / 2))
      (Set.mem_Ioi.mpr hb0) (by norm_num)
  have hqCont : Continuous q := continuous_norm_gmRPhase_pow W 2
  have hfInt : IntervalIntegrable (fun x => q x * Real.exp x) volume a b :=
    (hqCont.mul Real.continuous_exp).intervalIntegrable a b
  have hgInt : IntervalIntegrable (fun x => (2 : ℝ) * q x) volume a b :=
    (continuous_const.mul hqCont).intervalIntegrable a b
  have hweighted : (∫ x in a..b, q x * Real.exp x) ≤
      2 * ∫ x in a..b, q x := by
    calc
      (∫ x in a..b, q x * Real.exp x) ≤ ∫ x in a..b, 2 * q x := by
        apply intervalIntegral.integral_mono_on hab hfInt hgInt
        intro x hx
        have hexp : Real.exp x ≤ (2 : ℝ) := by
          rw [← Real.exp_log hb0]
          exact Real.exp_le_exp.mpr hx.2
        have hq0 : 0 ≤ q x := by positivity
        nlinarith
      _ = 2 * ∫ x in a..b, q x := by
        rw [intervalIntegral.integral_const_mul]
  have hphase := intervalIntegral_norm_gmRPhase_sq_le_epsilon
    hε hT hSep hBase a b hab
  rw [setIntegral_norm_gmR_sq_eq_logWeighted W]
  change (∫ x in a..b, q x * Real.exp x) ≤ _
  calc
    (∫ x in a..b, q x * Real.exp x) ≤ 2 * ∫ x in a..b, q x := hweighted
    _ ≤ 2 * ((|b - a| + 4 * (1 + ε⁻¹) * 2 ^ ε * T ^ ε) *
        (W.card : ℝ)) := by gcongr
    _ = _ := by
      dsimp only [a, b, q]
      ring

/-! ## Exact changes of variables for Proposition 8.1 -/

/-- Restricting a nonnegative integrable function to an affine image costs
exactly the inverse absolute slope.  This is the measurable Jacobian form
needed for the first cancellation center in Proposition 8.1. -/
theorem setIntegral_comp_affine_le_global
    {f : ℝ → ℝ} (hf : Integrable f) (hf0 : ∀ x, 0 ≤ f x)
    {a b l u : ℝ} (ha : a ≠ 0) :
    (∫ x in Set.Icc l u, f (a * x + b)) ≤ |a|⁻¹ * ∫ y : ℝ, f y := by
  let φ : ℝ → ℝ := fun x => a * x + b
  have hderiv : ∀ x ∈ Set.Icc l u, HasDerivWithinAt φ a (Set.Icc l u) x := by
    intro x hx
    simpa only [φ, id_eq, mul_one] using
      (((hasDerivAt_id x).const_mul a).add_const b).hasDerivWithinAt
  have hinj : Set.InjOn φ (Set.Icc l u) := by
    intro x hx y hy hxy
    dsimp only [φ] at hxy
    apply mul_left_cancel₀ ha
    linarith
  have hjac := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    measurableSet_Icc hderiv hinj f
  have himageInt : IntegrableOn f (φ '' Set.Icc l u) := hf.integrableOn
  have hcompInt : IntegrableOn (fun x => |a| • f (φ x)) (Set.Icc l u) :=
    (MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul
      measurableSet_Icc hderiv hinj f).mp himageInt
  have hrestricted : (∫ y in φ '' Set.Icc l u, f y) ≤ ∫ y : ℝ, f y := by
    exact MeasureTheory.setIntegral_le_integral hf
      (Filter.Eventually.of_forall hf0)
  have habs : 0 < |a| := abs_pos.mpr ha
  have heq : (∫ x in Set.Icc l u, f (φ x)) = |a|⁻¹ * ∫ y in φ '' Set.Icc l u, f y := by
    have hjac' : (∫ y in φ '' Set.Icc l u, f y) =
        |a| * ∫ x in Set.Icc l u, f (φ x) := by
      calc
        (∫ y in φ '' Set.Icc l u, f y) =
            ∫ x in Set.Icc l u, |a| • f (φ x) := hjac
        _ = |a| * ∫ x in Set.Icc l u, f (φ x) := by
          simp only [smul_eq_mul]
          rw [MeasureTheory.integral_const_mul]
    rw [hjac']
    field_simp [habs.ne']
  rw [heq]
  exact mul_le_mul_of_nonneg_left hrestricted (inv_nonneg.mpr habs.le)

/-- Reciprocal substitution on the source interval.  The interval is fixed
by inversion, and its Jacobian is bounded by four.  No continuity assumption
on `f` is used. -/
theorem setIntegral_comp_inv_le_four_mul
    {f : ℝ → ℝ}
    (hf : IntegrableOn f (Set.Icc (1 / 2 : ℝ) 2))
    (hf0 : ∀ x, 0 ≤ f x) :
    (∫ x in Set.Icc (1 / 2 : ℝ) 2, f x⁻¹) ≤
      4 * ∫ y in Set.Icc (1 / 2 : ℝ) 2, f y := by
  let s : Set ℝ := Set.Icc (1 / 2 : ℝ) 2
  let φ : ℝ → ℝ := fun x => x⁻¹
  let g : ℝ → ℝ := fun y => (y ^ 2)⁻¹ * f y
  have hspos : ∀ x ∈ s, 0 < x := by
    intro x hx
    change x ∈ Set.Icc (1 / 2 : ℝ) 2 at hx
    exact lt_of_lt_of_le (by norm_num) hx.1
  have hderiv : ∀ x ∈ s, HasDerivWithinAt φ (-(x ^ 2)⁻¹) s x := by
    intro x hx
    exact (hasDerivAt_inv (ne_of_gt (hspos x hx))).hasDerivWithinAt
  have hinj : Set.InjOn φ s := by
    intro x hx y hy hxy
    exact inv_injective hxy
  have himage : φ '' s = s := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change x ∈ Set.Icc (1 / 2 : ℝ) 2 at hx
      change x⁻¹ ∈ Set.Icc (1 / 2 : ℝ) 2
      constructor
      · simpa using inv_anti₀ (hspos x hx) hx.2
      · simpa using inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 2) hx.1
    · intro hy
      refine ⟨y⁻¹, ?_, inv_inv y⟩
      change y ∈ Set.Icc (1 / 2 : ℝ) 2 at hy
      change y⁻¹ ∈ Set.Icc (1 / 2 : ℝ) 2
      have hypos : 0 < y := lt_of_lt_of_le (by norm_num) hy.1
      constructor
      · simpa using inv_anti₀ hypos hy.2
      · simpa using inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 2) hy.1
  have hgInt : IntegrableOn g (φ '' s) := by
    rw [himage]
    have hinvCont : ContinuousOn (fun y : ℝ => (y ^ 2)⁻¹) s := by
      apply (continuousOn_id.pow 2).inv₀
      intro y hy
      exact pow_ne_zero 2 (hspos y hy).ne'
    have hinvBound : ∀ y ∈ s, ‖(y ^ 2)⁻¹‖ ≤ 4 := by
      intro y hy
      have hypos := hspos y hy
      rw [Real.norm_eq_abs, abs_inv, abs_pow, abs_of_pos hypos]
      have hyinv : y⁻¹ ≤ 2 := by
        have := inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 2) hy.1
        simpa using this
      have hyinv0 : 0 ≤ y⁻¹ := (inv_pos.mpr hypos).le
      rw [← inv_pow]
      nlinarith
    have hmul : IntegrableOn (fun y => f y * (y ^ 2)⁻¹) s :=
      hf.mul_bdd
        (hinvCont.aestronglyMeasurable measurableSet_Icc)
        (by
          filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
          exact hinvBound y hy)
    apply hmul.congr
    filter_upwards with y
    simp only [g]
    ring
  have hjac := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    measurableSet_Icc hderiv hinj g
  rw [himage] at hjac hgInt
  have heq : (∫ x in s, f x⁻¹) = ∫ y in s, (y ^ 2)⁻¹ * f y := by
    calc
      (∫ x in s, f x⁻¹) =
          ∫ x in s, |-(x ^ 2)⁻¹| • g (φ x) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
        have hxpos := hspos x hx
        simp only [φ, g, abs_neg, abs_inv, abs_pow,
          abs_of_pos hxpos, smul_eq_mul]
        field_simp [hxpos.ne']
      _ = ∫ y in s, g y := hjac.symm
      _ = ∫ y in s, (y ^ 2)⁻¹ * f y := rfl
  rw [heq]
  have hmono : (∫ y in s, g y) ≤ ∫ y in s, 4 * f y := by
    apply MeasureTheory.setIntegral_mono_on hgInt (hf.const_mul 4)
      measurableSet_Icc
    intro y hy
    have hypos : 0 < y := by
      change y ∈ Set.Icc (1 / 2 : ℝ) 2 at hy
      exact lt_of_lt_of_le (by norm_num) hy.1
    have hyinv : y⁻¹ ≤ 2 := by
      have := inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 2) hy.1
      simpa using this
    have hyinv0 : 0 ≤ y⁻¹ := (inv_pos.mpr hypos).le
    have hfinv0 : 0 ≤ f y := hf0 y
    dsimp only [g]
    have hsq : (y ^ 2)⁻¹ ≤ 4 := by
      rw [← inv_pow]
      nlinarith
    nlinarith
  change (∫ y in s, g y) ≤ _
  calc
    (∫ y in s, g y) ≤ ∫ y in s, 4 * f y := hmono
    _ = 4 * ∫ y in s, f y := by rw [MeasureTheory.integral_const_mul]
    _ = _ := rfl

/-- The smoothed fourth power is globally integrable.  This is extracted
from the same compact-support Fubini majorant used in Lemma 8.3. -/
theorem integrable_gmCubicSmoothedR_fourth
    {η T : ℝ} {N M : ℕ} (W : Finset ℝ)
    (hB : 0 < gmCubicSmoothingScale η T N M) :
    Integrable (fun v : ℝ => gmCubicSmoothedR η T N M W v ^ 4) := by
  let B := gmCubicSmoothingScale η T N M
  let F : ℝ → ℝ := fun v =>
    ∫ u in gmCubicSmoothingSupport B v, ‖gmR W u‖ ^ 4
  have hkernel := integrable_gmCubicLocalFourthKernel (B := B) W
  have hFInt : Integrable F := by
    have hiter := hkernel.integral_prod_left
    apply hiter.congr
    filter_upwards with v
    exact integral_gmCubicLocalFourthKernel_right (B := B) W v
  have hmajorInt : Integrable (fun v => 4 * B * F v) := hFInt.const_mul (4 * B)
  apply hmajorInt.mono'
    ((measurable_gmCubicSmoothedR η T N M W).pow_const 4).aestronglyMeasurable
  filter_upwards with v
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
    0 ≤ gmCubicSmoothedR η T N M W v ^ 4)]
  rw [show gmCubicSmoothedR η T N M W v ^ 4 =
      (gmCubicSmoothedR η T N M W v ^ 2) ^ 2 by ring]
  rw [gmCubicSmoothedR_sq W v hB.le]
  exact gmCubicSmoothedRSq_sq_le_localFourth W v hB

/-- Exact affine-center fourth-moment transport in Proposition 8.1. -/
theorem setIntegral_gmCubicSmoothedR_fourth_cancellationCenter_le
    {η T : ℝ} {N M : ℕ} (W : Finset ℝ)
    (m : ℤ × (ℤ × ℤ)) (hm₁ : m.1 ≠ 0) (hm₂ : m.2.1 ≠ 0)
    (hB : 0 < gmCubicSmoothingScale η T N M) :
    (∫ v in Set.Icc (1 / 2 : ℝ) 2,
        gmCubicSmoothedR η T N M W (gmCubicCancellationCenter m v) ^ 4) ≤
      |-(m.1 : ℝ) / (m.2.1 : ℝ)|⁻¹ *
        ∫ u : ℝ, gmCubicSmoothedR η T N M W u ^ 4 := by
  let f : ℝ → ℝ := fun u => gmCubicSmoothedR η T N M W u ^ 4
  let a : ℝ := -(m.1 : ℝ) / (m.2.1 : ℝ)
  let b : ℝ := -(m.2.2 : ℝ) / (m.2.1 : ℝ)
  have hm₁R : (m.1 : ℝ) ≠ 0 := by exact_mod_cast hm₁
  have hm₂R : (m.2.1 : ℝ) ≠ 0 := by exact_mod_cast hm₂
  have ha : a ≠ 0 := div_ne_zero (neg_ne_zero.mpr hm₁R) hm₂R
  have hbase := setIntegral_comp_affine_le_global
    (integrable_gmCubicSmoothedR_fourth W hB)
    (fun u => by positivity) (a := a) (b := b)
    (l := 1 / 2) (u := 2) ha
  have hcenter : ∀ v : ℝ, gmCubicCancellationCenter m v = a * v + b := by
    intro v
    dsimp only [gmCubicCancellationCenter, a, b]
    field_simp [hm₂R]
    ring
  simpa only [f, a, b, hcenter] using hbase

/-- Exact reciprocal-plus-affine transport for the reflected cancellation
center.  The factor four is solely the reciprocal Jacobian on `[1/2,2]`. -/
theorem setIntegral_gmCubicSmoothedR_fourth_reflectedCenter_le
    {η T : ℝ} {N M : ℕ} (W : Finset ℝ)
    (m : ℤ × (ℤ × ℤ)) (hm₂ : m.2.1 ≠ 0) (hm₃ : m.2.2 ≠ 0)
    (hB : 0 < gmCubicSmoothingScale η T N M) :
    (∫ v in Set.Icc (1 / 2 : ℝ) 2,
        gmCubicSmoothedR η T N M W
          (gmCubicReflectedCancellationCenter m v) ^ 4) ≤
      4 * |-(m.2.2 : ℝ) / (m.2.1 : ℝ)|⁻¹ *
        ∫ u : ℝ, gmCubicSmoothedR η T N M W u ^ 4 := by
  let f : ℝ → ℝ := fun u => gmCubicSmoothedR η T N M W u ^ 4
  let a : ℝ := -(m.1 : ℝ) / (m.2.1 : ℝ)
  let b : ℝ := -(m.2.2 : ℝ) / (m.2.1 : ℝ)
  let q : ℝ → ℝ := fun y => f (b * y + a)
  have hm₂R : (m.2.1 : ℝ) ≠ 0 := by exact_mod_cast hm₂
  have hm₃R : (m.2.2 : ℝ) ≠ 0 := by exact_mod_cast hm₃
  have hb : b ≠ 0 := div_ne_zero (neg_ne_zero.mpr hm₃R) hm₂R
  have hfInt := integrable_gmCubicSmoothedR_fourth W hB
  have hqInt : IntegrableOn q (Set.Icc (1 / 2 : ℝ) 2) := by
    have hmeas : AEStronglyMeasurable q := by
      exact (((measurable_gmCubicSmoothedR η T N M W).comp
        (measurable_const.mul measurable_id |>.add measurable_const)).pow_const 4).aestronglyMeasurable
    apply IntegrableOn.of_bound measure_Icc_lt_top hmeas.restrict
        ((gmCubicSmoothingScale η T N M * (W.card : ℝ) ^ 2 * 4) ^ 2)
    filter_upwards with y
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ q y)]
    dsimp only [q, f]
    rw [show gmCubicSmoothedR η T N M W (b * y + a) ^ 4 =
        (gmCubicSmoothedRSq η T N M W (b * y + a)) ^ 2 by
      rw [← gmCubicSmoothedR_sq W _ hB.le]
      ring]
    nlinarith [gmCubicSmoothedRSq_nonneg W (b * y + a) hB.le,
      gmCubicSmoothedRSq_le W (b * y + a) hB.le]
  have hinv := setIntegral_comp_inv_le_four_mul hqInt (fun y => by positivity)
  have haff := setIntegral_comp_affine_le_global hfInt (fun u => by positivity)
    (a := b) (b := a) (l := 1 / 2) (u := 2) hb
  have hreflect : ∀ v ∈ Set.Icc (1 / 2 : ℝ) 2,
      gmCubicReflectedCancellationCenter m v = b * v⁻¹ + a := by
    intro v hv
    have hv0 : v ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hv.1)
    dsimp only [gmCubicReflectedCancellationCenter, gmCubicCancellationCenter, a, b]
    field_simp [hm₂R, hv0]
    ring
  calc
    (∫ v in Set.Icc (1 / 2 : ℝ) 2,
        gmCubicSmoothedR η T N M W
          (gmCubicReflectedCancellationCenter m v) ^ 4) =
        ∫ v in Set.Icc (1 / 2 : ℝ) 2, q v⁻¹ := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
      simp only [q, f, hreflect v hv]
    _ ≤ 4 * ∫ y in Set.Icc (1 / 2 : ℝ) 2, q y := hinv
    _ ≤ 4 * (|b|⁻¹ * ∫ u : ℝ, f u) := by gcongr
    _ = 4 * |-(m.2.2 : ℝ) / (m.2.1 : ℝ)|⁻¹ *
        ∫ u : ℝ, gmCubicSmoothedR η T N M W u ^ 4 := by
      dsimp only [a, b, f]
      ring

theorem inv_abs_neg_div_eq_abs_div
    (x y : ℝ) :
    |(-x) / y|⁻¹ = |y| / |x| := by
  rw [abs_div, abs_neg, inv_div]

/-- On the selected dyadic block, the first affine Jacobian is the source
ratio `M/M₁`, displayed with the exact dyadic endpoints. -/
theorem setIntegral_gmCubicSmoothedR_fourth_cancellationCenter_dyadic_le
    {η T : ℝ} {N M H r s : ℕ} (W : Finset ℝ)
    {m : ℤ × (ℤ × ℤ)} (hm : m ∈ gmCubicDyadicFrequencyBlock H r s)
    (hB : 0 < gmCubicSmoothingScale η T N M) :
    (∫ v in Set.Icc (1 / 2 : ℝ) 2,
        gmCubicSmoothedR η T N M W (gmCubicCancellationCenter m v) ^ 4) ≤
      ((((2 ^ (s + 1) : ℕ) : ℝ)) / (((2 ^ r : ℕ) : ℝ))) *
        ∫ u : ℝ, gmCubicSmoothedR η T N M W u ^ 4 := by
  have hmBlock := mem_gmCubicDyadicFrequencyBlock.mp hm
  have hmOrdered := mem_gmCubicBalancedOrderedFrequencyBox.mp hmBlock.1
  have hmNonzero := mem_gmCubicOrderedFrequencyBox.mp hmOrdered.1
  have hmNZ := mem_gmCubicNonzeroFrequencyBox.mp hmNonzero.1
  have hm₁R : (m.1 : ℝ) ≠ 0 := by exact_mod_cast hmNZ.2.1
  have hm₂R : (m.2.1 : ℝ) ≠ 0 := by exact_mod_cast hmNZ.2.2.1
  have hbase := setIntegral_gmCubicSmoothedR_fourth_cancellationCenter_le
    W m hmNZ.2.1 hmNZ.2.2.1 hB
  have hpowr0 : (0 : ℝ) < (((2 ^ r : ℕ) : ℝ)) := by positivity
  have habs1 : 0 < |(m.1 : ℝ)| := abs_pos.mpr hm₁R
  have hlow : (((2 ^ r : ℕ) : ℝ)) ≤ |(m.1 : ℝ)| := by
    rw [show |(m.1 : ℝ)| = (m.1.natAbs : ℝ) by
      simp only [Nat.cast_natAbs, Int.cast_abs]]
    exact_mod_cast hmBlock.2.1
  have hupp : |(m.2.1 : ℝ)| ≤ (((2 ^ (s + 1) : ℕ) : ℝ)) := by
    rw [show |(m.2.1 : ℝ)| = (m.2.1.natAbs : ℝ) by
      simp only [Nat.cast_natAbs, Int.cast_abs]]
    exact_mod_cast hmBlock.2.2.2.2.le
  have hratio : |(m.2.1 : ℝ)| / |(m.1 : ℝ)| ≤
      (((2 ^ (s + 1) : ℕ) : ℝ)) / (((2 ^ r : ℕ) : ℝ)) := by
    rw [div_le_div_iff₀ habs1 hpowr0]
    calc
      |(m.2.1 : ℝ)| * (((2 ^ r : ℕ) : ℝ)) ≤
          (((2 ^ (s + 1) : ℕ) : ℝ)) * (((2 ^ r : ℕ) : ℝ)) := by
        gcongr
      _ ≤ (((2 ^ (s + 1) : ℕ) : ℝ)) * |(m.1 : ℝ)| := by
        gcongr
  rw [inv_abs_neg_div_eq_abs_div (m.1 : ℝ) (m.2.1 : ℝ)] at hbase
  calc
    _ ≤ (|(m.2.1 : ℝ)| / |(m.1 : ℝ)|) *
        ∫ u : ℝ, gmCubicSmoothedR η T N M W u ^ 4 := hbase
    _ ≤ ((((2 ^ (s + 1) : ℕ) : ℝ)) / (((2 ^ r : ℕ) : ℝ))) *
        ∫ u : ℝ, gmCubicSmoothedR η T N M W u ^ 4 := by
      gcongr

/-- Ordered balanced frequencies make the reflected affine Jacobian at
most one; together with reciprocal substitution this costs exactly four. -/
theorem setIntegral_gmCubicSmoothedR_fourth_reflectedCenter_dyadic_le
    {η T : ℝ} {N M H r s : ℕ} (W : Finset ℝ)
    {m : ℤ × (ℤ × ℤ)} (hm : m ∈ gmCubicDyadicFrequencyBlock H r s)
    (hB : 0 < gmCubicSmoothingScale η T N M) :
    (∫ v in Set.Icc (1 / 2 : ℝ) 2,
        gmCubicSmoothedR η T N M W
          (gmCubicReflectedCancellationCenter m v) ^ 4) ≤
      4 * ∫ u : ℝ, gmCubicSmoothedR η T N M W u ^ 4 := by
  have hmBlock := mem_gmCubicDyadicFrequencyBlock.mp hm
  have hmBalanced := mem_gmCubicBalancedOrderedFrequencyBox.mp hmBlock.1
  have hmOrdered := mem_gmCubicOrderedFrequencyBox.mp hmBalanced.1
  have hmNZ := mem_gmCubicNonzeroFrequencyBox.mp hmOrdered.1
  have hm₂R : (m.2.1 : ℝ) ≠ 0 := by exact_mod_cast hmNZ.2.2.1
  have hm₃R : (m.2.2 : ℝ) ≠ 0 := by exact_mod_cast hmNZ.2.2.2
  have hbase := setIntegral_gmCubicSmoothedR_fourth_reflectedCenter_le
    W m hmNZ.2.2.1 hmNZ.2.2.2 hB
  rw [inv_abs_neg_div_eq_abs_div (m.2.2 : ℝ) (m.2.1 : ℝ)] at hbase
  have hratio : |(m.2.1 : ℝ)| / |(m.2.2 : ℝ)| ≤ 1 := by
    rw [div_le_one (abs_pos.mpr hm₃R)]
    exact hmOrdered.2.2
  have hglobal0 : 0 ≤ ∫ u : ℝ,
      gmCubicSmoothedR η T N M W u ^ 4 :=
    integral_nonneg_of_ae (Filter.Eventually.of_forall fun u => by positivity)
  calc
    _ ≤ 4 * (|(m.2.1 : ℝ)| / |(m.2.2 : ℝ)|) *
        ∫ u : ℝ, gmCubicSmoothedR η T N M W u ^ 4 := hbase
    _ ≤ 4 * 1 * ∫ u : ℝ,
        gmCubicSmoothedR η T N M W u ^ 4 := by gcongr
    _ = _ := by ring

/-- Per-mode Hölder step in Proposition 8.1, now attached to the actual
two cancellation centers from Proposition 7.2. -/
theorem gmCubicSmoothedModeIntegral_holder
    {η T : ℝ} {N M : ℕ} (W : Finset ℝ)
    (m : ℤ × (ℤ × ℤ))
    (hB : 0 < gmCubicSmoothingScale η T N M) :
    gmCubicSmoothedModeIntegral η T N M W m ≤
      Real.sqrt (∫ v in Set.Icc (1 / 2 : ℝ) 2, ‖gmR W v‖ ^ 2) *
        Real.sqrt
          (Real.sqrt (∫ v in Set.Icc (1 / 2 : ℝ) 2,
              gmCubicSmoothedR η T N M W
                (gmCubicReflectedCancellationCenter m v) ^ 4) *
            Real.sqrt (∫ v in Set.Icc (1 / 2 : ℝ) 2,
              gmCubicSmoothedR η T N M W
                (gmCubicCancellationCenter m v) ^ 4)) := by
  let μ : Measure ℝ := volume.restrict (Set.Icc (1 / 2 : ℝ) 2)
  let A : ℝ → ℝ := fun v => ‖gmR W v‖
  let B : ℝ → ℝ := fun v => gmCubicSmoothedR η T N M W
    (gmCubicReflectedCancellationCenter m v)
  let C : ℝ → ℝ := fun v => gmCubicSmoothedR η T N M W
    (gmCubicCancellationCenter m v)
  have hcenter : Measurable (gmCubicCancellationCenter m) := by
    unfold gmCubicCancellationCenter
    exact ((measurable_const.mul measurable_id).add measurable_const).neg.div_const _
  have hreflected : Measurable (gmCubicReflectedCancellationCenter m) := by
    unfold gmCubicReflectedCancellationCenter
    exact hcenter.div measurable_id
  have hAmeas : AEStronglyMeasurable A μ :=
    (measurable_gmR W).norm.aestronglyMeasurable
  have hBmeas : AEStronglyMeasurable B μ :=
    ((measurable_gmCubicSmoothedR η T N M W).comp hreflected).aestronglyMeasurable
  have hCmeas : AEStronglyMeasurable C μ :=
    ((measurable_gmCubicSmoothedR η T N M W).comp hcenter).aestronglyMeasurable
  let S : ℝ := Real.sqrt
    (gmCubicSmoothingScale η T N M * (W.card : ℝ) ^ 2 * 4)
  have hA2 : MemLp A (ENNReal.ofReal 2) μ := by
    apply MemLp.of_bound hAmeas (W.card : ℝ)
    filter_upwards with v
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact norm_gmR_le_card_all W v
  have hB4 : MemLp B (ENNReal.ofReal 4) μ := by
    apply MemLp.of_bound hBmeas S
    filter_upwards with v
    rw [Real.norm_eq_abs, abs_of_nonneg (by
      dsimp only [B, gmCubicSmoothedR]
      exact Real.sqrt_nonneg _)]
    dsimp only [B, S, gmCubicSmoothedR]
    exact Real.sqrt_le_sqrt (gmCubicSmoothedRSq_le W _ hB.le)
  have hC4 : MemLp C (ENNReal.ofReal 4) μ := by
    apply MemLp.of_bound hCmeas S
    filter_upwards with v
    rw [Real.norm_eq_abs, abs_of_nonneg (by
      dsimp only [C, gmCubicSmoothedR]
      exact Real.sqrt_nonneg _)]
    dsimp only [C, S, gmCubicSmoothedR]
    exact Real.sqrt_le_sqrt (gmCubicSmoothedRSq_le W _ hB.le)
  have hholder := integral_triple_le_L2_L4_L4
    (A := A) (B := B) (C := C) (μ := μ)
    (Filter.Eventually.of_forall fun v => by dsimp only [A]; positivity)
    (Filter.Eventually.of_forall fun v => by
      dsimp only [B, gmCubicSmoothedR]
      exact Real.sqrt_nonneg _)
    (Filter.Eventually.of_forall fun v => by
      dsimp only [C, gmCubicSmoothedR]
      exact Real.sqrt_nonneg _)
    hA2 hB4 hC4
  have hfour (x : ℝ) : x ^ (4 : ℝ) = x ^ (4 : ℕ) := by
    exact Real.rpow_natCast x 4
  simpa only [gmCubicSmoothedModeIntegral, gmCubicSmoothedModeIntegrand,
    μ, A, B, C, Real.rpow_two, hfour,
    ← Real.sqrt_eq_rpow] using hholder

theorem gmCubicSmoothedModeIntegral_dyadic_le
    {η T : ℝ} {N M H r s : ℕ} (W : Finset ℝ)
    {m : ℤ × (ℤ × ℤ)} (hm : m ∈ gmCubicDyadicFrequencyBlock H r s)
    (hB : 0 < gmCubicSmoothingScale η T N M) :
    gmCubicSmoothedModeIntegral η T N M W m ≤
      Real.sqrt (∫ v in Set.Icc (1 / 2 : ℝ) 2, ‖gmR W v‖ ^ 2) *
        Real.sqrt
          (Real.sqrt (4 * ∫ u : ℝ,
              gmCubicSmoothedR η T N M W u ^ 4) *
            Real.sqrt
              (((((2 ^ (s + 1) : ℕ) : ℝ)) /
                  (((2 ^ r : ℕ) : ℝ))) *
                ∫ u : ℝ, gmCubicSmoothedR η T N M W u ^ 4)) := by
  have hholder := gmCubicSmoothedModeIntegral_holder W m hB
  have href := setIntegral_gmCubicSmoothedR_fourth_reflectedCenter_dyadic_le
    W hm hB
  have hcenter := setIntegral_gmCubicSmoothedR_fourth_cancellationCenter_dyadic_le
    W hm hB
  calc
    gmCubicSmoothedModeIntegral η T N M W m ≤
        Real.sqrt (∫ v in Set.Icc (1 / 2 : ℝ) 2, ‖gmR W v‖ ^ 2) *
          Real.sqrt
            (Real.sqrt (∫ v in Set.Icc (1 / 2 : ℝ) 2,
                gmCubicSmoothedR η T N M W
                  (gmCubicReflectedCancellationCenter m v) ^ 4) *
              Real.sqrt (∫ v in Set.Icc (1 / 2 : ℝ) 2,
                gmCubicSmoothedR η T N M W
                  (gmCubicCancellationCenter m v) ^ 4)) := hholder
    _ ≤ _ := by gcongr

theorem sqrt_holder_product_identity
    {L G R : ℝ} (hG : 0 ≤ G) (hR : 0 ≤ R) :
    Real.sqrt L * Real.sqrt (Real.sqrt (4 * G) * Real.sqrt (R * G)) =
      Real.sqrt 2 * Real.sqrt (Real.sqrt R) * Real.sqrt L * Real.sqrt G := by
  have hfour : Real.sqrt (4 * G) = 2 * Real.sqrt G := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  have hRG : Real.sqrt (R * G) = Real.sqrt R * Real.sqrt G := by
    rw [Real.sqrt_mul hR]
  rw [hfour, hRG]
  have hinside : (2 * Real.sqrt G) * (Real.sqrt R * Real.sqrt G) =
      2 * Real.sqrt R * G := by
    calc
      (2 * Real.sqrt G) * (Real.sqrt R * Real.sqrt G) =
          2 * Real.sqrt R * (Real.sqrt G * Real.sqrt G) := by ring
      _ = 2 * Real.sqrt R * G := by rw [Real.mul_self_sqrt hG]
  rw [hinside]
  have hsqrt : Real.sqrt (2 * Real.sqrt R * G) =
      Real.sqrt 2 * (Real.sqrt (Real.sqrt R) * Real.sqrt G) := by
    calc
      Real.sqrt (2 * Real.sqrt R * G) =
          Real.sqrt (2 * (Real.sqrt R * G)) := by ring_nf
      _ = Real.sqrt 2 * Real.sqrt (Real.sqrt R * G) := by
        rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2)]
      _ = Real.sqrt 2 * (Real.sqrt (Real.sqrt R) * Real.sqrt G) := by
        rw [Real.sqrt_mul (Real.sqrt_nonneg R)]
  rw [hsqrt]
  ring

theorem gmCubicSmoothedModeIntegral_dyadic_simplified_le
    {η T : ℝ} {N M H r s : ℕ} (W : Finset ℝ)
    {m : ℤ × (ℤ × ℤ)} (hm : m ∈ gmCubicDyadicFrequencyBlock H r s)
    (hB : 0 < gmCubicSmoothingScale η T N M) :
    gmCubicSmoothedModeIntegral η T N M W m ≤
      Real.sqrt 2 *
        Real.sqrt (Real.sqrt
          (((2 ^ (s + 1) : ℕ) : ℝ) / ((2 ^ r : ℕ) : ℝ))) *
        Real.sqrt (∫ v in Set.Icc (1 / 2 : ℝ) 2, ‖gmR W v‖ ^ 2) *
        Real.sqrt (∫ u : ℝ, gmCubicSmoothedR η T N M W u ^ 4) := by
  let L : ℝ := ∫ v in Set.Icc (1 / 2 : ℝ) 2, ‖gmR W v‖ ^ 2
  let G : ℝ := ∫ u : ℝ, gmCubicSmoothedR η T N M W u ^ 4
  let R : ℝ := (((2 ^ (s + 1) : ℕ) : ℝ) / ((2 ^ r : ℕ) : ℝ))
  have hG : 0 ≤ G := integral_nonneg_of_ae
    (Filter.Eventually.of_forall fun u => by dsimp only [G]; positivity)
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have hraw := gmCubicSmoothedModeIntegral_dyadic_le W hm hB
  have hid := sqrt_holder_product_identity (L := L) hG hR
  change gmCubicSmoothedModeIntegral η T N M W m ≤
      Real.sqrt L * Real.sqrt (Real.sqrt (4 * G) * Real.sqrt (R * G)) at hraw
  rw [hid] at hraw
  simpa only [L, G, R] using hraw

/-! ### Exact dyadic mode count -/

/-- The `gmCubicDyadicBoundingBox` definition used by the source-facing construction in `LargeValuesS3`. -/
noncomputable def gmCubicDyadicBoundingBox (r s : ℕ) :
    Finset (ℤ × (ℤ × ℤ)) :=
  let A : ℕ := 2 ^ (r + 1)
  let B : ℕ := 2 ^ (s + 1)
  Finset.Icc (-(A : ℤ)) (A : ℤ) ×ˢ
    (Finset.Icc (-(B : ℤ)) (B : ℤ) ×ˢ
      Finset.Icc (-((5 * B : ℕ) : ℤ)) ((5 * B : ℕ) : ℤ))

theorem gmCubicDyadicFrequencyBlock_subset_boundingBox
    (H r s : ℕ) :
    gmCubicDyadicFrequencyBlock H r s ⊆ gmCubicDyadicBoundingBox r s := by
  intro m hm
  have hmBlock := mem_gmCubicDyadicFrequencyBlock.mp hm
  have hmBalanced := mem_gmCubicBalancedOrderedFrequencyBox.mp hmBlock.1
  let A : ℕ := 2 ^ (r + 1)
  let B : ℕ := 2 ^ (s + 1)
  have h₁absZ : |m.1| ≤ (A : ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast hmBlock.2.2.1.le
  have h₂absZ : |m.2.1| ≤ (B : ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast hmBlock.2.2.2.2.le
  have h₃real : |(m.2.2 : ℝ)| ≤ (5 * B : ℕ) := by
    calc
      |(m.2.2 : ℝ)| ≤ 5 * |(m.2.1 : ℝ)| := hmBalanced.2
      _ ≤ 5 * (B : ℝ) := by
        gcongr
        rw [show |(m.2.1 : ℝ)| = (m.2.1.natAbs : ℝ) by
          simp only [Nat.cast_natAbs, Int.cast_abs]]
        exact_mod_cast hmBlock.2.2.2.2.le
      _ = (5 * B : ℕ) := by push_cast; ring
  have h₃absZ : |m.2.2| ≤ ((5 * B : ℕ) : ℤ) := by
    exact_mod_cast h₃real
  rw [show m ∈ gmCubicDyadicBoundingBox r s ↔
      (-(A : ℤ) ≤ m.1 ∧ m.1 ≤ (A : ℤ)) ∧
      (-(B : ℤ) ≤ m.2.1 ∧ m.2.1 ≤ (B : ℤ)) ∧
      (-((5 * B : ℕ) : ℤ) ≤ m.2.2 ∧
        m.2.2 ≤ ((5 * B : ℕ) : ℤ)) by
    simp [gmCubicDyadicBoundingBox, A, B, and_assoc]]
  exact ⟨abs_le.mp h₁absZ, abs_le.mp h₂absZ, abs_le.mp h₃absZ⟩

theorem card_gmCubicDyadicBoundingBox (r s : ℕ) :
    (gmCubicDyadicBoundingBox r s).card =
      (2 * 2 ^ (r + 1) + 1) *
        ((2 * 2 ^ (s + 1) + 1) * (2 * (5 * 2 ^ (s + 1)) + 1)) := by
  let A : ℕ := 2 ^ (r + 1)
  let B : ℕ := 2 ^ (s + 1)
  have hcard (K : ℕ) : (Finset.Icc (-(K : ℤ)) (K : ℤ)).card = 2 * K + 1 := by
    rw [Int.card_Icc]
    rw [show (K : ℤ) + 1 - -(K : ℤ) = ((2 * K + 1 : ℕ) : ℤ) by
      push_cast
      ring]
    exact Int.toNat_natCast _
  rw [gmCubicDyadicBoundingBox]
  simp only [Finset.card_product]
  rw [hcard A, hcard B, hcard (5 * B)]

theorem card_gmCubicDyadicFrequencyBlock_le_scales
    (H r s : ℕ) :
    (gmCubicDyadicFrequencyBlock H r s).card ≤
      1000 * 2 ^ r * (2 ^ s) ^ 2 := by
  let A : ℕ := 2 ^ (r + 1)
  let B : ℕ := 2 ^ (s + 1)
  have hsubset := gmCubicDyadicFrequencyBlock_subset_boundingBox H r s
  have hcard := Finset.card_le_card hsubset
  rw [card_gmCubicDyadicBoundingBox] at hcard
  have hApos : 0 < A := by positivity
  have hBpos : 0 < B := by positivity
  have hA : 2 * A + 1 ≤ 3 * A := by omega
  have hB : 2 * B + 1 ≤ 3 * B := by omega
  have h5B : 2 * (5 * B) + 1 ≤ 11 * B := by omega
  calc
    (gmCubicDyadicFrequencyBlock H r s).card ≤
        (2 * A + 1) * ((2 * B + 1) * (2 * (5 * B) + 1)) := by
      simpa only [A, B] using hcard
    _ ≤ (3 * A) * ((3 * B) * (11 * B)) := by gcongr
    _ = 792 * 2 ^ r * (2 ^ s) ^ 2 := by
      dsimp only [A, B]
      ring
    _ ≤ 1000 * 2 ^ r * (2 ^ s) ^ 2 := by
      gcongr
      norm_num

/-- Proposition 8.1 before epsilon absorption: Hölder and the exact
dyadic mode count have been summed, while the second and fourth moments
remain visible for later substitution. -/
theorem sum_gmCubicSmoothedModeIntegral_dyadic_le
    {η T : ℝ} {N M H r s : ℕ} (W : Finset ℝ)
    (hB : 0 < gmCubicSmoothingScale η T N M) :
    (∑ m ∈ gmCubicDyadicFrequencyBlock H r s,
        gmCubicSmoothedModeIntegral η T N M W m) ≤
      (1000 * 2 ^ r * (2 ^ s) ^ 2 : ℕ) *
        (Real.sqrt (∫ v in Set.Icc (1 / 2 : ℝ) 2, ‖gmR W v‖ ^ 2) *
          Real.sqrt
            (Real.sqrt (4 * ∫ u : ℝ,
                gmCubicSmoothedR η T N M W u ^ 4) *
              Real.sqrt
                (((((2 ^ (s + 1) : ℕ) : ℝ)) /
                    (((2 ^ r : ℕ) : ℝ))) *
                  ∫ u : ℝ, gmCubicSmoothedR η T N M W u ^ 4))) := by
  let Q : ℝ :=
    Real.sqrt (∫ v in Set.Icc (1 / 2 : ℝ) 2, ‖gmR W v‖ ^ 2) *
      Real.sqrt
        (Real.sqrt (4 * ∫ u : ℝ,
            gmCubicSmoothedR η T N M W u ^ 4) *
          Real.sqrt
            (((((2 ^ (s + 1) : ℕ) : ℝ)) /
                (((2 ^ r : ℕ) : ℝ))) *
              ∫ u : ℝ, gmCubicSmoothedR η T N M W u ^ 4))
  have hsum : (∑ m ∈ gmCubicDyadicFrequencyBlock H r s,
      gmCubicSmoothedModeIntegral η T N M W m) ≤
      ∑ _m ∈ gmCubicDyadicFrequencyBlock H r s, Q := by
    apply Finset.sum_le_sum
    intro m hm
    exact gmCubicSmoothedModeIntegral_dyadic_le W hm hB
  have hcard := card_gmCubicDyadicFrequencyBlock_le_scales H r s
  have hQ0 : 0 ≤ Q := by dsimp only [Q]; positivity
  calc
    (∑ m ∈ gmCubicDyadicFrequencyBlock H r s,
        gmCubicSmoothedModeIntegral η T N M W m) ≤
        ∑ _m ∈ gmCubicDyadicFrequencyBlock H r s, Q := hsum
    _ = ((gmCubicDyadicFrequencyBlock H r s).card : ℝ) * Q := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((1000 * 2 ^ r * (2 ^ s) ^ 2 : ℕ) : ℝ) * Q := by
      gcongr
    _ = _ := by rfl

theorem Real.sqrt_le_self_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    Real.sqrt x ≤ x := by
  rw [Real.sqrt_le_iff]
  constructor
  · linarith
  · nlinarith [sq_nonneg (x - 1)]

/-- The `M₁` count cancels the enlarged affine Jacobian.  This is the
finite scale calculation `M₁ M² (M/M₁)^{1/4} ≪ M³` from Proposition 8.1,
proved here with the harmless stronger bound `(M/M₁)^{1/4} ≤ M/M₁`. -/
theorem sum_gmCubicSmoothedModeIntegral_dyadic_scale_le
    {η T : ℝ} {N M H r s : ℕ} (W : Finset ℝ) (hrs : r ≤ s)
    (hB : 0 < gmCubicSmoothingScale η T N M) :
    (∑ m ∈ gmCubicDyadicFrequencyBlock H r s,
        gmCubicSmoothedModeIntegral η T N M W m) ≤
      (2000 : ℝ) * (2 ^ s : ℕ) ^ 3 * Real.sqrt 2 *
        Real.sqrt (∫ v in Set.Icc (1 / 2 : ℝ) 2, ‖gmR W v‖ ^ 2) *
        Real.sqrt (∫ u : ℝ, gmCubicSmoothedR η T N M W u ^ 4) := by
  let A : ℝ := ((2 ^ r : ℕ) : ℝ)
  let B : ℝ := ((2 ^ s : ℕ) : ℝ)
  let R : ℝ := ((2 ^ (s + 1) : ℕ) : ℝ) / A
  let L : ℝ := ∫ v in Set.Icc (1 / 2 : ℝ) 2, ‖gmR W v‖ ^ 2
  let G : ℝ := ∫ u : ℝ, gmCubicSmoothedR η T N M W u ^ 4
  let Q : ℝ := Real.sqrt 2 * Real.sqrt (Real.sqrt R) * Real.sqrt L * Real.sqrt G
  have hApos : 0 < A := by dsimp only [A]; positivity
  have hBpos : 0 < B := by dsimp only [B]; positivity
  have hAB : A ≤ B := by
    dsimp only [A, B]
    exact_mod_cast Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) hrs
  have hRform : R = 2 * B / A := by
    dsimp only [R, A, B]
    push_cast
    rw [pow_succ']
  have hRone : 1 ≤ R := by
    rw [hRform, le_div_iff₀ hApos]
    nlinarith
  have hroot : Real.sqrt (Real.sqrt R) ≤ R :=
    (Real.sqrt_le_self_of_one_le (Real.one_le_sqrt.mpr hRone)).trans
      (Real.sqrt_le_self_of_one_le hRone)
  have hsum : (∑ m ∈ gmCubicDyadicFrequencyBlock H r s,
      gmCubicSmoothedModeIntegral η T N M W m) ≤
      ((gmCubicDyadicFrequencyBlock H r s).card : ℝ) * Q := by
    calc
      _ ≤ ∑ _m ∈ gmCubicDyadicFrequencyBlock H r s, Q := by
        apply Finset.sum_le_sum
        intro m hm
        exact gmCubicSmoothedModeIntegral_dyadic_simplified_le W hm hB
      _ = ((gmCubicDyadicFrequencyBlock H r s).card : ℝ) * Q := by
        simp only [Finset.sum_const, nsmul_eq_mul]
  have hcard := card_gmCubicDyadicFrequencyBlock_le_scales H r s
  have hQ0 : 0 ≤ Q := by dsimp only [Q]; positivity
  have hscale : ((1000 * 2 ^ r * (2 ^ s) ^ 2 : ℕ) : ℝ) * Q ≤
      2000 * B ^ 3 * Real.sqrt 2 * Real.sqrt L * Real.sqrt G := by
    calc
      ((1000 * 2 ^ r * (2 ^ s) ^ 2 : ℕ) : ℝ) * Q =
          1000 * A * B ^ 2 *
            (Real.sqrt 2 * Real.sqrt (Real.sqrt R) * Real.sqrt L * Real.sqrt G) := by
        dsimp only [A, B, Q]
        push_cast
        ring
      _ ≤ 1000 * A * B ^ 2 *
            (Real.sqrt 2 * R * Real.sqrt L * Real.sqrt G) := by gcongr
      _ = 2000 * B ^ 3 * Real.sqrt 2 * Real.sqrt L * Real.sqrt G := by
        rw [hRform]
        field_simp [hApos.ne']
        ring
  calc
    _ ≤ ((gmCubicDyadicFrequencyBlock H r s).card : ℝ) * Q := hsum
    _ ≤ ((1000 * 2 ^ r * (2 ^ s) ^ 2 : ℕ) : ℝ) * Q := by
      gcongr
    _ ≤ 2000 * B ^ 3 * Real.sqrt 2 * Real.sqrt L * Real.sqrt G := hscale
    _ = _ := by
      dsimp only [B, L, G]

/-- The `gmCubicL2Constant` definition used by the source-facing construction in `LargeValuesS3`. -/
noncomputable def gmCubicL2Constant (ε : ℝ) : ℝ :=
  2 * (|Real.log 2 - Real.log (1 / 2 : ℝ)| +
    4 * (1 + ε⁻¹) * 2 ^ ε)

/-- The `gmCubicFourthConstant` definition used by the source-facing construction in `LargeValuesS3`. -/
noncomputable def gmCubicFourthConstant (ε : ℝ) : ℝ :=
  66 * (4 * |Real.log (33 / 8 : ℝ) - Real.log (1 / 8 : ℝ)| +
    8 * (1 + ε⁻¹) * 3 ^ ε)

theorem gmCubicL2Constant_pos {ε : ℝ} (hε : 0 < ε) :
    0 < gmCubicL2Constant ε := by
  unfold gmCubicL2Constant
  positivity

theorem gmCubicFourthConstant_pos {ε : ℝ} (hε : 0 < ε) :
    0 < gmCubicFourthConstant ε := by
  unfold gmCubicFourthConstant
  positivity

theorem setIntegral_norm_gmR_sq_le_epsilon_budget
    {ε T : ℝ} {W : Finset ℝ} (hε : 0 < ε) (hT : 1 ≤ T)
    (hSep : IsSeparated 1 W) (hBase : InBaseInterval T W) :
    (∫ u in Set.Icc (1 / 2 : ℝ) 2, ‖gmR W u‖ ^ 2) ≤
      gmCubicL2Constant ε * T ^ ε * (W.card : ℝ) := by
  let A : ℝ := |Real.log 2 - Real.log (1 / 2 : ℝ)|
  let D : ℝ := 4 * (1 + ε⁻¹) * 2 ^ ε
  let X : ℝ := T ^ ε
  have hraw := setIntegral_norm_gmR_sq_le_epsilon hε hT hSep hBase
  have hX : 1 ≤ X := by
    dsimp only [X]
    simpa using Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hT hε.le
  have hA : 0 ≤ A := abs_nonneg _
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hcard : 0 ≤ (W.card : ℝ) := by positivity
  calc
    (∫ u in Set.Icc (1 / 2 : ℝ) 2, ‖gmR W u‖ ^ 2) ≤
        2 * (A + D * X) * (W.card : ℝ) := by
      simpa only [A, D, X] using hraw
    _ ≤ 2 * ((A + D) * X) * (W.card : ℝ) := by
      gcongr
      calc
        A + D * X ≤ A * X + D * X := by
          have := mul_nonneg hA (sub_nonneg.mpr hX)
          nlinarith
        _ = (A + D) * X := by ring
    _ = gmCubicL2Constant ε * T ^ ε * (W.card : ℝ) := by
      dsimp only [gmCubicL2Constant, A, D, X]
      ring

theorem integral_gmCubicSmoothedR_fourth_le_epsilon_budget
    {ε η T : ℝ} {N M : ℕ} {W : Finset ℝ}
    (hε : 0 < ε) (hT : 1 ≤ T) (hW : InBaseInterval T W)
    (hB : 0 < gmCubicSmoothingScale η T N M) :
    (∫ v : ℝ, gmCubicSmoothedR η T N M W v ^ 4) ≤
      gmCubicFourthConstant ε * T ^ ε * (ApproxAddEnergy 1 W : ℝ) := by
  simpa only [gmCubicFourthConstant] using
    integral_gmCubicSmoothedR_fourth_le_energy_epsilon hε hT hW hB

/-- Guth--Maynard Proposition 8.1 at one selected dyadic block, with all
epsilon constants explicit and no asymptotic notation. -/
theorem sum_gmCubicSmoothedModeIntegral_prop8_1
    {ε η T : ℝ} {N M H r s : ℕ} {W : Finset ℝ}
    (hε : 0 < ε) (hT : 1 ≤ T) (hSep : IsSeparated 1 W)
    (hBase : InBaseInterval T W) (hrs : r ≤ s)
    (hB : 0 < gmCubicSmoothingScale η T N M) :
    (∑ m ∈ gmCubicDyadicFrequencyBlock H r s,
        gmCubicSmoothedModeIntegral η T N M W m) ≤
      (2000 : ℝ) * (2 ^ s : ℕ) ^ 3 * Real.sqrt 2 *
        Real.sqrt (gmCubicL2Constant ε * T ^ ε * (W.card : ℝ)) *
        Real.sqrt (gmCubicFourthConstant ε * T ^ ε *
          (ApproxAddEnergy 1 W : ℝ)) := by
  have hraw := sum_gmCubicSmoothedModeIntegral_dyadic_scale_le
    (H := H) W hrs hB
  have hL := setIntegral_norm_gmR_sq_le_epsilon_budget hε hT hSep hBase
  have hG := integral_gmCubicSmoothedR_fourth_le_epsilon_budget
    hε hT hBase hB
  calc
    _ ≤ (2000 : ℝ) * (2 ^ s : ℕ) ^ 3 * Real.sqrt 2 *
        Real.sqrt (∫ v in Set.Icc (1 / 2 : ℝ) 2, ‖gmR W v‖ ^ 2) *
        Real.sqrt (∫ u : ℝ, gmCubicSmoothedR η T N M W u ^ 4) := hraw
    _ ≤ _ := by gcongr

theorem twoPow_second_dyadicIndex_le_two_ratio
    {η T : ℝ} {N : ℕ} {p : ℕ × ℕ}
    (hT : 1 ≤ T) (hη : 0 ≤ η) (hN : 0 < N) (hNT : (N : ℝ) ≤ T)
    (hp : p ∈ gmCubicDyadicIndexPairs (gmCubicFrequencyRadius η T N)) :
    ((2 ^ p.2 : ℕ) : ℝ) ≤ 2 * T ^ (1 + η) / (N : ℝ) := by
  let H := gmCubicFrequencyRadius η T N
  let X : ℝ := T ^ (1 + η) / (N : ℝ)
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hpowT : T ≤ T ^ (1 + η) := by
    calc
      T = T ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ ≤ T ^ (1 + η) := Real.rpow_le_rpow_of_exponent_le hT (by linarith)
  have hXone : 1 ≤ X := by
    rw [le_div_iff₀ hNreal]
    simpa using hNT.trans hpowT
  have hXH : X ≤ (H : ℝ) := ratio_le_gmCubicFrequencyRadius
  have hHpos : 0 < H := by
    by_contra hHzero
    have hH0 : H = 0 := Nat.eq_zero_of_not_pos hHzero
    rw [hH0, Nat.cast_zero] at hXH
    linarith
  have hpMem := mem_gmCubicDyadicIndexPairs.mp hp
  have hpLog : p.2 ≤ Nat.log 2 H := by
    dsimp only [H]
    omega
  have hpPow : 2 ^ p.2 ≤ H := by
    exact (Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) hpLog).trans
      (Nat.pow_log_le_self 2 hHpos.ne')
  have hHlt : (H : ℝ) < X + 1 := by
    dsimp only [H, X, gmCubicFrequencyRadius]
    exact Nat.ceil_lt_add_one (by positivity)
  calc
    ((2 ^ p.2 : ℕ) : ℝ) ≤ (H : ℝ) := by exact_mod_cast hpPow
    _ ≤ X + 1 := hHlt.le
    _ ≤ 2 * X := by linarith
    _ = 2 * T ^ (1 + η) / (N : ℝ) := by
      dsimp only [X]
      ring

/-- The dyadic scale chosen in Section 7 removes the original `N²/M`
normalization exactly as in the first line of the proof of Proposition 8.1. -/
theorem natCast_sq_mul_twoPow_second_dyadicIndex_sq_le
    {η T : ℝ} {N : ℕ} {p : ℕ × ℕ}
    (hT : 1 ≤ T) (hη : 0 ≤ η) (hN : 0 < N) (hNT : (N : ℝ) ≤ T)
    (hp : p ∈ gmCubicDyadicIndexPairs (gmCubicFrequencyRadius η T N)) :
    (N : ℝ) ^ 2 * ((2 ^ p.2 : ℕ) : ℝ) ^ 2 ≤
      4 * T ^ (2 * (1 + η)) := by
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hscale := twoPow_second_dyadicIndex_le_two_ratio hT hη hN hNT hp
  have hNM : (N : ℝ) * ((2 ^ p.2 : ℕ) : ℝ) ≤ 2 * T ^ (1 + η) := by
    have := (le_div_iff₀ hNreal).mp hscale
    nlinarith
  have hNM0 : 0 ≤ (N : ℝ) * ((2 ^ p.2 : ℕ) : ℝ) := by positivity
  have hright0 : 0 ≤ 2 * T ^ (1 + η) := by positivity
  have hsq := (sq_le_sq₀ hNM0 hright0).mpr hNM
  calc
    (N : ℝ) ^ 2 * ((2 ^ p.2 : ℕ) : ℝ) ^ 2 =
        ((N : ℝ) * ((2 ^ p.2 : ℕ) : ℝ)) ^ 2 := by ring
    _ ≤ (2 * T ^ (1 + η)) ^ 2 := hsq
    _ = 4 * T ^ (2 * (1 + η)) := by
      rw [mul_pow]
      norm_num
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul (lt_of_lt_of_le zero_lt_one hT).le]
      ring_nf

/-- The two dyadic pigeonhole logarithms in Proposition 7.2 cost at most
`36 (log T)²` once the height has reached `e`.  This is the explicit bridge
from the finite binary logarithm to the paper's `T^{o(1)}` notation. -/
theorem gmCubicDyadicLogFactor_sq_le_realLog_sq
    {η T : ℝ} {N : ℕ} (hT : Real.exp 1 ≤ T)
    (hη : 0 ≤ η) (hηupper : η ≤ 2 / 3) (hN : 0 < N)
    (hNT : (N : ℝ) ≤ T) :
    (((Nat.log 2 (gmCubicFrequencyRadius η T N) + 1 : ℕ) : ℝ)) ^ 2 ≤
      36 * (Real.log T) ^ 2 := by
  let H := gmCubicFrequencyRadius η T N
  have hTpos : 0 < T := (Real.exp_pos 1).trans_le hT
  have hTone : 1 ≤ T := by
    calc
      (1 : ℝ) = Real.exp 0 := by rw [Real.exp_zero]
      _ ≤ Real.exp 1 := Real.exp_le_exp.mpr (by norm_num)
      _ ≤ T := hT
  have hlogTone : 1 ≤ Real.log T := by
    simpa using Real.log_le_log (Real.exp_pos 1) hT
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hpowOne : 1 ≤ T ^ (1 + η) := by
    apply Real.one_le_rpow hTone
    linarith
  have hpowT : T ≤ T ^ (1 + η) := by
    calc
      T = T ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ ≤ T ^ (1 + η) := Real.rpow_le_rpow_of_exponent_le hTone (by linarith)
  have hHone : 1 ≤ H := by
    have hratioOne : 1 ≤ T ^ (1 + η) / (N : ℝ) := by
      rw [le_div_iff₀ hNreal]
      simpa using hNT.trans hpowT
    have hceilReal : (1 : ℝ) ≤
        (Nat.ceil (T ^ (1 + η) / (N : ℝ)) : ℝ) :=
      hratioOne.trans (Nat.le_ceil _)
    exact_mod_cast hceilReal
  have hHle : (H : ℝ) ≤ 2 * T ^ (1 + η) := by
    have hraw := gmCubicFrequencyRadius_cast_lt_rpow_add_one
      (η := η) hTpos hN
    linarith
  have hlogH := natCast_log_two_le_log H hHone
  have hlogMono : Real.log (H : ℝ) ≤ Real.log (2 * T ^ (1 + η)) :=
    Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr (by exact_mod_cast (show 0 < H by omega)))
      (Set.mem_Ioi.mpr (by positivity)) hHle
  have hlogProduct :
      Real.log (2 * T ^ (1 + η)) =
        Real.log 2 + (1 + η) * Real.log T := by
    rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hTpos _).ne']
    rw [Real.log_rpow hTpos]
  have hlogTwoPos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcount : ((Nat.log 2 H + 1 : ℕ) : ℝ) ≤ 6 * Real.log T := by
    push_cast
    calc
      (Nat.log 2 H : ℝ) + 1 ≤ Real.log H / Real.log 2 + 1 := by
        linarith
      _ ≤ Real.log (2 * T ^ (1 + η)) / Real.log 2 + 1 := by
        gcongr
      _ = (Real.log 2 + (1 + η) * Real.log T) / Real.log 2 + 1 := by
        rw [hlogProduct]
      _ ≤ 6 * Real.log T := by
        have hdiv :
            (Real.log 2 + (1 + η) * Real.log T) / Real.log 2 ≤
              6 * Real.log T - 1 := by
          rw [div_le_iff₀ hlogTwoPos]
          nlinarith [Real.log_two_gt_d9, Real.log_two_lt_d9]
        linarith
  have hcount0 : 0 ≤ ((Nat.log 2 H + 1 : ℕ) : ℝ) := by positivity
  have hlog0 : 0 ≤ 6 * Real.log T := by positivity
  have hsq := (sq_le_sq₀ hcount0 hlog0).mpr hcount
  simpa only [H] using (hsq.trans_eq (by ring))

/-- Exact extraction of the common epsilon power from the second- and
fourth-moment square roots in Proposition 8.1. -/
theorem sqrt_epsilon_moment_product_eq
    {A B T ε X Y : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hT : 0 ≤ T) :
    Real.sqrt (A * T ^ ε * X) * Real.sqrt (B * T ^ ε * Y) =
      Real.sqrt A * Real.sqrt B * T ^ ε * Real.sqrt X * Real.sqrt Y := by
  have hpow : 0 ≤ T ^ ε := Real.rpow_nonneg hT _
  have hleft : Real.sqrt (A * T ^ ε * X) =
      Real.sqrt A * Real.sqrt (T ^ ε) * Real.sqrt X := by
    calc
      Real.sqrt (A * T ^ ε * X) = Real.sqrt (A * (T ^ ε * X)) := by ring_nf
      _ = Real.sqrt A * Real.sqrt (T ^ ε * X) := by rw [Real.sqrt_mul hA]
      _ = Real.sqrt A * (Real.sqrt (T ^ ε) * Real.sqrt X) := by
        rw [Real.sqrt_mul hpow]
      _ = _ := by ring
  have hright : Real.sqrt (B * T ^ ε * Y) =
      Real.sqrt B * Real.sqrt (T ^ ε) * Real.sqrt Y := by
    calc
      Real.sqrt (B * T ^ ε * Y) = Real.sqrt (B * (T ^ ε * Y)) := by ring_nf
      _ = Real.sqrt B * Real.sqrt (T ^ ε * Y) := by rw [Real.sqrt_mul hB]
      _ = Real.sqrt B * (Real.sqrt (T ^ ε) * Real.sqrt Y) := by
        rw [Real.sqrt_mul hpow]
      _ = _ := by ring
  rw [hleft, hright]
  have hsqrtPow : Real.sqrt (T ^ ε) * Real.sqrt (T ^ ε) = T ^ ε :=
    Real.mul_self_sqrt hpow
  calc
    Real.sqrt A * Real.sqrt (T ^ ε) * Real.sqrt X *
          (Real.sqrt B * Real.sqrt (T ^ ε) * Real.sqrt Y) =
        Real.sqrt A * Real.sqrt B *
          (Real.sqrt (T ^ ε) * Real.sqrt (T ^ ε)) *
          Real.sqrt X * Real.sqrt Y := by ring
    _ = _ := by rw [hsqrtPow]

/-- Sections 7 and 8 assembled without suppressing the selected block,
logarithmic pigeonhole, or finite far-frequency error. -/
theorem gmCubicS3_prop8_1_explicit
    (cutoff : GMSmoothCutoff) (ε η : ℝ)
    (hε : 0 < ε) (hηpos : 0 < η) (hηupper : η ≤ 2 / 3) :
    ∃ K C : ℝ, 0 < K ∧ 0 < C ∧
      ∀ {T : ℝ} {N : ℕ} {W : Finset ℝ},
      1 ≤ T → 0 < N → (N : ℝ) ≤ T →
      T ^ (2 / 3 : ℝ) ≤ (N : ℝ) →
      IsSeparated 1 W → InBaseInterval T W →
      ∃ p ∈ gmCubicDyadicIndexPairs (gmCubicFrequencyRadius η T N),
        ‖gmCubicS3 cutoff N W‖ ≤
          6 * (((Nat.log 2 (gmCubicFrequencyRadius η T N) + 1 : ℕ) : ℝ)) ^ 2 *
            (2000 * C * T ^ η * (N : ℝ) ^ 2 * (2 ^ p.2 : ℕ) ^ 2 *
                Real.sqrt 2 *
                Real.sqrt (gmCubicL2Constant ε * T ^ ε * (W.card : ℝ)) *
                Real.sqrt (gmCubicFourthConstant ε * T ^ ε *
                  (ApproxAddEnergy 1 W : ℝ)) +
              ((gmCubicDyadicFrequencyBlock
                (gmCubicFrequencyRadius η T N) p.1 p.2).card : ℝ) *
                (C / T ^ 200)) +
            K / T ^ 100 := by
  obtain ⟨K, C, hK, hC, hprop7⟩ :=
    gmCubicS3_prop7_2_explicit cutoff η hηpos hηupper
  refine ⟨K, C, hK, hC, ?_⟩
  intro T N W hT hN hNT hNlower hSep hBase
  obtain ⟨p, hp, hpbound⟩ := hprop7 hT hN hNT hNlower hSep hBase
  have hpMem := mem_gmCubicDyadicIndexPairs.mp hp
  have hM : 0 < 2 ^ p.2 := by positivity
  have hB := gmCubicSmoothingScale_pos (η := η)
    (lt_of_lt_of_le zero_lt_one hT) hN hM
  have hsum := sum_gmCubicSmoothedModeIntegral_prop8_1
    (H := gmCubicFrequencyRadius η T N) (M := 2 ^ p.2)
    hε hT hSep hBase hpMem.2.2 hB
  refine ⟨p, hp, hpbound.trans ?_⟩
  have hcoeff : 0 ≤ C * T ^ η * (N : ℝ) ^ 2 / (2 ^ p.2 : ℕ) := by
    positivity
  have hmain : C * T ^ η * (N : ℝ) ^ 2 / (2 ^ p.2 : ℕ) *
          (∑ m ∈ gmCubicDyadicFrequencyBlock
            (gmCubicFrequencyRadius η T N) p.1 p.2,
            gmCubicSmoothedModeIntegral η T N (2 ^ p.2) W m) ≤
      2000 * C * T ^ η * (N : ℝ) ^ 2 * (2 ^ p.2 : ℕ) ^ 2 *
        Real.sqrt 2 *
        Real.sqrt (gmCubicL2Constant ε * T ^ ε * (W.card : ℝ)) *
        Real.sqrt (gmCubicFourthConstant ε * T ^ ε *
          (ApproxAddEnergy 1 W : ℝ)) := by
    calc
      C * T ^ η * (N : ℝ) ^ 2 / (2 ^ p.2 : ℕ) *
            (∑ m ∈ gmCubicDyadicFrequencyBlock
              (gmCubicFrequencyRadius η T N) p.1 p.2,
              gmCubicSmoothedModeIntegral η T N (2 ^ p.2) W m) ≤
        C * T ^ η * (N : ℝ) ^ 2 / (2 ^ p.2 : ℕ) *
          ((2000 : ℝ) * (2 ^ p.2 : ℕ) ^ 3 * Real.sqrt 2 *
            Real.sqrt (gmCubicL2Constant ε * T ^ ε * (W.card : ℝ)) *
            Real.sqrt (gmCubicFourthConstant ε * T ^ ε *
              (ApproxAddEnergy 1 W : ℝ))) := by gcongr
      _ = 2000 * C * T ^ η * (N : ℝ) ^ 2 * (2 ^ p.2 : ℕ) ^ 2 *
          Real.sqrt 2 *
          Real.sqrt (gmCubicL2Constant ε * T ^ ε * (W.card : ℝ)) *
          Real.sqrt (gmCubicFourthConstant ε * T ^ ε *
            (ApproxAddEnergy 1 W : ℝ)) := by
        have hMreal : ((2 ^ p.2 : ℕ) : ℝ) ≠ 0 := by positivity
        field_simp [hMreal]
  have hlog0 : 0 ≤
      6 * (((Nat.log 2 (gmCubicFrequencyRadius η T N) + 1 : ℕ) : ℝ)) ^ 2 := by
    positivity
  have herr :
      C * T ^ η * (N : ℝ) ^ 2 / (2 ^ p.2 : ℕ) *
            (∑ m ∈ gmCubicDyadicFrequencyBlock
              (gmCubicFrequencyRadius η T N) p.1 p.2,
              gmCubicSmoothedModeIntegral η T N (2 ^ p.2) W m) +
          (gmCubicDyadicFrequencyBlock
            (gmCubicFrequencyRadius η T N) p.1 p.2).card * (C / T ^ 200) ≤
        2000 * C * T ^ η * (N : ℝ) ^ 2 * (2 ^ p.2 : ℕ) ^ 2 *
            Real.sqrt 2 *
            Real.sqrt (gmCubicL2Constant ε * T ^ ε * (W.card : ℝ)) *
            Real.sqrt (gmCubicFourthConstant ε * T ^ ε *
              (ApproxAddEnergy 1 W : ℝ)) +
          (gmCubicDyadicFrequencyBlock
            (gmCubicFrequencyRadius η T N) p.1 p.2).card * (C / T ^ 200) :=
    add_le_add hmain (le_refl _)
  have hmul := mul_le_mul_of_nonneg_left herr hlog0
  exact add_le_add hmul (le_refl _)

/-- Guth--Maynard Proposition 8.1 with the selected dyadic scale eliminated.
The only losses not yet absorbed into a final arbitrary epsilon are the
displayed `(log T)²`, the chosen smoothing exponent `η`, and the moment
epsilon.  The finite Poisson tail remains quantitative. -/
theorem gmCubicS3_prop8_1_physical_explicit
    (cutoff : GMSmoothCutoff) (ε η : ℝ)
    (hε : 0 < ε) (hηpos : 0 < η) (hηupper : η ≤ 2 / 3) :
    ∃ K C : ℝ, 0 < K ∧ 0 < C ∧
      ∀ {T : ℝ} {N : ℕ} {W : Finset ℝ},
      Real.exp 1 ≤ T → 0 < N → (N : ℝ) ≤ T →
      T ^ (2 / 3 : ℝ) ≤ (N : ℝ) →
      IsSeparated 1 W → InBaseInterval T W →
      ‖gmCubicS3 cutoff N W‖ ≤
        1728000 * C * Real.sqrt 2 *
          Real.sqrt (gmCubicL2Constant ε) *
          Real.sqrt (gmCubicFourthConstant ε) *
          (Real.log T) ^ 2 * T ^ (2 + 3 * η + ε) *
          Real.sqrt (W.card : ℝ) *
          Real.sqrt (ApproxAddEnergy 1 W : ℝ) +
        27000 * C * (Real.log T) ^ 2 * T ^ 5 / T ^ 200 +
        K / T ^ 100 := by
  obtain ⟨K, C, hK, hC, hprop⟩ :=
    gmCubicS3_prop8_1_explicit cutoff ε η hε hηpos hηupper
  refine ⟨K, C, hK, hC, ?_⟩
  intro T N W hT hN hNT hNlower hSep hBase
  have hTone : 1 ≤ T := by
    calc
      (1 : ℝ) = Real.exp 0 := by rw [Real.exp_zero]
      _ ≤ Real.exp 1 := Real.exp_le_exp.mpr (by norm_num)
      _ ≤ T := hT
  have hTpos : 0 < T := zero_lt_one.trans_le hTone
  obtain ⟨p, hp, hpbound⟩ := hprop hTone hN hNT hNlower hSep hBase
  have hscale := natCast_sq_mul_twoPow_second_dyadicIndex_sq_le
    hTone hηpos.le hN hNT hp
  have hlog := gmCubicDyadicLogFactor_sq_le_realLog_sq
    hT hηpos.le hηupper hN hNT
  have hcard := card_gmCubicDyadicFrequencyBlock_sourceRadius_le
    (r := p.1) (s := p.2) hTone hηpos.le hηupper hN
  have hsqrt :
      Real.sqrt (gmCubicL2Constant ε * T ^ ε * (W.card : ℝ)) *
          Real.sqrt (gmCubicFourthConstant ε * T ^ ε *
            (ApproxAddEnergy 1 W : ℝ)) =
        Real.sqrt (gmCubicL2Constant ε) *
          Real.sqrt (gmCubicFourthConstant ε) * T ^ ε *
          Real.sqrt (W.card : ℝ) *
          Real.sqrt (ApproxAddEnergy 1 W : ℝ) :=
    sqrt_epsilon_moment_product_eq
      (gmCubicL2Constant_pos hε).le (gmCubicFourthConstant_pos hε).le hTpos.le
  have hpow : T ^ η * T ^ (2 * (1 + η)) * T ^ ε =
      T ^ (2 + 3 * η + ε) := by
    calc
      T ^ η * T ^ (2 * (1 + η)) * T ^ ε =
          T ^ (η + 2 * (1 + η)) * T ^ ε := by
            rw [← Real.rpow_add hTpos]
      _ = T ^ ((η + 2 * (1 + η)) + ε) := by
            rw [← Real.rpow_add hTpos]
      _ = T ^ (2 + 3 * η + ε) := by ring_nf
  let main : ℝ :=
    2000 * C * T ^ η * (N : ℝ) ^ 2 * (2 ^ p.2 : ℕ) ^ 2 *
      Real.sqrt 2 *
      Real.sqrt (gmCubicL2Constant ε * T ^ ε * (W.card : ℝ)) *
      Real.sqrt (gmCubicFourthConstant ε * T ^ ε *
        (ApproxAddEnergy 1 W : ℝ))
  let err : ℝ :=
    ((gmCubicDyadicFrequencyBlock
      (gmCubicFrequencyRadius η T N) p.1 p.2).card : ℝ) * (C / T ^ 200)
  have hmain :
      6 * (((Nat.log 2 (gmCubicFrequencyRadius η T N) + 1 : ℕ) : ℝ)) ^ 2 * main ≤
        1728000 * C * Real.sqrt 2 *
          Real.sqrt (gmCubicL2Constant ε) *
          Real.sqrt (gmCubicFourthConstant ε) *
          (Real.log T) ^ 2 * T ^ (2 + 3 * η + ε) *
          Real.sqrt (W.card : ℝ) *
          Real.sqrt (ApproxAddEnergy 1 W : ℝ) := by
    dsimp only [main]
    have hscaledMain :
        2000 * C * T ^ η *
            ((N : ℝ) ^ 2 * ((2 ^ p.2 : ℕ) : ℝ) ^ 2) * Real.sqrt 2 *
            Real.sqrt (gmCubicL2Constant ε * T ^ ε * (W.card : ℝ)) *
            Real.sqrt (gmCubicFourthConstant ε * T ^ ε *
              (ApproxAddEnergy 1 W : ℝ)) ≤
          2000 * C * T ^ η * (4 * T ^ (2 * (1 + η))) * Real.sqrt 2 *
            Real.sqrt (gmCubicL2Constant ε * T ^ ε * (W.card : ℝ)) *
            Real.sqrt (gmCubicFourthConstant ε * T ^ ε *
              (ApproxAddEnergy 1 W : ℝ)) := by
      gcongr
    have hproduct :
        (((Nat.log 2 (gmCubicFrequencyRadius η T N) + 1 : ℕ) : ℝ)) ^ 2 *
            (2000 * C * T ^ η *
              ((N : ℝ) ^ 2 * ((2 ^ p.2 : ℕ) : ℝ) ^ 2) * Real.sqrt 2 *
              Real.sqrt (gmCubicL2Constant ε * T ^ ε * (W.card : ℝ)) *
              Real.sqrt (gmCubicFourthConstant ε * T ^ ε *
                (ApproxAddEnergy 1 W : ℝ))) ≤
          (36 * (Real.log T) ^ 2) *
            (2000 * C * T ^ η * (4 * T ^ (2 * (1 + η))) * Real.sqrt 2 *
              Real.sqrt (gmCubicL2Constant ε * T ^ ε * (W.card : ℝ)) *
              Real.sqrt (gmCubicFourthConstant ε * T ^ ε *
                (ApproxAddEnergy 1 W : ℝ))) :=
      mul_le_mul hlog hscaledMain (by positivity) (by positivity)
    calc
      _ = 6 *
          ((((Nat.log 2 (gmCubicFrequencyRadius η T N) + 1 : ℕ) : ℝ)) ^ 2 *
            (2000 * C * T ^ η *
              ((N : ℝ) ^ 2 * ((2 ^ p.2 : ℕ) : ℝ) ^ 2) * Real.sqrt 2 *
              Real.sqrt (gmCubicL2Constant ε * T ^ ε * (W.card : ℝ)) *
              Real.sqrt (gmCubicFourthConstant ε * T ^ ε *
                (ApproxAddEnergy 1 W : ℝ)))) := by ring
      _ ≤ 6 * ((36 * (Real.log T) ^ 2) *
          (2000 * C * T ^ η * (4 * T ^ (2 * (1 + η))) *
            Real.sqrt 2 *
            Real.sqrt (gmCubicL2Constant ε * T ^ ε * (W.card : ℝ)) *
            Real.sqrt (gmCubicFourthConstant ε * T ^ ε *
              (ApproxAddEnergy 1 W : ℝ)))) := by gcongr
      _ = 1728000 * C * Real.sqrt 2 * (Real.log T) ^ 2 *
          (T ^ η * T ^ (2 * (1 + η))) *
          (Real.sqrt (gmCubicL2Constant ε * T ^ ε * (W.card : ℝ)) *
            Real.sqrt (gmCubicFourthConstant ε * T ^ ε *
              (ApproxAddEnergy 1 W : ℝ))) := by ring
      _ = 1728000 * C * Real.sqrt 2 * (Real.log T) ^ 2 *
          (T ^ η * T ^ (2 * (1 + η))) *
          (Real.sqrt (gmCubicL2Constant ε) *
            Real.sqrt (gmCubicFourthConstant ε) * T ^ ε *
            Real.sqrt (W.card : ℝ) *
            Real.sqrt (ApproxAddEnergy 1 W : ℝ)) := by rw [hsqrt]
      _ = _ := by
        calc
          1728000 * C * Real.sqrt 2 * (Real.log T) ^ 2 *
              (T ^ η * T ^ (2 * (1 + η))) *
              (Real.sqrt (gmCubicL2Constant ε) *
                Real.sqrt (gmCubicFourthConstant ε) * T ^ ε *
                Real.sqrt (W.card : ℝ) *
                Real.sqrt (ApproxAddEnergy 1 W : ℝ)) =
            1728000 * C * Real.sqrt 2 *
              Real.sqrt (gmCubicL2Constant ε) *
              Real.sqrt (gmCubicFourthConstant ε) * (Real.log T) ^ 2 *
              ((T ^ η * T ^ (2 * (1 + η))) * T ^ ε) *
              Real.sqrt (W.card : ℝ) *
              Real.sqrt (ApproxAddEnergy 1 W : ℝ) := by ring
          _ = _ := by rw [hpow]
  have herr :
      6 * (((Nat.log 2 (gmCubicFrequencyRadius η T N) + 1 : ℕ) : ℝ)) ^ 2 * err ≤
        27000 * C * (Real.log T) ^ 2 * T ^ 5 / T ^ 200 := by
    dsimp only [err]
    calc
      _ ≤ 6 * (36 * (Real.log T) ^ 2) *
          ((125 * T ^ 5) * (C / T ^ 200)) := by
        gcongr
      _ = _ := by ring
  calc
    ‖gmCubicS3 cutoff N W‖ ≤
        6 * (((Nat.log 2 (gmCubicFrequencyRadius η T N) + 1 : ℕ) : ℝ)) ^ 2 *
          (main + err) + K / T ^ 100 := by
      simpa only [main, err] using hpbound
    _ = 6 * (((Nat.log 2 (gmCubicFrequencyRadius η T N) + 1 : ℕ) : ℝ)) ^ 2 *
          main +
        6 * (((Nat.log 2 (gmCubicFrequencyRadius η T N) + 1 : ℕ) : ℝ)) ^ 2 *
          err + K / T ^ 100 := by ring
    _ ≤ _ := add_le_add (add_le_add hmain herr) (le_refl _)

/-- Guth--Maynard Proposition 8.1 in its final epsilon-power form.  The
The constant is uniform in `T`, `N`, the coefficients encoded by the source
cutoff, and the separated set `W`; the residual `T⁻⁹⁰` term is the summed
finite Poisson tail and is retained for the later cubic-trace assembly. -/
theorem gmEventuallyLogNatPower_le_rpow
    (B : ℕ) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ T : ℝ in Filter.atTop, (Real.log T) ^ B ≤ T ^ η := by
  have hLittle := isLittleO_log_rpow_rpow_atTop (B : ℝ) hη
  filter_upwards [hLittle.eventuallyLE, Filter.eventually_ge_atTop (1 : ℝ)] with T hBound hT
  have hLogNonneg : 0 ≤ Real.log T := Real.log_nonneg hT
  have hTNonneg : 0 ≤ T := by linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hLogNonneg _),
    Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hTNonneg _)] at hBound
  rw [← Real.rpow_natCast]
  exact hBound

theorem gmCubicS3_prop8_1_native
    (cutoff : GMSmoothCutoff) :
    ∀ ε : ℝ, 0 < ε →
      ∃ C T₀ : ℝ, 0 < C ∧ 1 ≤ T₀ ∧
        ∀ {T : ℝ} {N : ℕ} {W : Finset ℝ},
        T₀ ≤ T → 0 < N → (N : ℝ) ≤ T →
        T ^ (2 / 3 : ℝ) ≤ (N : ℝ) →
        IsSeparated 1 W → InBaseInterval T W →
        ‖gmCubicS3 cutoff N W‖ ≤
          C * T ^ (2 + ε) * Real.sqrt (W.card : ℝ) *
              Real.sqrt (ApproxAddEnergy 1 W : ℝ) +
            C / T ^ 90 := by
  intro ε hε
  let η : ℝ := min (ε / 12) (1 / 12)
  let μ : ℝ := ε / 4
  have hηpos : 0 < η := by
    dsimp only [η]
    exact lt_min (by positivity) (by norm_num)
  have hηupper : η ≤ 2 / 3 := by
    exact (min_le_right _ _).trans (by norm_num)
  have hηbudget : 3 * η ≤ ε / 4 := by
    have := min_le_left (ε / 12) (1 / 12)
    dsimp only [η]
    linarith
  have hμ : 0 < μ := by dsimp only [μ]; positivity
  obtain ⟨K, C₀, hK, hC₀, hphysical⟩ :=
    gmCubicS3_prop8_1_physical_explicit cutoff μ η hμ hηpos hηupper
  have hLogMainEventually := gmEventuallyLogNatPower_le_rpow 2 (ε / 2) (by positivity)
  have hLogTailEventually := gmEventuallyLogNatPower_le_rpow 2 1 (by norm_num)
  rw [Filter.eventually_atTop] at hLogMainEventually hLogTailEventually
  obtain ⟨Tmain, hTmain⟩ := hLogMainEventually
  obtain ⟨Ttail, hTtail⟩ := hLogTailEventually
  let T₀ : ℝ := max (Real.exp 1) (max Tmain Ttail)
  let A : ℝ := 1728000 * C₀ * Real.sqrt 2 *
    Real.sqrt (gmCubicL2Constant μ) * Real.sqrt (gmCubicFourthConstant μ)
  let B : ℝ := 27000 * C₀
  let C : ℝ := A + B + K
  have hA : 0 < A := by
    dsimp only [A]
    have hL := gmCubicL2Constant_pos hμ
    have hG := gmCubicFourthConstant_pos hμ
    positivity
  have hB : 0 < B := by dsimp only [B]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, T₀, hC, ?_, ?_⟩
  · exact le_trans (by norm_num : (1 : ℝ) ≤ Real.exp 1) (le_max_left _ _)
  intro T N W hT hN hNT hNlower hSep hBase
  have hTexp : Real.exp 1 ≤ T := (le_max_left _ _).trans hT
  have hTmain' : Tmain ≤ T := (le_max_left Tmain Ttail).trans
    ((le_max_right (Real.exp 1) (max Tmain Ttail)).trans hT)
  have hTtail' : Ttail ≤ T := (le_max_right Tmain Ttail).trans
    ((le_max_right (Real.exp 1) (max Tmain Ttail)).trans hT)
  have hTone : 1 ≤ T := by
    exact (show (1 : ℝ) ≤ Real.exp 1 by norm_num).trans hTexp
  have hTpos : 0 < T := zero_lt_one.trans_le hTone
  have hlogMain := hTmain T hTmain'
  have hlogTail := hTtail T hTtail'
  have hsource := hphysical hTexp hN hNT hNlower hSep hBase
  have hexpBudget : 2 + 3 * η + μ + ε / 2 ≤ 2 + ε := by
    dsimp only [μ]
    linarith
  have hpowerMain :
      (Real.log T) ^ 2 * T ^ (2 + 3 * η + μ) ≤ T ^ (2 + ε) := by
    calc
      (Real.log T) ^ 2 * T ^ (2 + 3 * η + μ) ≤
          T ^ (ε / 2) * T ^ (2 + 3 * η + μ) := by gcongr
      _ = T ^ ((ε / 2) + (2 + 3 * η + μ)) := by
        rw [← Real.rpow_add hTpos]
      _ ≤ T ^ (2 + ε) :=
        Real.rpow_le_rpow_of_exponent_le hTone (by linarith)
  have htailPower : (Real.log T) ^ 2 * T ^ 5 / T ^ 200 ≤ 1 / T ^ 90 := by
    have hnum : (Real.log T) ^ 2 * T ^ 5 ≤ T ^ 6 := by
      calc
        (Real.log T) ^ 2 * T ^ 5 ≤ T ^ (1 : ℝ) * T ^ 5 := by gcongr
        _ = T ^ 6 := by rw [Real.rpow_one, ← pow_succ']
    rw [div_le_div_iff₀ (pow_pos hTpos 200) (pow_pos hTpos 90)]
    calc
      ((Real.log T) ^ 2 * T ^ 5) * T ^ 90 ≤ T ^ 6 * T ^ 90 := by gcongr
      _ = T ^ 96 := by rw [← pow_add]
      _ ≤ T ^ 200 := pow_le_pow_right₀ hTone (by omega)
      _ = 1 * T ^ 200 := by ring
  have htail100 : 1 / T ^ 100 ≤ 1 / T ^ 90 := by
    rw [one_div, one_div]
    exact inv_anti₀ (pow_pos hTpos 90)
      (pow_le_pow_right₀ hTone (by omega : 90 ≤ 100))
  have hroots0 : 0 ≤ Real.sqrt (W.card : ℝ) *
      Real.sqrt (ApproxAddEnergy 1 W : ℝ) := by positivity
  have hmain :
      A * (Real.log T) ^ 2 * T ^ (2 + 3 * η + μ) *
          Real.sqrt (W.card : ℝ) * Real.sqrt (ApproxAddEnergy 1 W : ℝ) ≤
        C * T ^ (2 + ε) * Real.sqrt (W.card : ℝ) *
          Real.sqrt (ApproxAddEnergy 1 W : ℝ) := by
    have hAC : A ≤ C := by dsimp only [C]; linarith [hB.le, hK.le]
    have hcore : A * ((Real.log T) ^ 2 * T ^ (2 + 3 * η + μ)) ≤
        C * T ^ (2 + ε) := by
      exact (mul_le_mul_of_nonneg_left hpowerMain hA.le).trans
        (mul_le_mul_of_nonneg_right hAC (Real.rpow_nonneg hTpos.le _))
    calc
      _ = (A * ((Real.log T) ^ 2 * T ^ (2 + 3 * η + μ))) *
          (Real.sqrt (W.card : ℝ) *
            Real.sqrt (ApproxAddEnergy 1 W : ℝ)) := by ring
      _ ≤ (C * T ^ (2 + ε)) *
          (Real.sqrt (W.card : ℝ) *
            Real.sqrt (ApproxAddEnergy 1 W : ℝ)) :=
        mul_le_mul_of_nonneg_right hcore hroots0
      _ = _ := by ring
  have htail :
      B * (Real.log T) ^ 2 * T ^ 5 / T ^ 200 + K / T ^ 100 ≤ C / T ^ 90 := by
    have hBtail := mul_le_mul_of_nonneg_left htailPower hB.le
    have hKtail := mul_le_mul_of_nonneg_left htail100 hK.le
    calc
      B * (Real.log T) ^ 2 * T ^ 5 / T ^ 200 + K / T ^ 100 =
          B * ((Real.log T) ^ 2 * T ^ 5 / T ^ 200) + K / T ^ 100 := by ring
      _ ≤ B * (1 / T ^ 90) + K * (1 / T ^ 90) := by
        exact add_le_add hBtail (by simpa [div_eq_mul_inv] using hKtail)
      _ ≤ (A + B + K) * (1 / T ^ 90) := by
        have hInv0 : 0 ≤ 1 / T ^ 90 := by positivity
        nlinarith [mul_nonneg hA.le hInv0]
      _ = C / T ^ 90 := by dsimp only [C]; ring
  calc
    ‖gmCubicS3 cutoff N W‖ ≤
        A * (Real.log T) ^ 2 * T ^ (2 + 3 * η + μ) *
            Real.sqrt (W.card : ℝ) *
            Real.sqrt (ApproxAddEnergy 1 W : ℝ) +
          B * (Real.log T) ^ 2 * T ^ 5 / T ^ 200 + K / T ^ 100 := by
      simpa only [A, B] using hsource
    _ = A * (Real.log T) ^ 2 * T ^ (2 + 3 * η + μ) *
          Real.sqrt (W.card : ℝ) *
          Real.sqrt (ApproxAddEnergy 1 W : ℝ) +
        (B * (Real.log T) ^ 2 * T ^ 5 / T ^ 200 + K / T ^ 100) := by ring
    _ ≤ C * T ^ (2 + ε) * Real.sqrt (W.card : ℝ) *
          Real.sqrt (ApproxAddEnergy 1 W : ℝ) + C / T ^ 90 :=
      add_le_add hmain htail

end RiemannZeta.GuthMaynard
