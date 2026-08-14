import RiemannZeta.GuthMaynard.DFIEquation24DoubleDual
import RiemannZeta.GuthMaynard.DFIEquation29
import RiemannZeta.GuthMaynard.DFIEquation30
import RiemannZeta.GuthMaynard.KloostermanComposite

/-!
# DFI equations (24)--(30): quantitative error assembly

This module estimates the eight non-main branches isolated by the exact
equation-(24) decomposition.  It keeps the complete Weil--Estermann factor
and the Mellin--Voronoi weights visible so that the source truncations from
equation (29) can be inserted without an assumed error certificate.
-/

open Complex Finset Set Filter Topology MeasureTheory
open scoped BigOperators Topology Interval ContDiff
open Classical

namespace RiemannZeta.GuthMaynard

/-- The elementary partial-sum estimate needed for DFI's retained dual
frequencies. -/
theorem sum_Icc_natCast_rpow_neg_quarter_le (L : ℕ) :
    ∑ n ∈ Finset.Icc 1 L, (n : ℝ) ^ (-(1 / 4 : ℝ)) ≤
      (4 / 3 : ℝ) * (L : ℝ) ^ (3 / 4 : ℝ) := by
  cases L with
  | zero => simp
  | succ K =>
      let f : ℝ → ℝ := fun x ↦ x ^ (-(1 / 4 : ℝ))
      have hanti : AntitoneOn f (Set.Icc 1 (1 + K)) := by
        exact (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by norm_num)).mono
          (fun x hx ↦ lt_of_lt_of_le zero_lt_one hx.1)
      have htail :
          ∑ j ∈ Finset.range K, f (1 + (j + 1 : ℕ)) ≤
            ∫ x in (1 : ℝ)..1 + K, f x := hanti.sum_le_integral
      have hzero : (0 : ℝ) ∉ [[(1 : ℝ), 1 + K]] := by
        rw [Set.uIcc_of_le
          (le_add_of_nonneg_right (Nat.cast_nonneg K) : (1 : ℝ) ≤ 1 + K)]
        intro hx
        linarith [hx.1]
      rw [integral_rpow (Or.inr ⟨by norm_num, hzero⟩)] at htail
      have hfinset : Finset.Icc 1 (K + 1) =
          insert 1 ((Finset.range K).image
            (fun j ↦ (1 + (j + 1) : ℕ))) := by
        ext n
        simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_image,
          Finset.mem_range]
        constructor
        · intro hn
          by_cases h1 : n = 1
          · exact Or.inl h1
          · right
            refine ⟨n - 2, by omega, by omega⟩
        · intro hn
          rcases hn with h1 | ⟨j, hj, rfl⟩
          · omega
          · omega
      have honeNot : 1 ∉ (Finset.range K).image
          (fun j ↦ (1 + (j + 1) : ℕ)) := by
        intro hmem
        rw [Finset.mem_image] at hmem
        rcases hmem with ⟨j, _, hj⟩
        omega
      have hinj : Function.Injective (fun j : ℕ ↦ (1 + (j + 1) : ℕ)) := by
        intro x y hxy
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hxy
      rw [hfinset, Finset.sum_insert honeNot, Finset.sum_image] 
      · dsimp [f] at htail ⊢
        norm_num at htail ⊢
        calc
          _ ≤ 1 + (((1 + (K : ℝ)) ^ (3 / 4 : ℝ) - 1) /
                (3 / 4 : ℝ)) := by linarith
          _ ≤ (4 / 3 : ℝ) * (1 + (K : ℝ)) ^ (3 / 4 : ℝ) := by
            ring_nf
            norm_num
          _ = (4 / 3 : ℝ) * ((K : ℝ) + 1) ^ (3 / 4 : ℝ) := by
            congr 2
            ring
      · intro x _ y _ hxy
        exact hinj hxy

/-- A complete Kloosterman coefficient may be pulled uniformly through one
absolutely convergent dual Voronoi series. -/
theorem norm_tsum_kloostermanSumZMod_mul_dfiVoronoiDualTerm_le
    (q r : ℕ) [NeZero q] [NeZero r] (A : ZMod q)
    (frequency : ℕ → ZMod q) (branch : DFIVoronoiDualBranch)
    (g : ℝ → ℂ) :
    ‖∑' n : ℕ, kloostermanSumZMod q A (frequency n) *
        dfiVoronoiDualTerm r branch g n‖ ≤
      (Real.sqrt (Nat.gcd A.val q) * Real.sqrt q *
          (q.divisors.card : ℝ)) *
        ∑' n : ℕ, ‖dfiVoronoiDualTerm r branch g n‖ := by
  let B : ℝ := Real.sqrt (Nat.gcd A.val q) * Real.sqrt q *
    (q.divisors.card : ℝ)
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hDual := summable_norm_dfiVoronoiDualTerm r branch g
  have hScaled : Summable (fun n : ℕ =>
      B * ‖dfiVoronoiDualTerm r branch g n‖) := hDual.mul_left B
  have hPoint (n : ℕ) :
      ‖kloostermanSumZMod q A (frequency n) *
          dfiVoronoiDualTerm r branch g n‖ ≤
        B * ‖dfiVoronoiDualTerm r branch g n‖ := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right
      (norm_kloostermanSumZMod_le_first_gcd q A (frequency n))
      (norm_nonneg _)
  have hSeries : Summable (fun n : ℕ =>
      kloostermanSumZMod q A (frequency n) *
        dfiVoronoiDualTerm r branch g n) := by
    apply Summable.of_norm_bounded hScaled
    exact hPoint
  calc
    ‖∑' n : ℕ, kloostermanSumZMod q A (frequency n) *
        dfiVoronoiDualTerm r branch g n‖ ≤
      ∑' n : ℕ, ‖kloostermanSumZMod q A (frequency n) *
        dfiVoronoiDualTerm r branch g n‖ :=
      norm_tsum_le_tsum_norm hSeries.norm
    _ ≤ ∑' n : ℕ, B * ‖dfiVoronoiDualTerm r branch g n‖ :=
      hSeries.norm.tsum_le_tsum hPoint hScaled
    _ = B * ∑' n : ℕ, ‖dfiVoronoiDualTerm r branch g n‖ := by
      rw [tsum_mul_left]

/-- A complete Kloosterman coefficient may be pulled uniformly through an
absolutely convergent source-ordered double-frequency series. -/
theorem norm_dfiEquation24DualDualKloosterman_le
    (q a b : ℕ) [NeZero q] (h : ℤ)
    (xSign ySign : DFIVoronoiFrequencySign)
    (amplitude : ℕ → ℕ → ℂ)
    (hRight : ∀ m, Summable (fun n ↦ ‖amplitude m n‖))
    (hOuter : Summable (fun m ↦ ∑' n, ‖amplitude m n‖)) :
    ‖dfiEquation24DualDualKloosterman
        q a b h xSign ySign amplitude‖ ≤
      (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
          (q.divisors.card : ℝ)) *
        ∑' m : ℕ, ∑' n : ℕ, ‖amplitude m n‖ := by
  let B : ℝ := Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) *
    Real.sqrt q * (q.divisors.card : ℝ)
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hPoint (m n : ℕ) :
      ‖kloostermanSumZMod q (-h : ZMod q)
          (dfiSignedFrequency xSign (dfiLiftedInverseFrequency a q m) +
            dfiSignedFrequency ySign (dfiLiftedInverseFrequency b q n)) *
        amplitude m n‖ ≤ B * ‖amplitude m n‖ := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right
      (norm_kloostermanSumZMod_le_first_gcd q (-h : ZMod q) _)
      (norm_nonneg _)
  have hInner (m : ℕ) : Summable (fun n : ℕ ↦
      kloostermanSumZMod q (-h : ZMod q)
          (dfiSignedFrequency xSign (dfiLiftedInverseFrequency a q m) +
            dfiSignedFrequency ySign (dfiLiftedInverseFrequency b q n)) *
        amplitude m n) := by
    apply Summable.of_norm_bounded ((hRight m).mul_left B)
    exact hPoint m
  have hInnerNorm (m : ℕ) :
      ‖∑' n : ℕ,
        kloostermanSumZMod q (-h : ZMod q)
            (dfiSignedFrequency xSign (dfiLiftedInverseFrequency a q m) +
              dfiSignedFrequency ySign (dfiLiftedInverseFrequency b q n)) *
          amplitude m n‖ ≤
        B * ∑' n : ℕ, ‖amplitude m n‖ := by
    calc
      _ ≤ ∑' n : ℕ,
          ‖kloostermanSumZMod q (-h : ZMod q)
              (dfiSignedFrequency xSign (dfiLiftedInverseFrequency a q m) +
                dfiSignedFrequency ySign (dfiLiftedInverseFrequency b q n)) *
            amplitude m n‖ := norm_tsum_le_tsum_norm (hInner m).norm
      _ ≤ ∑' n : ℕ, B * ‖amplitude m n‖ :=
        (hInner m).norm.tsum_le_tsum (hPoint m) ((hRight m).mul_left B)
      _ = B * ∑' n : ℕ, ‖amplitude m n‖ := by
        rw [tsum_mul_left]
  have hSeries : Summable (fun m : ℕ ↦ ∑' n : ℕ,
      kloostermanSumZMod q (-h : ZMod q)
          (dfiSignedFrequency xSign (dfiLiftedInverseFrequency a q m) +
            dfiSignedFrequency ySign (dfiLiftedInverseFrequency b q n)) *
        amplitude m n) := by
    apply Summable.of_norm_bounded (hOuter.mul_left B)
    exact hInnerNorm
  unfold dfiEquation24DualDualKloosterman
  calc
    _ ≤ ∑' m : ℕ, ‖∑' n : ℕ,
        kloostermanSumZMod q (-h : ZMod q)
            (dfiSignedFrequency xSign (dfiLiftedInverseFrequency a q m) +
              dfiSignedFrequency ySign (dfiLiftedInverseFrequency b q n)) *
          amplitude m n‖ := norm_tsum_le_tsum_norm hSeries.norm
    _ ≤ ∑' m : ℕ, B * ∑' n : ℕ, ‖amplitude m n‖ :=
      hSeries.norm.tsum_le_tsum hInnerNorm (hOuter.mul_left B)
    _ = B * ∑' m : ℕ, ∑' n : ℕ, ‖amplitude m n‖ := by
      rw [tsum_mul_left]

/-- The single transformed `x` branch has exactly the Weil factor times the
absolute dual Voronoi mass. -/
theorem norm_dfiEquation24XDualContribution_le
    (q a : ℕ) [NeZero q] (h : ℤ) (branch : DFIVoronoiDualBranch)
    (g : ℝ → ℂ) :
    ‖dfiEquation24XDualContribution q a h branch g‖ ≤
      (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
          (q.divisors.card : ℝ)) *
        ∑' n : ℕ,
          ‖dfiVoronoiDualTerm (dfiReducedModulus a q).denominator
            branch g n‖ := by
  rw [dfiEquation24XDualContribution_eq]
  exact norm_tsum_kloostermanSumZMod_mul_dfiVoronoiDualTerm_le
    q (dfiReducedModulus a q).denominator (-h : ZMod q)
    (fun n => dfiSignedFrequency branch.xSign
      (dfiLiftedInverseFrequency a q n)) branch g

/-- The symmetric single transformed `y` branch, including the reversed
source character, has the same Weil majorant. -/
theorem norm_dfiEquation24YDualContribution_le
    (q b : ℕ) [NeZero q] (h : ℤ) (branch : DFIVoronoiDualBranch)
    (g : ℝ → ℂ) :
    ‖dfiEquation24YDualContribution q b h branch g‖ ≤
      (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
          (q.divisors.card : ℝ)) *
        ∑' n : ℕ,
          ‖dfiVoronoiDualTerm (dfiReducedModulus b q).denominator
            branch g n‖ := by
  rw [dfiEquation24YDualContribution_eq]
  exact norm_tsum_kloostermanSumZMod_mul_dfiVoronoiDualTerm_le
    q (dfiReducedModulus b q).denominator (-h : ZMod q)
    (fun n => dfiSignedFrequency branch.ySign
      (dfiLiftedInverseFrequency b q n)) branch g

/-- The literal double-dual branch of equation (24) is bounded by the full
Weil factor times the absolutely convergent Mellin-amplitude mass. -/
theorem norm_dfiEquation24ActualDualDualContribution_le
    {E : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hA : 0 < A) (hAB : A ≤ B) (hC : 0 < C) (hCD : C ≤ D)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D)
    (q a b : ℕ) [NeZero q] (h : ℤ)
    (xBranch yBranch : DFIVoronoiDualBranch) :
    ‖dfiEquation24ActualDualDualContribution
        q a b h xBranch yBranch E‖ ≤
      (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
          (q.divisors.card : ℝ)) *
        ∑' m : ℕ, ∑' n : ℕ,
          ‖dfiEquation24DoubleDualMellinAmplitude
            (dfiReducedModulus a q).denominator xBranch
            (dfiReducedModulus b q).denominator yBranch E m n‖ := by
  rw [dfiEquation24ActualDualDualContribution_eq_kloosterman
    hE hA hAB hC hCD hSupport q a b h xBranch yBranch]
  exact norm_dfiEquation24DualDualKloosterman_le
    q a b h xBranch.xSign yBranch.ySign
      (dfiEquation24DoubleDualMellinAmplitude
        (dfiReducedModulus a q).denominator xBranch
        (dfiReducedModulus b q).denominator yBranch E)
    (fun m ↦
      summable_norm_dfiEquation24DoubleDualMellinAmplitude_right
        (E := E) (dfiReducedModulus a q).denominator xBranch
        (dfiReducedModulus b q).denominator yBranch m)
    (summable_tsum_norm_dfiEquation24DoubleDualMellinAmplitude
      (E := E) (dfiReducedModulus a q).denominator xBranch
      (dfiReducedModulus b q).denominator yBranch)

/-- The literal eight non-main terms in DFI equation (24) are bounded by
the two one-sided transformed families and the four double-transformed
families.  This is the source-facing bridge from the exact branch expansion
to the analytic estimates in equations (29) and (30). -/
theorem norm_dfiEquation24ReducedError_le_single_add_double
    {E : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hA : 0 < A) (hC : 0 < C) (hCD : C ≤ D)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D)
    (q a b : ℕ) [NeZero q] (h : ℤ) :
    ‖dfiEquation24ReducedError q a b h E‖ ≤
      (∑ branch : DFIVoronoiDualBranch,
        ‖dfiEquation24XDualContribution q a h branch
          (fun x ↦ dfiVoronoiMainTerm
            (dfiReducedModulus b q).denominator (E x))‖) +
      (∑ branch : DFIVoronoiDualBranch,
        ‖dfiEquation24YDualContribution q b h branch
          (fun y ↦ dfiVoronoiMainTerm
            (dfiReducedModulus a q).denominator (fun x ↦ E x y))‖) +
      ∑ yBranch : DFIVoronoiDualBranch,
        ∑ xBranch : DFIVoronoiDualBranch,
          ‖dfiEquation24ActualDualDualContribution
            q a b h xBranch yBranch E‖ := by
  calc
    ‖dfiEquation24ReducedError q a b h E‖ ≤
        ∑ yBranch : DFIVoronoiBranch, ∑ xBranch : DFIVoronoiBranch,
          if xBranch = .mainTerm ∧ yBranch = .mainTerm then 0 else
            ‖dfiEquation24ReducedBranchContribution
              q a b h xBranch yBranch E‖ :=
      norm_dfiEquation24ReducedError_le q a b h E
    _ = _ := by
      have hBranches : (Finset.univ : Finset DFIVoronoiBranch) =
          {DFIVoronoiBranch.mainTerm, DFIVoronoiBranch.minusTerm,
            DFIVoronoiBranch.plusTerm} := by
        ext branch
        fin_cases branch <;> simp
      have hDualBranches : (Finset.univ : Finset DFIVoronoiDualBranch) =
          {DFIVoronoiDualBranch.minusTerm,
            DFIVoronoiDualBranch.plusTerm} := by
        ext branch
        fin_cases branch <;> simp
      rw [hBranches, hDualBranches]
      simp only [Finset.sum_insert, Finset.sum_singleton,
        Finset.mem_insert, Finset.mem_singleton, reduceCtorEq,
        or_false, not_false_eq_true, true_and, false_and, ite_true,
        ite_false]
      have hxMinus := dfiEquation24ReducedBranchContribution_dual_main
        q a b h DFIVoronoiDualBranch.minusTerm E
      have hxPlus := dfiEquation24ReducedBranchContribution_dual_main
        q a b h DFIVoronoiDualBranch.plusTerm E
      have hyMinus := dfiEquation24ReducedBranchContribution_main_dual
        q a b h DFIVoronoiDualBranch.minusTerm E hE hA hC hCD hSupport
      have hyPlus := dfiEquation24ReducedBranchContribution_main_dual
        q a b h DFIVoronoiDualBranch.plusTerm E hE hA hC hCD hSupport
      have hmm := dfiEquation24ReducedBranchContribution_dual_dual
        q a b h DFIVoronoiDualBranch.minusTerm
          DFIVoronoiDualBranch.minusTerm E
      have hpm := dfiEquation24ReducedBranchContribution_dual_dual
        q a b h DFIVoronoiDualBranch.plusTerm
          DFIVoronoiDualBranch.minusTerm E
      have hmp := dfiEquation24ReducedBranchContribution_dual_dual
        q a b h DFIVoronoiDualBranch.minusTerm
          DFIVoronoiDualBranch.plusTerm E
      have hpp := dfiEquation24ReducedBranchContribution_dual_dual
        q a b h DFIVoronoiDualBranch.plusTerm
          DFIVoronoiDualBranch.plusTerm E
      simp only [DFIVoronoiDualBranch.toBranch] at hxMinus hxPlus hyMinus hyPlus hmm hpm hmp hpp
      rw [hxMinus, hxPlus, hyMinus, hyPlus, hmm, hpm, hmp, hpp]
      ring

/-- Absolute mass of the two `x`-dual/`y`-main terms in DFI (24). -/
noncomputable def dfiEquation24XSingleDualMass
    (q a b : ℕ) [NeZero q] (E : ℝ → ℝ → ℂ) : ℝ :=
  ∑ branch : DFIVoronoiDualBranch,
    ∑' n : ℕ,
      ‖dfiVoronoiDualTerm (dfiReducedModulus a q).denominator branch
        (fun x ↦ dfiVoronoiMainTerm
          (dfiReducedModulus b q).denominator (E x)) n‖

/-- Absolute mass of the two `x`-main/`y`-dual terms in DFI (24). -/
noncomputable def dfiEquation24YSingleDualMass
    (q a b : ℕ) [NeZero q] (E : ℝ → ℝ → ℂ) : ℝ :=
  ∑ branch : DFIVoronoiDualBranch,
    ∑' n : ℕ,
      ‖dfiVoronoiDualTerm (dfiReducedModulus b q).denominator branch
        (fun y ↦ dfiVoronoiMainTerm
          (dfiReducedModulus a q).denominator (fun x ↦ E x y)) n‖

/-- Absolute two-variable Mellin mass of the four double-dual terms in
DFI (24). -/
noncomputable def dfiEquation24DoubleDualMass
    (q a b : ℕ) [NeZero q] (E : ℝ → ℝ → ℂ) : ℝ :=
  ∑ yBranch : DFIVoronoiDualBranch,
    ∑ xBranch : DFIVoronoiDualBranch,
      ∑' m : ℕ, ∑' n : ℕ,
        ‖dfiEquation24DoubleDualMellinAmplitude
          (dfiReducedModulus a q).denominator xBranch
          (dfiReducedModulus b q).denominator yBranch E m n‖

/-- The complete equation-(24) error is the Weil--Estermann factor times
the sum of the two single-dual masses and the four double-dual masses. -/
theorem norm_dfiEquation24ReducedError_le_weil_mul_masses
    {E : ℝ → ℝ → ℂ} {A B C D : ℝ}
    (hE : ContDiff ℝ ∞ (Function.uncurry E))
    (hA : 0 < A) (hAB : A ≤ B) (hC : 0 < C) (hCD : C ≤ D)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc A B ×ˢ Set.Icc C D)
    (q a b : ℕ) [NeZero q] (h : ℤ) :
    ‖dfiEquation24ReducedError q a b h E‖ ≤
      (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
          (q.divisors.card : ℝ)) *
        (dfiEquation24XSingleDualMass q a b E +
          dfiEquation24YSingleDualMass q a b E +
          dfiEquation24DoubleDualMass q a b E) := by
  let K : ℝ := Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) *
    Real.sqrt q * (q.divisors.card : ℝ)
  have hSingle := norm_dfiEquation24ReducedError_le_single_add_double
    hE hA hC hCD hSupport q a b h
  calc
    ‖dfiEquation24ReducedError q a b h E‖ ≤
        (∑ branch : DFIVoronoiDualBranch,
          ‖dfiEquation24XDualContribution q a h branch
            (fun x ↦ dfiVoronoiMainTerm
              (dfiReducedModulus b q).denominator (E x))‖) +
        (∑ branch : DFIVoronoiDualBranch,
          ‖dfiEquation24YDualContribution q b h branch
            (fun y ↦ dfiVoronoiMainTerm
              (dfiReducedModulus a q).denominator (fun x ↦ E x y))‖) +
        ∑ yBranch : DFIVoronoiDualBranch,
          ∑ xBranch : DFIVoronoiDualBranch,
            ‖dfiEquation24ActualDualDualContribution
              q a b h xBranch yBranch E‖ := hSingle
    _ ≤
        (∑ branch : DFIVoronoiDualBranch,
          K * ∑' n : ℕ,
            ‖dfiVoronoiDualTerm (dfiReducedModulus a q).denominator branch
              (fun x ↦ dfiVoronoiMainTerm
                (dfiReducedModulus b q).denominator (E x)) n‖) +
        (∑ branch : DFIVoronoiDualBranch,
          K * ∑' n : ℕ,
            ‖dfiVoronoiDualTerm (dfiReducedModulus b q).denominator branch
              (fun y ↦ dfiVoronoiMainTerm
                (dfiReducedModulus a q).denominator (fun x ↦ E x y)) n‖) +
        ∑ yBranch : DFIVoronoiDualBranch,
          ∑ xBranch : DFIVoronoiDualBranch,
            K * ∑' m : ℕ, ∑' n : ℕ,
              ‖dfiEquation24DoubleDualMellinAmplitude
                (dfiReducedModulus a q).denominator xBranch
                (dfiReducedModulus b q).denominator yBranch E m n‖ := by
      apply add_le_add
      · apply add_le_add
        · apply Finset.sum_le_sum
          intro branch _hbranch
          simpa only [K] using
            norm_dfiEquation24XDualContribution_le q a h branch
              (fun x ↦ dfiVoronoiMainTerm
                (dfiReducedModulus b q).denominator (E x))
        · apply Finset.sum_le_sum
          intro branch _hbranch
          simpa only [K] using
            norm_dfiEquation24YDualContribution_le q b h branch
              (fun y ↦ dfiVoronoiMainTerm
                (dfiReducedModulus a q).denominator (fun x ↦ E x y))
      · apply Finset.sum_le_sum
        intro yBranch _hyBranch
        apply Finset.sum_le_sum
        intro xBranch _hxBranch
        simpa only [K] using
          norm_dfiEquation24ActualDualDualContribution_le
            hE hA hAB hC hCD hSupport q a b h xBranch yBranch
    _ = _ := by
      unfold dfiEquation24XSingleDualMass
        dfiEquation24YSingleDualMass dfiEquation24DoubleDualMass
      dsimp only [K]
      simp_rw [← Finset.mul_sum]
      ring

/-- Source specialization of the complete equation-(24) error bound.  All
smoothness, support, and positive-scale hypotheses are discharged from the
literal equation-(2)/(21)/(23) weight. -/
theorem norm_dfiEquation24_source_error_le_weil_mul_masses
    {Q P X Y U : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (h : ℤ)
    (q : ℕ) [NeZero q] (hq : 0 < q) :
    let E := dfiEquation23Weight w
      (dfiLocalizedWeight f φ h) a b h q
    ‖dfiEquation24ReducedError q a b h E‖ ≤
      (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
          (q.divisors.card : ℝ)) *
        (dfiEquation24XSingleDualMass q a b E +
          dfiEquation24YSingleDualMass q a b E +
          dfiEquation24DoubleDualMass q a b E) := by
  dsimp only
  have hE : ContDiff ℝ ∞ (Function.uncurry
      (dfiEquation23Weight w
        (dfiLocalizedWeight f φ h) a b h q)) :=
    contDiff_uncurry_dfiEquation23Weight w hf hφ a b h q hq
  have hSupport : Function.support (Function.uncurry
      (dfiEquation23Weight w
        (dfiLocalizedWeight f φ h) a b h q)) ⊆
      Set.Icc (X / a) (2 * X / a) ×ˢ
        Set.Icc (Y / b) (2 * Y / b) :=
    dfiEquation23Weight_support_rectangle w hbox a b ha hb h q
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  exact norm_dfiEquation24ReducedError_le_weil_mul_masses
    hE
    (div_pos (zero_lt_one.trans_le hf.one_le_X) haR)
    ((div_le_div_iff_of_pos_right haR).2 (by nlinarith [hf.one_le_X]))
    (div_pos (zero_lt_one.trans_le hf.one_le_Y) hbR)
    ((div_le_div_iff_of_pos_right hbR).2 (by nlinarith [hf.one_le_Y]))
    hSupport q a b h

/-- The dual Voronoi series has no zero-frequency term; DFI's transformed
sums begin at frequency one. -/
@[simp] theorem dfiVoronoiDualTerm_zero
    (q : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch)
    (g : ℝ → ℂ) :
    dfiVoronoiDualTerm q branch g 0 = 0 := by
  cases branch <;>
    simp [dfiVoronoiDualTerm, divisorWeight]

/-- Exact equation-(29) retained window. -/
noncomputable def dfiVoronoiDualMassUpTo
    (q : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch)
    (g : ℝ → ℂ) (L : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 L, ‖dfiVoronoiDualTerm q branch g n‖

/-- Exact equation-(29) tail beyond the retained window. -/
noncomputable def dfiVoronoiDualMassAfter
    (q : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch)
    (g : ℝ → ℂ) (L : ℕ) : ℝ :=
  ∑' j : ℕ, ‖dfiVoronoiDualTerm q branch g (L + (j + 1))‖

/-- Summed retained-frequency bound from the right-shifted equation-(29)
contour. -/
theorem DFIVoronoiTestFunction.exists_dfiVoronoiDualMassUpTo_le
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (S : ℝ) (hS : 0 < S) (branch : DFIVoronoiDualBranch) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q L : ℕ) (_hq : NeZero q),
      dfiVoronoiDualMassUpTo q branch g L ≤
        C * S ^ (1 / 2 : ℝ) * (L : ℝ) ^ (3 / 4 : ℝ) := by
  obtain ⟨A, hA, hPoint⟩ :=
    hg.exists_dfiVoronoiDualTerm_scaled_retained_bound S hS branch
  refine ⟨(4 / 3 : ℝ) * A, by positivity, ?_⟩
  intro q L hq
  letI : NeZero q := hq
  have hScale : 0 ≤ A * S ^ (1 / 2 : ℝ) :=
    mul_nonneg hA (Real.rpow_nonneg hS.le _)
  unfold dfiVoronoiDualMassUpTo
  calc
    ∑ n ∈ Finset.Icc 1 L, ‖dfiVoronoiDualTerm q branch g n‖ ≤
        ∑ n ∈ Finset.Icc 1 L,
          A * S ^ (1 / 2 : ℝ) * (n : ℝ) ^ (-(1 / 4 : ℝ)) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnIcc : n ∈ Finset.Icc 1 L := by simpa using hn
      exact hPoint q hq n (by
        have := (Finset.mem_Icc.mp hnIcc).1
        omega)
    _ = (A * S ^ (1 / 2 : ℝ)) *
        ∑ n ∈ Finset.Icc 1 L, (n : ℝ) ^ (-(1 / 4 : ℝ)) := by
      rw [Finset.mul_sum]
    _ ≤ (A * S ^ (1 / 2 : ℝ)) *
        ((4 / 3 : ℝ) * (L : ℝ) ^ (3 / 4 : ℝ)) :=
      mul_le_mul_of_nonneg_left (sum_Icc_natCast_rpow_neg_quarter_le L) hScale
    _ = ((4 / 3 : ℝ) * A) * S ^ (1 / 2 : ℝ) *
        (L : ℝ) ^ (3 / 4 : ℝ) := by ring

/-- Absolute convergence decomposes the complete transformed mass exactly
into DFI's retained frequencies `1 ≤ n ≤ L` and the tail `n > L`. -/
theorem dfiVoronoiDualMassUpTo_add_after
    (q : ℕ) [NeZero q] (branch : DFIVoronoiDualBranch)
    (g : ℝ → ℂ) (L : ℕ) :
    dfiVoronoiDualMassUpTo q branch g L +
        dfiVoronoiDualMassAfter q branch g L =
      ∑' n : ℕ, ‖dfiVoronoiDualTerm q branch g n‖ := by
  let F : ℕ → ℝ := fun n ↦ ‖dfiVoronoiDualTerm q branch g n‖
  have hF : Summable F := summable_norm_dfiVoronoiDualTerm q branch g
  have hSplit := hF.sum_add_tsum_nat_add (L + 1)
  have hFinite : ∑ n ∈ Finset.range (L + 1), F n =
      dfiVoronoiDualMassUpTo q branch g L := by
    unfold dfiVoronoiDualMassUpTo
    rw [show Finset.range (L + 1) = insert 0 (Finset.Icc 1 L) by
      ext n
      simp
      omega]
    simp [F]
  have hTail : (∑' j : ℕ, F (j + (L + 1))) =
      dfiVoronoiDualMassAfter q branch g L := by
    unfold dfiVoronoiDualMassAfter
    apply tsum_congr
    intro j
    rw [show j + (L + 1) = L + (j + 1) by omega]
  rw [hFinite, hTail] at hSplit
  simpa only [F] using hSplit

/-- Quantitative equation-(29) tail for an arbitrary admissible test
function, expressed using the exact tail object above. -/
theorem DFIVoronoiTestFunction.exists_dfiVoronoiDualMassAfter_le
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (S : ℝ) (hS : 0 < S) (k : ℕ) (hk : 0 < k)
    (branch : DFIVoronoiDualBranch) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q L : ℕ) (_hq : NeZero q), 0 < L →
      dfiVoronoiDualMassAfter q branch g L ≤
        C * (q : ℝ) ^ (2 + 2 * (k : ℝ)) *
          S ^ (-(1 / 2 : ℝ) - k) *
            ((L : ℝ) ^ (-(k : ℝ)) / (k : ℝ)) := by
  simpa only [dfiVoronoiDualMassAfter] using
    hg.exists_dfiVoronoiDualTerm_tail_scaled_decay S hS k hk branch

/-- Full one-variable Voronoi mass split at an arbitrary positive retained
window.  The first term is the right-contour estimate and the second is the
arbitrary-order left-contour tail. -/
theorem DFIVoronoiTestFunction.exists_dfiVoronoiDualMass_split_bound
    {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (S : ℝ) (hS : 0 < S) (k : ℕ) (hk : 0 < k)
    (branch : DFIVoronoiDualBranch) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ (q L : ℕ) (_hq : NeZero q), 0 < L →
      (∑' n : ℕ, ‖dfiVoronoiDualTerm q branch g n‖) ≤
        A * S ^ (1 / 2 : ℝ) * (L : ℝ) ^ (3 / 4 : ℝ) +
        B * (q : ℝ) ^ (2 + 2 * (k : ℝ)) *
          S ^ (-(1 / 2 : ℝ) - k) *
            ((L : ℝ) ^ (-(k : ℝ)) / (k : ℝ)) := by
  obtain ⟨A, hA, hRetained⟩ := hg.exists_dfiVoronoiDualMassUpTo_le S hS branch
  obtain ⟨B, hB, hTail⟩ := hg.exists_dfiVoronoiDualMassAfter_le S hS k hk branch
  refine ⟨A, B, hA, hB, ?_⟩
  intro q L hq hL
  letI : NeZero q := hq
  rw [← dfiVoronoiDualMassUpTo_add_after q branch g L]
  exact add_le_add (hRetained q L hq) (hTail q L hq hL)

/-- Retained first-variable frequencies for the literal equation-(23)
source weight, with physical scale `X/a`. -/
theorem exists_dfiEquation29_xSlice_retained_mass
    {Q P X Y U : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (a b : ℕ) (ha : 0 < a) (h : ℤ) (q : ℕ) (hq : 0 < q)
    (y : ℝ) (branch : DFIVoronoiDualBranch) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r L : ℕ) (_hr : NeZero r),
      dfiVoronoiDualMassUpTo r branch
          (fun x ↦ dfiEquation23Weight w
            (dfiLocalizedWeight f φ h) a b h q x y) L ≤
        C * (X / a) ^ (1 / 2 : ℝ) * (L : ℝ) ^ (3 / 4 : ℝ) := by
  have hScale : 0 < X / (a : ℝ) :=
    div_pos (zero_lt_one.trans_le hf.one_le_X) (by exact_mod_cast ha)
  exact (dfiEquation23Weight_xSlice w hf hbox hφ a b ha h q hq y)
    |>.exists_dfiVoronoiDualMassUpTo_le (X / a) hScale branch

/-- Retained second-variable frequencies for the literal equation-(23)
source weight, with physical scale `Y/b`. -/
theorem exists_dfiEquation29_ySlice_retained_mass
    {Q P X Y U : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (a b : ℕ) (hb : 0 < b) (h : ℤ) (q : ℕ) (hq : 0 < q)
    (x : ℝ) (branch : DFIVoronoiDualBranch) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r L : ℕ) (_hr : NeZero r),
      dfiVoronoiDualMassUpTo r branch
          (dfiEquation23Weight w
            (dfiLocalizedWeight f φ h) a b h q x) L ≤
        C * (Y / b) ^ (1 / 2 : ℝ) * (L : ℝ) ^ (3 / 4 : ℝ) := by
  have hScale : 0 < Y / (b : ℝ) :=
    div_pos (zero_lt_one.trans_le hf.one_le_Y) (by exact_mod_cast hb)
  exact (dfiEquation23Weight_ySlice w hf hbox hφ a b hb h q hq x)
    |>.exists_dfiVoronoiDualMassUpTo_le (Y / b) hScale branch

end RiemannZeta.GuthMaynard
