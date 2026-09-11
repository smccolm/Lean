import Tao2026.Asymptotics
import Tao2026.FactorialFibers
import Tao2026.FactorialOneTerm
import Tao2026.FactorialLowGeometry
import Tao2026.FactorialSmallIndexCounting
import Tao2026.FactorialLargeSieve
import Tao2026.PublicStatements

/-!
# Lower asymptotics for the factorial-square problem

The exact square family supplies more than a cardinal inequality: it proves
the reverse-big-O half of the `x^(1/2+o(1))` contracts in Tao's Theorems 1.9
and 1.10.  The analytic upper halves remain separate obligations.
-/

open Filter Asymptotics

namespace Tao2026

/-- Natural-valued subpolynomial budget supplied by Lemma 4.2 at the fixed
slack `η=1/12`, so the displayed logarithmic exponent is `3/4`. -/
noncomputable def factorialLemma42GapBudget (x : ℕ) : ℕ :=
  ⌈Real.exp ((Real.log x) ^ (3 / 4 : ℝ))⌉₊

theorem tendsto_factorialLemma42GapBudget_atTop :
    Tendsto factorialLemma42GapBudget atTop atTop := by
  have hreal : Tendsto (fun x : ℕ =>
      Real.exp ((Real.log x) ^ (3 / 4 : ℝ))) atTop atTop :=
    Real.tendsto_exp_atTop.comp
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 4)).comp
        (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))
  rw [tendsto_atTop]
  intro b
  filter_upwards [hreal.eventually (eventually_ge_atTop (b : ℝ))] with x hx
  have hcast : (b : ℝ) ≤
      (⌈Real.exp ((Real.log x) ^ (3 / 4 : ℝ))⌉₊ : ℝ) :=
    hx.trans (Nat.le_ceil _)
  exact_mod_cast hcast

/-- Lemma 4.2 gives a single endpoint-dependent tail-gap budget for every
factorial-square triple.  Middle indices below the eventual Lemma 4.2
threshold are absorbed using the unconditional `gap < middle` bound. -/
theorem eventually_factorialSquareTriple_tail_gap_le_lemma42Budget
    (h42 : TaoLemma42Conclusion) :
    ∀ᶠ x : ℕ in atTop, ∀ t ∈ factorialSquareTriplesUpTo x,
      t.2.2 - t.2.1 ≤ factorialLemma42GapBudget x := by
  have h42fixed := h42 (1 / 12) (by norm_num)
  rw [eventually_atTop] at h42fixed
  obtain ⟨N₀, hN₀⟩ := h42fixed
  have hbudgetLarge : ∀ᶠ x : ℕ in atTop,
      N₀ ≤ factorialLemma42GapBudget x :=
    tendsto_factorialLemma42GapBudget_atTop.eventually
      (eventually_ge_atTop N₀)
  filter_upwards [hbudgetLarge] with x hbudget
  intro t ht
  rw [mem_factorialSquareTriplesUpTo] at ht
  obtain ⟨_ht₁, ht₂, _ht₃, htTriple⟩ := ht
  let N : ℕ := t.2.1
  let H : ℕ := t.2.2 - t.2.1
  have htriple : IsFactorialSquareTriple t.1 N t.2.2 := htTriple
  have hNpos : 1 ≤ N := by
    dsimp only [N]
    exact (Finset.mem_Icc.mp ht₂).1
  have hNleX : N ≤ x := by
    dsimp only [N]
    exact (Finset.mem_Icc.mp ht₂).2
  have hinterval : IsFactorialThreeInterval N H := by
    rw [isFactorialThreeInterval_iff_factorialSquare]
    obtain ⟨m, hm⟩ := htriple.2.2.2
    refine ⟨Nat.sub_pos_of_lt htriple.2.2.1, t.1, m,
      htriple.1, htriple.2.1, ?_⟩
    simpa only [N, H, Nat.add_sub_of_le htriple.2.2.1.le] using hm
  by_cases hHtwo : 2 ≤ H
  · by_cases hNlarge : N₀ ≤ N
    · obtain ⟨_hHone, a, ha, haN, hcomponent⟩ := hinterval
      have hraw := hN₀ N hNlarge hHtwo ha haN hcomponent
      have hNreal : (0 : ℝ) < N := by exact_mod_cast hNpos
      have hXreal : (0 : ℝ) < x := lt_of_lt_of_le hNreal (by exact_mod_cast hNleX)
      have hlogMono : Real.log (N : ℝ) ≤ Real.log (x : ℝ) :=
        Real.strictMonoOn_log.monotoneOn hNreal hXreal (by exact_mod_cast hNleX)
      have hlogNnonneg : 0 ≤ Real.log (N : ℝ) :=
        Real.log_nonneg (by exact_mod_cast hNpos)
      have hpowMono : (Real.log (N : ℝ)) ^ (3 / 4 : ℝ) ≤
          (Real.log (x : ℝ)) ^ (3 / 4 : ℝ) :=
        Real.rpow_le_rpow hlogNnonneg hlogMono (by norm_num)
      have hexpMono :
          Real.exp ((Real.log (N : ℝ)) ^ (3 / 4 : ℝ)) ≤
            Real.exp ((Real.log (x : ℝ)) ^ (3 / 4 : ℝ)) :=
        Real.exp_le_exp.mpr hpowMono
      have hcast : (H : ℝ) ≤
          (factorialLemma42GapBudget x : ℕ) := by
        calc
          (H : ℝ) ≤ Real.exp ((Real.log N) ^ (3 / 4 : ℝ)) := by
            norm_num at hraw ⊢
            exact hraw
          _ ≤ Real.exp ((Real.log x) ^ (3 / 4 : ℝ)) := hexpMono
          _ ≤ (factorialLemma42GapBudget x : ℕ) := by
            exact Nat.le_ceil _
      exact_mod_cast hcast
    · have hgap : H < N := by
        simpa only [N, H] using htriple.tail_gap_lt_middle
      exact hgap.le.trans (Nat.le_of_lt (Nat.lt_of_not_ge hNlarge)) |>.trans hbudget
  · have hHle : H ≤ 1 := by omega
    have hbudgetPos : 1 ≤ factorialLemma42GapBudget x := by
      rw [factorialLemma42GapBudget, Nat.one_le_ceil_iff]
      exact Real.exp_pos _
    exact hHle.trans hbudgetPos

/-- The fixed `exp((log x)^(3/4))` budget is `x^o(1)`. -/
theorem factorialLemma42GapBudget_powerUpperBound :
    PowerUpperBound (fun x => (factorialLemma42GapBudget x : ℝ)) 0 := by
  intro ε hε
  have hquarterTop : Tendsto (fun x : ℕ =>
      (Real.log x) ^ (1 / 4 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hquarter : ∀ᶠ x : ℕ in atTop,
      1 / ε ≤ (Real.log x) ^ (1 / 4 : ℝ) :=
    hquarterTop.eventually (eventually_ge_atTop _)
  refine IsBigO.of_bound 2 ?_
  filter_upwards [hquarter, eventually_one_lt_log_nat,
    eventually_ge_atTop (2 : ℕ)] with x hx hlog hxTwo
  let L : ℝ := Real.log x
  have hLpos : 0 < L := by dsimp only [L]; linarith
  have hLone : 1 ≤ L := by dsimp only [L]; linarith
  have hquarterNonneg : 0 ≤ L ^ (1 / 4 : ℝ) :=
    Real.rpow_nonneg hLpos.le _
  have hone : 1 ≤ L ^ (1 / 4 : ℝ) * ε := by
    rw [← div_le_iff₀ hε]
    simpa only [L] using hx
  have hexponent : L ^ (3 / 4 : ℝ) ≤ ε * L := by
    calc
      L ^ (3 / 4 : ℝ) = L ^ (3 / 4 : ℝ) * 1 := by ring
      _ ≤ L ^ (3 / 4 : ℝ) * (L ^ (1 / 4 : ℝ) * ε) :=
        mul_le_mul_of_nonneg_left hone (Real.rpow_nonneg hLpos.le _)
      _ = (L ^ (3 / 4 : ℝ) * L ^ (1 / 4 : ℝ)) * ε := by ring
      _ = L ^ ((3 / 4 : ℝ) + 1 / 4) * ε := by
        rw [Real.rpow_add hLpos]
      _ = ε * L := by norm_num; ring
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hxTwo)
  have hexp : Real.exp (L ^ (3 / 4 : ℝ)) ≤ (x : ℝ) ^ ε := by
    calc
      Real.exp (L ^ (3 / 4 : ℝ)) ≤ Real.exp (ε * L) :=
        Real.exp_le_exp.mpr hexponent
      _ = (x : ℝ) ^ ε := by
        rw [Real.rpow_def_of_pos hxpos]
        dsimp only [L]
        congr 1
        ring
  have hxpowOne : 1 ≤ (x : ℝ) ^ ε :=
    Real.one_le_rpow (by exact_mod_cast (show 1 ≤ x by omega)) hε.le
  have hceil : (factorialLemma42GapBudget x : ℝ) <
      Real.exp (L ^ (3 / 4 : ℝ)) + 1 := by
    simpa only [factorialLemma42GapBudget, L] using
      Nat.ceil_lt_add_one (Real.exp_pos _).le
  have hbound : (factorialLemma42GapBudget x : ℝ) ≤
      2 * (x : ℝ) ^ (0 + ε) := by
    norm_num
    linarith
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _),
    Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg x) _)]
  exact hbound

/-- Interval-witness form of the uniform Lemma 4.2 budget. -/
theorem eventually_nontrivialFactorialThreeInterval_length_le_lemma42Budget
    (h42 : TaoLemma42Conclusion) :
    ∀ᶠ x : ℕ in atTop,
      ∀ t ∈ nontrivialFactorialThreeIntervalsUpTo x,
        t.2 ≤ factorialLemma42GapBudget x := by
  have h42fixed := h42 (1 / 12) (by norm_num)
  rw [eventually_atTop] at h42fixed
  obtain ⟨N₀, hN₀⟩ := h42fixed
  have hbudgetLarge : ∀ᶠ x : ℕ in atTop,
      N₀ ≤ factorialLemma42GapBudget x :=
    tendsto_factorialLemma42GapBudget_atTop.eventually
      (eventually_ge_atTop N₀)
  filter_upwards [hbudgetLarge] with x hbudget
  intro t ht
  have ht' := mem_nontrivialFactorialThreeIntervalsUpTo.mp ht
  have hNleX : t.1 ≤ x := ht'.1
  obtain ⟨_hNle, hHtwo, _hHle, _hend, hf3⟩ := ht'
  have hlengthLt : t.2 < t.1 := hf3.length_lt_start
  obtain ⟨_hHpos, a, ha, haN, hcomponent⟩ := hf3
  by_cases hNlarge : N₀ ≤ t.1
  · have hraw := hN₀ t.1 hNlarge hHtwo ha haN hcomponent
    have hNpos : (0 : ℝ) < t.1 := by exact_mod_cast (by omega : 0 < t.1)
    have hxpos : (0 : ℝ) < x :=
      lt_of_lt_of_le hNpos (by exact_mod_cast hNleX)
    have hlogMono : Real.log (t.1 : ℝ) ≤ Real.log (x : ℝ) :=
      Real.strictMonoOn_log.monotoneOn hNpos hxpos (by exact_mod_cast hNleX)
    have hlogNonneg : 0 ≤ Real.log (t.1 : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ t.1))
    have hpowMono : (Real.log (t.1 : ℝ)) ^ (3 / 4 : ℝ) ≤
        (Real.log (x : ℝ)) ^ (3 / 4 : ℝ) :=
      Real.rpow_le_rpow hlogNonneg hlogMono (by norm_num)
    have hcast : (t.2 : ℝ) ≤ (factorialLemma42GapBudget x : ℕ) := by
      calc
        (t.2 : ℝ) ≤ Real.exp ((Real.log t.1) ^ (3 / 4 : ℝ)) := by
          norm_num at hraw ⊢
          exact hraw
        _ ≤ Real.exp ((Real.log x) ^ (3 / 4 : ℝ)) :=
          Real.exp_le_exp.mpr hpowMono
        _ ≤ (factorialLemma42GapBudget x : ℕ) := Nat.le_ceil _
    exact_mod_cast hcast
  · exact hlengthLt.le.trans
      (Nat.le_of_lt (Nat.lt_of_not_ge hNlarge)) |>.trans hbudget

/-- The actual small-`a` source branch, after Lemma 4.2, contributes only
`x^(1/4+o(1))` endpoints. -/
theorem factorialSmallIndexSourceEndpointCount_powerUpperBound_of_lemma42
    (h42 : TaoLemma42Conclusion) :
    PowerUpperBound
      (fun x => ((factorialSmallIndexSourceEndpointsUpTo x).card : ℝ))
      (1 / 4 : ℝ) :=
  factorialSmallIndexSourceEndpointCount_powerUpperBound
    factorialLemma42GapBudget factorialLemma42GapBudget_powerUpperBound
    (eventually_nontrivialFactorialThreeInterval_length_le_lemma42Budget h42)

/-! ## Global parameter boxes for the complementary sieve branch -/

/-- Lemmas 4.1 and 4.2 give this common subpolynomial range for the factorial
index in every nontrivial interval. -/
noncomputable def factorialLemma41IndexBudget (x : ℕ) : ℕ :=
  factorialLemma42GapBudget x *
    logarithmicSmoothnessBudget taoLemma41Constant x

theorem factorialLemma41IndexBudget_powerUpperBound :
    PowerUpperBound (fun x => (factorialLemma41IndexBudget x : ℝ)) 0 := by
  have hLog := logarithmicSmoothnessBudget_powerUpperBound_zero
    taoLemma41Constant_pos
  simpa [factorialLemma41IndexBudget, Nat.cast_mul] using
    factorialLemma42GapBudget_powerUpperBound.mul hLog

/-- Uniform eventual `(a,H)` box for all nontrivial type-`F₃` interval
witnesses. -/
theorem eventually_nontrivialFactorialThreeInterval_parameters_le_budgets
    (h42 : TaoLemma42Conclusion) :
    ∀ᶠ x : ℕ in atTop,
      ∀ t : ↥(nontrivialFactorialThreeIntervalsUpTo x),
        (chosenFactorialRelationCertificate x t).factorialIndex ≤
            factorialLemma41IndexBudget x ∧
          t.1.2 ≤ factorialLemma42GapBudget x := by
  filter_upwards
    [eventually_nontrivialFactorialThreeInterval_length_le_lemma42Budget h42,
      eventually_ge_atTop (2 : ℕ)] with x hGap hx
  intro t
  let c := chosenFactorialRelationCertificate x t
  have hspec := chosenFactorialRelationCertificate_spec x t
  change c.Certifies t.1.1 t.1.2 at hspec
  have ht' := mem_nontrivialFactorialThreeIntervalsUpTo.mp t.property
  have hHGap : t.1.2 ≤ factorialLemma42GapBudget x := hGap t.1 t.property
  have h41 := taoLemma41_chosenConstant
    (N := t.1.1) (H := t.1.2) (a := c.factorialIndex)
    (by omega) hspec.1 hspec.2.1 hspec.2.2.1
  have hNpos : (0 : ℝ) < t.1.1 := by exact_mod_cast (by omega : 0 < t.1.1)
  have hlogLe : Real.log (t.1.1 : ℝ) ≤ Real.log (x + 2 : ℝ) := by
    apply Real.log_le_log hNpos
    exact_mod_cast (by omega : t.1.1 ≤ x + 2)
  have hlogShift : 0 ≤ Real.log (x + 2 : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ x + 2))
  have hceil : taoLemma41Constant * Real.log (x + 2 : ℝ) ≤
      (logarithmicSmoothnessBudget taoLemma41Constant x : ℝ) := by
    simpa [logarithmicSmoothnessBudget, mul_comm] using
      (Nat.le_ceil (taoLemma41Constant * Real.log (x + 2 : ℝ)))
  have haReal : (c.factorialIndex : ℝ) ≤
      (factorialLemma41IndexBudget x : ℕ) := by
    calc
      (c.factorialIndex : ℝ) ≤
          taoLemma41Constant * (t.1.2 : ℝ) * Real.log t.1.1 := h41.2
      _ ≤ taoLemma41Constant * (t.1.2 : ℝ) * Real.log (x + 2) :=
        mul_le_mul_of_nonneg_left hlogLe
          (mul_nonneg taoLemma41Constant_pos.le (Nat.cast_nonneg _))
      _ ≤ taoLemma41Constant * factorialLemma42GapBudget x *
          Real.log (x + 2) := by
        have hHcast : (t.1.2 : ℝ) ≤ factorialLemma42GapBudget x := by
          exact_mod_cast hHGap
        gcongr
        exact taoLemma41Constant_pos.le
      _ = (factorialLemma42GapBudget x : ℝ) *
          (taoLemma41Constant * Real.log (x + 2)) := by ring
      _ ≤ (factorialLemma42GapBudget x : ℝ) *
          logarithmicSmoothnessBudget taoLemma41Constant x := by
        gcongr
      _ = (factorialLemma41IndexBudget x : ℕ) := by
        simp [factorialLemma41IndexBudget]
  exact ⟨by exact_mod_cast haReal, hHGap⟩

/-- Hence the literal complementary family eventually lies in one explicit
subpolynomial `(a,H)` box. -/
theorem eventually_factorialLargeSieveIntervalsUpTo_subset_budgeted
    (B : ℕ) (h42 : TaoLemma42Conclusion) :
    ∀ᶠ x : ℕ in atTop,
      factorialLargeSieveIntervalsUpTo x B ⊆
        factorialLargeSieveBudgetedIntervalsUpTo x B
          (factorialLemma41IndexBudget x)
          (factorialLemma42GapBudget x) := by
  filter_upwards
    [eventually_nontrivialFactorialThreeInterval_parameters_le_budgets h42]
      with x hx
  intro t ht
  rw [mem_factorialLargeSieveBudgetedIntervalsUpTo]
  have hp := hx t
  exact ⟨ht, hp.1, hp.2⟩

/-- All remaining work in the nontrivial half of Theorem 1.9 is now isolated
in the complementary endpoint family.  Any square-root upper bound for that
family combines with the proved bounded-length and small-index estimates. -/
theorem nontrivialFactorialThreeCount_powerUpperBound_of_largeSieve
    (B : ℕ) (h42 : TaoLemma42Conclusion)
    (hLarge : PowerUpperBound
      (fun x => ((factorialLargeSieveEndpointsUpTo x B).card : ℝ))
      (1 / 2 : ℝ)) :
    PowerUpperBound
      (fun x => (nontrivialFactorialThreeCount x : ℝ)) (1 / 2 : ℝ) := by
  have hBounded :=
    (factorialBoundedLengthEndpointCount_powerUpperBound_zero B).mono_exponent
      (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  have hSmall :=
    (factorialSmallIndexSourceEndpointCount_powerUpperBound_of_lemma42 h42).mono_exponent
      (show (1 / 4 : ℝ) ≤ 1 / 2 by norm_num)
  have hCases : PowerUpperBound
      (fun x =>
        ((factorialBoundedLengthEndpointsUpTo x B).card : ℝ) +
          ((factorialSmallIndexSourceEndpointsUpTo x).card : ℝ) +
            ((factorialLargeSieveEndpointsUpTo x B).card : ℝ))
      (1 / 2 : ℝ) := hBounded.add hSmall |>.add hLarge
  intro ε hε
  have hdom : (fun x => (nontrivialFactorialThreeCount x : ℝ))
      =O[atTop]
        (fun x =>
          ((factorialBoundedLengthEndpointsUpTo x B).card : ℝ) +
            ((factorialSmallIndexSourceEndpointsUpTo x).card : ℝ) +
              ((factorialLargeSieveEndpointsUpTo x B).card : ℝ)) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards with x
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _), one_mul,
      Real.norm_of_nonneg (by positivity)]
    exact_mod_cast nontrivialFactorialThreeCount_le_three_cases x B
  exact hdom.trans (hCases ε hε)

private theorem power_half_sub_le_two_mul_factorialThreeOneTermCount
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      ‖(n : ℝ) ^ ((1 / 2 : ℝ) - ε)‖ ≤
        2 * ‖(factorialThreeOneTermCount n : ℝ)‖ := by
  filter_upwards [eventually_ge_atTop 9] with n hn
  have hnOne : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (le_trans (by decide : 1 ≤ 9) hn)
  have hpow : (n : ℝ) ^ ((1 / 2 : ℝ) - ε) ≤ Real.sqrt n := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hnOne (by linarith)
  have hsqrtNat : 3 ≤ Nat.sqrt n := by
    rw [Nat.le_sqrt']
    norm_num
    exact hn
  have hroot : Real.sqrt n ≤
      2 * (factorialThreeOneTermCount n : ℝ) := by
    calc
      Real.sqrt n ≤ (Nat.sqrt n : ℝ) + 1 :=
        Real.real_sqrt_le_nat_sqrt_succ
      _ ≤ 2 * (Nat.sqrt n - 1 : ℕ) := by
        norm_cast
        omega
      _ ≤ 2 * (factorialThreeOneTermCount n : ℝ) := by
        gcongr
        exact_mod_cast sqrt_sub_one_le_factorialThreeOneTermCount n
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _),
    Real.norm_of_nonneg
      (Nat.cast_nonneg (factorialThreeOneTermCount n) :
        0 ≤ (factorialThreeOneTermCount n : ℝ))]
  exact hpow.trans hroot

/-- The square family proves the lower half of the `F₃¹` square-root scale. -/
theorem factorialThreeOneTermCount_powerScale_lower :
    ∀ ε : ℝ, 0 < ε →
      ((fun n : ℕ => (n : ℝ) ^ ((1 / 2 : ℝ) - ε)) =O[atTop]
        fun n => (factorialThreeOneTermCount n : ℝ)) := by
  intro ε hε
  exact IsBigO.of_bound 2
    (power_half_sub_le_two_mul_factorialThreeOneTermCount ε hε)

/-- The same lower half transfers from `F₃¹` to all `F₃` endpoints. -/
theorem factorialThreeCount_powerScale_lower :
    ∀ ε : ℝ, 0 < ε →
      ((fun n : ℕ => (n : ℝ) ^ ((1 / 2 : ℝ) - ε)) =O[atTop]
        fun n => (factorialThreeCount n : ℝ)) := by
  intro ε hε
  refine IsBigO.of_bound 2 ?_
  filter_upwards
      [power_half_sub_le_two_mul_factorialThreeOneTermCount ε hε] with n hn
  calc
    ‖(n : ℝ) ^ ((1 / 2 : ℝ) - ε)‖ ≤
        2 * ‖(factorialThreeOneTermCount n : ℝ)‖ := hn
    _ ≤ 2 * ‖(factorialThreeCount n : ℝ)‖ := by
      rw [Real.norm_of_nonneg
          (Nat.cast_nonneg (factorialThreeOneTermCount n) :
            0 ≤ (factorialThreeOneTermCount n : ℝ)),
        Real.norm_of_nonneg
          (Nat.cast_nonneg (factorialThreeCount n) :
            0 ≤ (factorialThreeCount n : ℝ))]
      gcongr
      exact_mod_cast factorialThreeOneTermCount_le_factorialThreeCount n

/-- The exact endpoint projection transfers the lower half to the factorial-
square triple count, completing the lower half of Theorem 1.10's contract. -/
theorem factorialSquareTripleCount_powerScale_lower :
    ∀ ε : ℝ, 0 < ε →
      ((fun n : ℕ => (n : ℝ) ^ ((1 / 2 : ℝ) - ε)) =O[atTop]
        fun n => (factorialSquareTripleCount n : ℝ)) := by
  intro ε hε
  refine IsBigO.of_bound 2 ?_
  filter_upwards
      [power_half_sub_le_two_mul_factorialThreeOneTermCount ε hε] with n hn
  calc
    ‖(n : ℝ) ^ ((1 / 2 : ℝ) - ε)‖ ≤
        2 * ‖(factorialThreeOneTermCount n : ℝ)‖ := hn
    _ ≤ 2 * ‖(factorialSquareTripleCount n : ℝ)‖ := by
      rw [Real.norm_of_nonneg
          (Nat.cast_nonneg (factorialThreeOneTermCount n) :
            0 ≤ (factorialThreeOneTermCount n : ℝ)),
        Real.norm_of_nonneg
          (Nat.cast_nonneg (factorialSquareTripleCount n) :
            0 ≤ (factorialSquareTripleCount n : ℝ))]
      gcongr
      exact_mod_cast le_trans
        (factorialThreeOneTermCount_le_factorialThreeCount n)
        (factorialThreeCount_le_factorialSquareTripleCount n)

/-- A subpolynomial natural-valued gap budget times the square-root-scale
`F₃` count still has square-root power upper bound.  Combined with the exact
finite counting key, this is Tao's complete asymptotic upper transfer for
Theorem 1.10. -/
theorem factorialSquareTripleCount_powerUpperBound_of_f3_and_gap
    (hES : ErdosSelfridgeSquareConclusion) (g : ℕ → ℕ)
    (hgap : ∀ᶠ x : ℕ in atTop, ∀ t ∈ factorialSquareTriplesUpTo x,
      t.2.2 - t.2.1 ≤ g x)
    (hg : PowerUpperBound (fun x => (g x : ℝ)) 0)
    (hf3 : PowerScale (fun x => (factorialThreeCount x : ℝ)) (1 / 2)) :
    PowerUpperBound
      (fun x => (factorialSquareTripleCount x : ℝ)) (1 / 2) := by
  intro ε hε
  have hhalfε : 0 < ε / 2 := by linarith
  have hfinite :
      (fun x => (factorialSquareTripleCount x : ℝ)) =O[atTop]
        (fun x => (g x : ℝ) * (factorialThreeCount x : ℝ)) := by
    refine IsBigO.of_bound 2 ?_
    filter_upwards [hgap] with x hx
    rw [Real.norm_of_nonneg
        (Nat.cast_nonneg (factorialSquareTripleCount x) :
          0 ≤ (factorialSquareTripleCount x : ℝ)),
      Real.norm_of_nonneg (mul_nonneg
        (Nat.cast_nonneg (g x) : 0 ≤ (g x : ℝ))
        (Nat.cast_nonneg (factorialThreeCount x) :
          0 ≤ (factorialThreeCount x : ℝ)))]
    norm_cast
    simpa [mul_assoc] using
      (factorialSquareTripleCount_le_two_mul_gap_mul_factorialThreeCount
        hES hx)
  have hproduct := (hg (ε / 2) hhalfε).mul (hf3 (ε / 2) hhalfε).1
  have hpowers :
      (fun x : ℕ =>
        (x : ℝ) ^ ((0 : ℝ) + ε / 2) *
          (x : ℝ) ^ ((1 / 2 : ℝ) + ε / 2)) =O[atTop]
        (fun x : ℕ => (x : ℝ) ^ ((1 / 2 : ℝ) + ε)) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop 1] with x hx
    have hxpos : (0 : ℝ) < x := by exact_mod_cast hx
    have hleft : 0 ≤
        (x : ℝ) ^ ((0 : ℝ) + ε / 2) *
          (x : ℝ) ^ ((1 / 2 : ℝ) + ε / 2) :=
      mul_nonneg (Real.rpow_nonneg hxpos.le _)
        (Real.rpow_nonneg hxpos.le _)
    have hright : 0 ≤ (x : ℝ) ^ ((1 / 2 : ℝ) + ε) :=
      Real.rpow_nonneg hxpos.le _
    rw [Real.norm_of_nonneg hleft, Real.norm_of_nonneg hright, one_mul]
    calc
      (x : ℝ) ^ ((0 : ℝ) + ε / 2) *
          (x : ℝ) ^ ((1 / 2 : ℝ) + ε / 2) =
          (x : ℝ) ^ (((0 : ℝ) + ε / 2) +
            ((1 / 2 : ℝ) + ε / 2)) :=
        (Real.rpow_add hxpos _ _).symm
      _ = (x : ℝ) ^ ((1 / 2 : ℝ) + ε) := by
        apply congrArg (fun z : ℝ => (x : ℝ) ^ z)
        ring
      _ ≤ (x : ℝ) ^ ((1 / 2 : ℝ) + ε) := le_rfl
  exact hfinite.trans (hproduct.trans hpowers)

/-- Source-facing conditional closure of Tao's Theorem 1.10.  No counting or
asymptotic bookkeeping remains hidden: a proof of Theorem 1.9's total `F₃`
scale, an eventual subpolynomial `hf3` tail-gap budget, and the square case of
Erdős--Selfridge imply the exact public conclusion. -/
theorem taoTheorem110_of_theorem19_and_subpolynomial_gap
    (hES : ErdosSelfridgeSquareConclusion) (g : ℕ → ℕ)
    (hgap : ∀ᶠ x : ℕ in atTop, ∀ t ∈ factorialSquareTriplesUpTo x,
      t.2.2 - t.2.1 ≤ g x)
    (hg : PowerUpperBound (fun x => (g x : ℝ)) 0)
    (h19 : TaoTheorem19Conclusion) :
    TaoTheorem110Conclusion := by
  intro ε hε
  exact ⟨factorialSquareTripleCount_powerUpperBound_of_f3_and_gap
      hES g hgap hg h19.2 ε hε,
    factorialSquareTripleCount_powerScale_lower ε hε⟩

/-- Lemma 4.2 supplies exactly the subpolynomial tail-gap input required by
the finite counting proof of Theorem 1.10. -/
theorem taoTheorem110_of_theorem19_and_lemma42
    (hES : ErdosSelfridgeSquareConclusion)
    (h19 : TaoTheorem19Conclusion) (h42 : TaoLemma42Conclusion) :
    TaoTheorem110Conclusion :=
  taoTheorem110_of_theorem19_and_subpolynomial_gap hES
    factorialLemma42GapBudget
    (eventually_factorialSquareTriple_tail_gap_le_lemma42Budget h42)
    factorialLemma42GapBudget_powerUpperBound h19

/-- Source-facing conditional Theorem 1.10 closure using the analytic inputs
already isolated by the development. -/
theorem taoTheorem110_of_theorem19_and_analytic_inputs
    (hES : ErdosSelfridgeSquareConclusion)
    (h19 : TaoTheorem19Conclusion)
    (h25 : TaoTheorem25SpecializedConclusion)
    (h23ii : TaoProposition23iiConclusion) :
    TaoTheorem110Conclusion :=
  taoTheorem110_of_theorem19_and_lemma42 hES h19
    (taoLemma42_of_inputs h25 h23ii)

/-- Variant whose prime-gap input is the pinned source-shaped BHP theorem;
the endpoint transfer to Proposition 2.3(ii) is internal. -/
theorem taoTheorem110_of_theorem19_and_source_inputs
    (hES : ErdosSelfridgeSquareConclusion)
    (h19 : TaoTheorem19Conclusion)
    (h25 : TaoTheorem25SpecializedConclusion)
    (hBHP : BakerHarmanPintzTheorem1Conclusion) :
    TaoTheorem110Conclusion :=
  taoTheorem110_of_theorem19_and_lemma42 hES h19
    (taoLemma42_of_bakerHarmanPintz h25 hBHP)

end Tao2026
