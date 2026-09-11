import Tao2026.FactorialSmoothCounting

/-!
# The small-factorial-index branch in Tao's Theorem 1.9

This file treats the first easy case in Section 4 with the fixed numerical
threshold `a ≤ H log(x+2) / 100`.  Lemma 4.3 then makes both selected
coefficients at most `x^(1/10+o(1))`; the exact finite interval code from
`FactorialCounting` turns this into a power-saving endpoint count.
-/

open Filter Asymptotics

namespace Tao2026

noncomputable section

/-- A logarithmic natural budget which simultaneously absorbs the small
factorial index and the interval length. -/
def factorialSmallIndexLogBudget (x : ℕ) : ℕ :=
  logarithmicSmoothnessBudget 1 x

/-- The actual length budget is truncated at the ambient endpoint cutoff. -/
def factorialSmallIndexGapBudget (G : ℕ → ℕ) (x : ℕ) : ℕ :=
  min (G x) x

/-- Uniform budget for `max a H` on the small-index branch. -/
def factorialSmallIndexParameterBudget (G : ℕ → ℕ) (x : ℕ) : ℕ :=
  factorialSmallIndexGapBudget G x * factorialSmallIndexLogBudget x

/-- The direct exponential envelope obtained from Lemma 4.3. -/
def factorialSmallIndexCoefficientEnvelope (G : ℕ → ℕ) (x : ℕ) : ℕ :=
  ⌈Real.exp (3 * Real.log 4 *
    (3 + Real.log (factorialSmallIndexParameterBudget G x) +
      Real.log (x + 2) / 100))⌉₊

/-- Truncation at `x` preserves every selected coefficient, since the
coefficient is the squarefree part of an interval element at most `x`. -/
def factorialSmallIndexCoefficientBudget (G : ℕ → ℕ) (x : ℕ) : ℕ :=
  min x (factorialSmallIndexCoefficientEnvelope G x)

/-- The literal first easy subfamily, retaining the chosen Lemma 4.3 index. -/
def factorialSmallIndexIntervalsUpTo (G : ℕ → ℕ) (x : ℕ) :
    Finset ↥(nontrivialFactorialThreeIntervalsUpTo x) :=
  (nontrivialFactorialThreeIntervalsUpTo x).attach.filter fun t =>
    t.1.2 ≤ G x ∧
      ((chosenFactorialRelationCertificate x t).factorialIndex : ℝ) ≤
        (t.1.2 : ℝ) * Real.log (x + 2) / 100

theorem mem_factorialSmallIndexIntervalsUpTo
    {G : ℕ → ℕ} {x : ℕ}
    {t : ↥(nontrivialFactorialThreeIntervalsUpTo x)} :
    t ∈ factorialSmallIndexIntervalsUpTo G x ↔
      t.1.2 ≤ G x ∧
        ((chosenFactorialRelationCertificate x t).factorialIndex : ℝ) ≤
          (t.1.2 : ℝ) * Real.log (x + 2) / 100 := by
  simp [factorialSmallIndexIntervalsUpTo]

def factorialSmallIndexEndpointsUpTo (G : ℕ → ℕ) (x : ℕ) : Finset ℕ :=
  (factorialSmallIndexIntervalsUpTo G x).image fun t => t.1.1 + t.1.2

/-- The source-defined small-index family, before inserting any consequence
of Lemma 4.2 for its interval length. -/
def factorialSmallIndexSourceIntervalsUpTo (x : ℕ) :
    Finset ↥(nontrivialFactorialThreeIntervalsUpTo x) :=
  (nontrivialFactorialThreeIntervalsUpTo x).attach.filter fun t =>
    ((chosenFactorialRelationCertificate x t).factorialIndex : ℝ) ≤
      (t.1.2 : ℝ) * Real.log (x + 2) / 100

theorem mem_factorialSmallIndexSourceIntervalsUpTo
    {x : ℕ} {t : ↥(nontrivialFactorialThreeIntervalsUpTo x)} :
    t ∈ factorialSmallIndexSourceIntervalsUpTo x ↔
      ((chosenFactorialRelationCertificate x t).factorialIndex : ℝ) ≤
        (t.1.2 : ℝ) * Real.log (x + 2) / 100 := by
  simp [factorialSmallIndexSourceIntervalsUpTo]

def factorialSmallIndexSourceEndpointsUpTo (x : ℕ) : Finset ℕ :=
  (factorialSmallIndexSourceIntervalsUpTo x).image fun t => t.1.1 + t.1.2

theorem factorialSmallIndexSourceIntervalsUpTo_subset
    (G : ℕ → ℕ) {x : ℕ}
    (hG : ∀ t ∈ nontrivialFactorialThreeIntervalsUpTo x, t.2 ≤ G x) :
    factorialSmallIndexSourceIntervalsUpTo x ⊆
      factorialSmallIndexIntervalsUpTo G x := by
  intro t ht
  rw [mem_factorialSmallIndexIntervalsUpTo]
  exact ⟨hG t.1 t.property,
    mem_factorialSmallIndexSourceIntervalsUpTo.mp ht⟩

theorem factorialSmallIndexSourceEndpointsUpTo_subset
    (G : ℕ → ℕ) {x : ℕ}
    (hG : ∀ t ∈ nontrivialFactorialThreeIntervalsUpTo x, t.2 ≤ G x) :
    factorialSmallIndexSourceEndpointsUpTo x ⊆
      factorialSmallIndexEndpointsUpTo G x := by
  intro n hn
  rw [factorialSmallIndexSourceEndpointsUpTo, Finset.mem_image] at hn
  rcases hn with ⟨t, ht, rfl⟩
  rw [factorialSmallIndexEndpointsUpTo, Finset.mem_image]
  exact ⟨t, factorialSmallIndexSourceIntervalsUpTo_subset G hG ht, rfl⟩

/-- On a small-index interval, both `H` and the chosen factorial index are
bounded by the common parameter budget. -/
theorem factorialSmallIndex_parameters_le
    {G : ℕ → ℕ} {x : ℕ}
    {t : ↥(nontrivialFactorialThreeIntervalsUpTo x)}
    (ht : t ∈ factorialSmallIndexIntervalsUpTo G x) :
    (chosenFactorialRelationCertificate x t).factorialIndex ≤
        factorialSmallIndexParameterBudget G x ∧
      t.1.2 ≤ factorialSmallIndexGapBudget G x ∧
      max (chosenFactorialRelationCertificate x t).factorialIndex t.1.2 ≤
        factorialSmallIndexParameterBudget G x := by
  let c := chosenFactorialRelationCertificate x t
  have hsmall := mem_factorialSmallIndexIntervalsUpTo.mp ht
  change t.1.2 ≤ G x ∧ (c.factorialIndex : ℝ) ≤
    (t.1.2 : ℝ) * Real.log (x + 2) / 100 at hsmall
  have htBase := mem_nontrivialFactorialThreeIntervalsUpTo.mp t.property
  have hxH : t.1.2 ≤ x := htBase.2.2.1
  have hHGap : t.1.2 ≤ factorialSmallIndexGapBudget G x := by
    exact le_min hsmall.1 hxH
  have hxlog : 0 < Real.log (x + 2) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < x + 2))
  have hlogCeil : Real.log (x + 2) ≤
      (factorialSmallIndexLogBudget x : ℝ) := by
    simpa [factorialSmallIndexLogBudget, logarithmicSmoothnessBudget] using
      (Nat.le_ceil (Real.log (x + 2)))
  have hlogBudgetOne : 1 ≤ factorialSmallIndexLogBudget x := by
    rw [factorialSmallIndexLogBudget, logarithmicSmoothnessBudget,
      Nat.one_le_ceil_iff]
    simpa using hxlog
  have haReal : (c.factorialIndex : ℝ) ≤
      (factorialSmallIndexParameterBudget G x : ℕ) := by
    calc
      (c.factorialIndex : ℝ) ≤
          (t.1.2 : ℝ) * Real.log (x + 2) / 100 := hsmall.2
      _ ≤ (t.1.2 : ℝ) * Real.log (x + 2) := by
        have hprod : 0 ≤ (t.1.2 : ℝ) * Real.log (x + 2) := by positivity
        linarith
      _ ≤ (factorialSmallIndexGapBudget G x : ℝ) *
          factorialSmallIndexLogBudget x := by gcongr
      _ = (factorialSmallIndexParameterBudget G x : ℕ) := by
        simp [factorialSmallIndexParameterBudget]
  have ha : c.factorialIndex ≤ factorialSmallIndexParameterBudget G x := by
    exact_mod_cast haReal
  have hHParameter : t.1.2 ≤ factorialSmallIndexParameterBudget G x := by
    rw [factorialSmallIndexParameterBudget]
    exact hHGap.trans
      (le_mul_of_one_le_right (Nat.zero_le _) hlogBudgetOne)
  exact ⟨ha, hHGap, max_le ha hHParameter⟩

/-- The quotient term in Lemma 4.3 costs at most `1 + log(x+2)/100` in the
small-index branch. -/
theorem factorialSmallIndex_parameter_div_length_le
    {G : ℕ → ℕ} {x : ℕ}
    {t : ↥(nontrivialFactorialThreeIntervalsUpTo x)}
    (ht : t ∈ factorialSmallIndexIntervalsUpTo G x) :
    ((max (chosenFactorialRelationCertificate x t).factorialIndex
      t.1.2 : ℕ) : ℝ) / t.1.2 ≤ 1 + Real.log (x + 2) / 100 := by
  let c := chosenFactorialRelationCertificate x t
  have hsmall := mem_factorialSmallIndexIntervalsUpTo.mp ht
  change t.1.2 ≤ G x ∧ (c.factorialIndex : ℝ) ≤
    (t.1.2 : ℝ) * Real.log (x + 2) / 100 at hsmall
  have htBase := mem_nontrivialFactorialThreeIntervalsUpTo.mp t.property
  have hHpos : (0 : ℝ) < t.1.2 := by exact_mod_cast (by omega : 0 < t.1.2)
  have hmax : ((max c.factorialIndex t.1.2 : ℕ) : ℝ) ≤
      c.factorialIndex + t.1.2 := by
    have hmaxNat : max c.factorialIndex t.1.2 ≤
        c.factorialIndex + t.1.2 := by omega
    exact_mod_cast hmaxNat
  rw [div_le_iff₀ hHpos]
  calc
    ((max c.factorialIndex t.1.2 : ℕ) : ℝ) ≤
        c.factorialIndex + t.1.2 := hmax
    _ ≤ ((t.1.2 : ℝ) * Real.log (x + 2) / 100) + t.1.2 := by
      simpa [add_comm] using add_le_add_right hsmall.2 (t.1.2 : ℝ)
    _ = (1 + Real.log (x + 2) / 100) * t.1.2 := by ring

/-- The selected coefficients obey the explicit small-index envelope. -/
theorem chosenFactorialRelationCertificate_coefficients_le_smallIndexEnvelope
    {G : ℕ → ℕ} {x : ℕ}
    {t : ↥(nontrivialFactorialThreeIntervalsUpTo x)}
    (ht : t ∈ factorialSmallIndexIntervalsUpTo G x) :
    (chosenFactorialRelationCertificate x t).coeffLeft ≤
        factorialSmallIndexCoefficientEnvelope G x ∧
      (chosenFactorialRelationCertificate x t).coeffRight ≤
        factorialSmallIndexCoefficientEnvelope G x := by
  let c := chosenFactorialRelationCertificate x t
  let A := factorialSmallIndexParameterBudget G x
  have hspec := chosenFactorialRelationCertificate_spec x t
  change c.Certifies t.1.1 t.1.2 at hspec
  have hparameters := factorialSmallIndex_parameters_le ht
  change c.factorialIndex ≤ A ∧ _ at hparameters
  have hP : max c.factorialIndex t.1.2 ≤ A := hparameters.2.2
  have hApos : 0 < A := lt_of_lt_of_le
    (show 0 < max c.factorialIndex t.1.2 by
      exact lt_of_lt_of_le hspec.1 (Nat.le_max_left _ _)) hP
  have hlog : Real.log ((max c.factorialIndex t.1.2 : ℕ) : ℝ) ≤
      Real.log (A : ℝ) := by
    exact Real.log_le_log
      (by exact_mod_cast (show 0 < max c.factorialIndex t.1.2 from
        lt_of_lt_of_le hspec.1 (Nat.le_max_left _ _)))
      (by exact_mod_cast hP)
  have hdiv := factorialSmallIndex_parameter_div_length_le ht
  have hdiv' : ((max c.factorialIndex t.1.2 : ℕ) : ℝ) / t.1.2 ≤
      1 + Real.log (x + 2) / 100 := by
    simpa only [c] using hdiv
  have hinside :
      2 + Real.log ((max c.factorialIndex t.1.2 : ℕ) : ℝ) +
          ((max c.factorialIndex t.1.2 : ℕ) : ℝ) / t.1.2 ≤
        3 + Real.log (A : ℝ) + Real.log (x + 2) / 100 := by
    linarith
  have hlogFour : 0 ≤ 3 * Real.log 4 := by positivity
  have hexp : Real.exp
      (factorialCoefficientSelectionLogBound t.1.2
        (max c.factorialIndex t.1.2)) ≤
      Real.exp (3 * Real.log 4 *
        (3 + Real.log A + Real.log (x + 2) / 100)) := by
    apply Real.exp_le_exp.mpr
    rw [factorialCoefficientSelectionLogBound]
    exact mul_le_mul_of_nonneg_left hinside hlogFour
  have hceil : Real.exp (3 * Real.log 4 *
        (3 + Real.log A + Real.log (x + 2) / 100)) ≤
      (factorialSmallIndexCoefficientEnvelope G x : ℝ) := by
    exact Nat.le_ceil _
  constructor
  · exact_mod_cast hspec.2.2.2.2.2.2.2.2.2.2.2.1.trans (hexp.trans hceil)
  · exact_mod_cast hspec.2.2.2.2.2.2.2.2.2.2.2.2.1.trans (hexp.trans hceil)

/-- The same bounds after truncating the coefficient range at `x`. -/
theorem chosenFactorialRelationCertificate_coefficients_le_smallIndexBudget
    {G : ℕ → ℕ} {x : ℕ}
    {t : ↥(nontrivialFactorialThreeIntervalsUpTo x)}
    (ht : t ∈ factorialSmallIndexIntervalsUpTo G x) :
    (chosenFactorialRelationCertificate x t).coeffLeft ≤
        factorialSmallIndexCoefficientBudget G x ∧
      (chosenFactorialRelationCertificate x t).coeffRight ≤
        factorialSmallIndexCoefficientBudget G x := by
  have henv :=
    chosenFactorialRelationCertificate_coefficients_le_smallIndexEnvelope ht
  have hx := chosenFactorialRelationCertificate_coefficients_le x t
  exact ⟨le_min hx.1 henv.1, le_min hx.2 henv.2⟩

/-- Every small-index interval enters the concrete finite certificate box. -/
theorem factorialSmallIndexIntervalsUpTo_subset_budgeted
    (G : ℕ → ℕ) (x : ℕ) :
    factorialSmallIndexIntervalsUpTo G x ⊆
      factorialBudgetedIntervalsUpTo x
        (factorialSmallIndexParameterBudget G x)
        (factorialSmallIndexCoefficientBudget G x)
        (factorialSmallIndexGapBudget G x) := by
  intro t ht
  rw [mem_factorialBudgetedIntervalsUpTo]
  have hp := factorialSmallIndex_parameters_le ht
  have hc :=
    chosenFactorialRelationCertificate_coefficients_le_smallIndexBudget ht
  exact ⟨hp.1, hc.1, hc.2, hp.2.1⟩

theorem factorialSmallIndexEndpointsUpTo_subset_budgeted
    (G : ℕ → ℕ) (x : ℕ) :
    factorialSmallIndexEndpointsUpTo G x ⊆
      factorialBudgetedEndpointsUpTo x
        (factorialSmallIndexParameterBudget G x)
        (factorialSmallIndexCoefficientBudget G x)
        (factorialSmallIndexGapBudget G x) := by
  intro n hn
  rw [factorialSmallIndexEndpointsUpTo, Finset.mem_image] at hn
  rcases hn with ⟨t, ht, rfl⟩
  rw [factorialBudgetedEndpointsUpTo, Finset.mem_image]
  exact ⟨t, factorialSmallIndexIntervalsUpTo_subset_budgeted G x ht, rfl⟩

/-- Exact finite count for the small-index endpoint subfamily. -/
theorem card_factorialSmallIndexEndpointsUpTo_le
    (G : ℕ → ℕ) (x : ℕ) (hx : 1 ≤ x) {δ : ℝ} (hδ : 0 < δ) :
    (factorialSmallIndexEndpointsUpTo G x).card ≤
      factorialSmallIndexParameterBudget G x *
        factorialSmallIndexCoefficientBudget G x ^ 2 *
        factorialSmallIndexGapBudget G x ^ 3 *
        factorialSquareRelationCountBudget δ x := by
  calc
    (factorialSmallIndexEndpointsUpTo G x).card ≤
        (factorialBudgetedEndpointsUpTo x
          (factorialSmallIndexParameterBudget G x)
          (factorialSmallIndexCoefficientBudget G x)
          (factorialSmallIndexGapBudget G x)).card :=
      Finset.card_le_card
        (factorialSmallIndexEndpointsUpTo_subset_budgeted G x)
    _ ≤ factorialSmallIndexParameterBudget G x *
        factorialSmallIndexCoefficientBudget G x ^ 2 *
        factorialSmallIndexGapBudget G x ^ 3 *
        factorialSquareRelationCountBudget δ x :=
      card_factorialBudgetedEndpointsUpTo_le _ _ _ _ hx
        (min_le_left _ _) (min_le_right _ _) hδ

/-! ## Power bounds for the concrete budgets -/

theorem factorialSmallIndexGapBudget_powerUpperBound_zero
    (G : ℕ → ℕ) (hG : PowerUpperBound (fun x => (G x : ℝ)) 0) :
    PowerUpperBound
      (fun x => (factorialSmallIndexGapBudget G x : ℝ)) 0 := by
  intro ε hε
  have hdom : (fun x => (factorialSmallIndexGapBudget G x : ℝ))
      =O[atTop] (fun x => (G x : ℝ)) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards with x
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _), one_mul,
      Real.norm_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast min_le_left (G x) x
  exact hdom.trans (by simpa using hG ε hε)

theorem factorialSmallIndexParameterBudget_powerUpperBound_zero
    (G : ℕ → ℕ) (hG : PowerUpperBound (fun x => (G x : ℝ)) 0) :
    PowerUpperBound
      (fun x => (factorialSmallIndexParameterBudget G x : ℝ)) 0 := by
  have hGap := factorialSmallIndexGapBudget_powerUpperBound_zero G hG
  have hLog : PowerUpperBound
      (fun x => (factorialSmallIndexLogBudget x : ℝ)) 0 := by
    simpa [factorialSmallIndexLogBudget] using
      (logarithmicSmoothnessBudget_powerUpperBound_zero
        (show (0 : ℝ) < 1 by norm_num))
  simpa [factorialSmallIndexParameterBudget, Nat.cast_mul] using hGap.mul hLog

/-- The rounded Lemma 4.3 coefficient envelope has power exponent `1/10`.
The deliberately slack rational exponent keeps every transcendental estimate
elementary: `log 4 = 2 log 2 ≤ 2`. -/
theorem factorialSmallIndexCoefficientEnvelope_powerUpperBound
    (G : ℕ → ℕ) (hG : PowerUpperBound (fun x => (G x : ℝ)) 0) :
    PowerUpperBound
      (fun x => (factorialSmallIndexCoefficientEnvelope G x : ℝ))
      (1 / 10 : ℝ) := by
  have hA := factorialSmallIndexParameterBudget_powerUpperBound_zero G hG
  intro ε hε
  have hη : 0 < ε / 20 := by positivity
  obtain ⟨C, hC⟩ := (hA (ε / 20) hη).bound
  let K : ℝ := |C| + 1
  let D : ℝ := Real.exp (6 *
    (3 + Real.log K + Real.log 3 / 100)) + 1
  have hKone : 1 ≤ K := by
    dsimp only [K]
    linarith [abs_nonneg C]
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hKone
  have hlogTwo : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at h
    exact h
  have hlogFour : Real.log 4 ≤ 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
    linarith
  have hthreeLogFour : 3 * Real.log 4 ≤ 6 := by linarith
  have hthreeLogFourNonneg : 0 ≤ 3 * Real.log 4 := by positivity
  have hDnonneg : 0 ≤ D := by
    dsimp only [D]
    positivity
  refine IsBigO.of_bound D ?_
  filter_upwards [hC, eventually_ge_atTop (1 : ℕ)] with x hxA hxOne
  let A : ℕ := factorialSmallIndexParameterBudget G x
  let X : ℝ := (x : ℝ)
  have hXone : 1 ≤ X := by
    dsimp only [X]
    exact_mod_cast hxOne
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hXone
  have hXpowOne : 1 ≤ X ^ (ε / 20 : ℝ) :=
    Real.one_le_rpow hXone hη.le
  have hAnorm : (A : ℝ) ≤ C * X ^ (ε / 20 : ℝ) := by
    simpa [A, X, Real.norm_of_nonneg (Nat.cast_nonneg _),
      Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)] using hxA
  have hAle : (A : ℝ) ≤ K * X ^ (ε / 20 : ℝ) := by
    calc
      (A : ℝ) ≤ C * X ^ (ε / 20 : ℝ) := hAnorm
      _ ≤ K * X ^ (ε / 20 : ℝ) := by
        gcongr
        dsimp only [K]
        linarith [le_abs_self C]
  have hRone : 1 ≤ K * X ^ (ε / 20 : ℝ) := by
    nlinarith [hKone, hXpowOne]
  have hlogA : Real.log (A : ℝ) ≤
      Real.log K + (ε / 20) * Real.log X := by
    have hlogR : Real.log (K * X ^ (ε / 20 : ℝ)) =
        Real.log K + (ε / 20) * Real.log X := by
      rw [Real.log_mul hKpos.ne'
        (ne_of_gt (Real.rpow_pos_of_pos hXpos _)), Real.log_rpow hXpos]
    by_cases hAzero : A = 0
    · rw [hAzero, Nat.cast_zero, Real.log_zero, hlogR.symm]
      exact Real.log_nonneg hRone
    · calc
        Real.log (A : ℝ) ≤ Real.log (K * X ^ (ε / 20 : ℝ)) :=
          Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hAzero) hAle
        _ = Real.log K + (ε / 20) * Real.log X := hlogR
  have hshiftPos : (0 : ℝ) < x + 2 := by positivity
  have hthreeXPos : (0 : ℝ) < 3 * X := by positivity
  have hshiftLe : (x + 2 : ℝ) ≤ 3 * X := by
    dsimp only [X]
    norm_cast
    omega
  have hlogShift : Real.log (x + 2) ≤ Real.log 3 + Real.log X := by
    calc
      Real.log (x + 2) ≤ Real.log (3 * X) :=
        Real.log_le_log hshiftPos hshiftLe
      _ = Real.log 3 + Real.log X := by
        rw [Real.log_mul (by norm_num) hXpos.ne']
  have hbaseNonneg : 0 ≤
      3 + Real.log K + Real.log 3 / 100 := by
    have hklog : 0 ≤ Real.log K := Real.log_nonneg hKone
    have hlogThree : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    positivity
  have hinside :
      3 + Real.log (A : ℝ) + Real.log (x + 2) / 100 ≤
        (3 + Real.log K + Real.log 3 / 100) +
          (ε / 20 + 1 / 100) * Real.log X := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    nlinarith [hlogA, hlogShift]
  have hlogXNonneg : 0 ≤ Real.log X := Real.log_nonneg hXone
  have hcoefficient :
      3 * Real.log 4 *
          (3 + Real.log (A : ℝ) + Real.log (x + 2) / 100) ≤
        6 * (3 + Real.log K + Real.log 3 / 100) +
          (1 / 10 + ε) * Real.log X := by
    calc
      3 * Real.log 4 *
          (3 + Real.log (A : ℝ) + Real.log (x + 2) / 100) ≤
          3 * Real.log 4 *
            ((3 + Real.log K + Real.log 3 / 100) +
              (ε / 20 + 1 / 100) * Real.log X) :=
        mul_le_mul_of_nonneg_left hinside hthreeLogFourNonneg
      _ ≤ 6 *
            ((3 + Real.log K + Real.log 3 / 100) +
              (ε / 20 + 1 / 100) * Real.log X) := by
        gcongr
      _ ≤ 6 * (3 + Real.log K + Real.log 3 / 100) +
          (1 / 10 + ε) * Real.log X := by
        have hscale : 6 * (ε / 20 + 1 / 100) ≤ 1 / 10 + ε := by
          linarith
        nlinarith
  have hexp : Real.exp (3 * Real.log 4 *
        (3 + Real.log (A : ℝ) + Real.log (x + 2) / 100)) ≤
      Real.exp (6 * (3 + Real.log K + Real.log 3 / 100)) *
        X ^ (1 / 10 + ε : ℝ) := by
    calc
      Real.exp (3 * Real.log 4 *
          (3 + Real.log (A : ℝ) + Real.log (x + 2) / 100)) ≤
          Real.exp (6 * (3 + Real.log K + Real.log 3 / 100) +
            (1 / 10 + ε) * Real.log X) :=
        Real.exp_le_exp.mpr hcoefficient
      _ = Real.exp (6 * (3 + Real.log K + Real.log 3 / 100)) *
          X ^ (1 / 10 + ε : ℝ) := by
        rw [Real.exp_add, Real.rpow_def_of_pos hXpos]
        congr 2
        ring
  have hceil : (factorialSmallIndexCoefficientEnvelope G x : ℝ) <
      Real.exp (3 * Real.log 4 *
        (3 + Real.log (A : ℝ) + Real.log (x + 2) / 100)) + 1 := by
    simpa only [factorialSmallIndexCoefficientEnvelope, A] using
      Nat.ceil_lt_add_one (Real.exp_pos _).le
  have htargetOne : 1 ≤ X ^ (1 / 10 + ε : ℝ) :=
    Real.one_le_rpow hXone (by linarith)
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _),
    Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  calc
    (factorialSmallIndexCoefficientEnvelope G x : ℝ) ≤
        Real.exp (3 * Real.log 4 *
          (3 + Real.log (A : ℝ) + Real.log (x + 2) / 100)) + 1 := hceil.le
    _ ≤ Real.exp (6 * (3 + Real.log K + Real.log 3 / 100)) *
          X ^ (1 / 10 + ε : ℝ) + X ^ (1 / 10 + ε : ℝ) :=
      add_le_add hexp htargetOne
    _ = D * X ^ (1 / 10 + ε : ℝ) := by
      dsimp only [D]
      ring

/-- Truncation only decreases the coefficient envelope. -/
theorem factorialSmallIndexCoefficientBudget_powerUpperBound
    (G : ℕ → ℕ) (hG : PowerUpperBound (fun x => (G x : ℝ)) 0) :
    PowerUpperBound
      (fun x => (factorialSmallIndexCoefficientBudget G x : ℝ))
      (1 / 10 : ℝ) := by
  have hEnvelope :=
    factorialSmallIndexCoefficientEnvelope_powerUpperBound G hG
  intro ε hε
  have hdom : (fun x => (factorialSmallIndexCoefficientBudget G x : ℝ))
      =O[atTop]
        (fun x => (factorialSmallIndexCoefficientEnvelope G x : ℝ)) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards with x
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _), one_mul,
      Real.norm_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast min_le_right x (factorialSmallIndexCoefficientEnvelope G x)
  exact hdom.trans (hEnvelope ε hε)

/-- Complete abstract small-index branch: a subpolynomial length budget and
the fixed threshold `a ≤ H log(x+2)/100` give at most
`x^(1/4+o(1))` endpoint values. -/
theorem factorialSmallIndexEndpointCount_powerUpperBound
    (G : ℕ → ℕ) (hG : PowerUpperBound (fun x => (G x : ℝ)) 0) :
    PowerUpperBound
      (fun x => ((factorialSmallIndexEndpointsUpTo G x).card : ℝ))
      (1 / 4 : ℝ) := by
  have hA := factorialSmallIndexParameterBudget_powerUpperBound_zero G hG
  have hC := factorialSmallIndexCoefficientBudget_powerUpperBound G hG
  have hGap := factorialSmallIndexGapBudget_powerUpperBound_zero G hG
  have hCtwo : PowerUpperBound
      (fun x => (factorialSmallIndexCoefficientBudget G x : ℝ) ^ 2)
      (1 / 5 : ℝ) := by
    convert hC.mul hC using 1 <;> norm_num [pow_two]
  have hGapTwo : PowerUpperBound
      (fun x => (factorialSmallIndexGapBudget G x : ℝ) ^ 2) 0 := by
    simpa [pow_two] using hGap.mul hGap
  have hGapThree : PowerUpperBound
      (fun x => (factorialSmallIndexGapBudget G x : ℝ) ^ 3) 0 := by
    simpa [pow_succ, mul_assoc] using hGapTwo.mul hGap
  have hRelation := factorialSquareRelationCountBudget_powerUpperBound
    (show (0 : ℝ) < 1 / 20 by norm_num)
  have hProduct : PowerUpperBound
      (fun x =>
        (factorialSmallIndexParameterBudget G x : ℝ) *
          (factorialSmallIndexCoefficientBudget G x : ℝ) ^ 2 *
          (factorialSmallIndexGapBudget G x : ℝ) ^ 3 *
          (factorialSquareRelationCountBudget (1 / 20) x : ℝ))
      (1 / 4 : ℝ) := by
    have hRaw := ((hA.mul hCtwo).mul hGapThree).mul hRelation
    norm_num at hRaw
    simpa [mul_assoc] using hRaw
  intro ε hε
  have hdom :
      (fun x => ((factorialSmallIndexEndpointsUpTo G x).card : ℝ))
        =O[atTop]
      (fun x =>
        (factorialSmallIndexParameterBudget G x : ℝ) *
          (factorialSmallIndexCoefficientBudget G x : ℝ) ^ 2 *
          (factorialSmallIndexGapBudget G x : ℝ) ^ 3 *
          (factorialSquareRelationCountBudget (1 / 20) x : ℝ)) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with x hx
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _), one_mul,
      Real.norm_of_nonneg (by positivity)]
    exact_mod_cast card_factorialSmallIndexEndpointsUpTo_le G x hx
      (show (0 : ℝ) < 1 / 20 by norm_num)
  exact hdom.trans (hProduct ε hε)

/-- Source-facing closure: once an external argument (Lemma 4.2 in Tao's
proof) eventually bounds every interval length by `G`, the literal
small-index endpoint family has the same `1/4+o(1)` upper bound. -/
theorem factorialSmallIndexSourceEndpointCount_powerUpperBound
    (G : ℕ → ℕ) (hG : PowerUpperBound (fun x => (G x : ℝ)) 0)
    (hcover : ∀ᶠ x : ℕ in atTop,
      ∀ t ∈ nontrivialFactorialThreeIntervalsUpTo x, t.2 ≤ G x) :
    PowerUpperBound
      (fun x => ((factorialSmallIndexSourceEndpointsUpTo x).card : ℝ))
      (1 / 4 : ℝ) := by
  have hcount := factorialSmallIndexEndpointCount_powerUpperBound G hG
  intro ε hε
  have hdom :
      (fun x => ((factorialSmallIndexSourceEndpointsUpTo x).card : ℝ))
        =O[atTop]
      (fun x => ((factorialSmallIndexEndpointsUpTo G x).card : ℝ)) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [hcover] with x hx
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _), one_mul,
      Real.norm_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast Finset.card_le_card
      (factorialSmallIndexSourceEndpointsUpTo_subset G hx)
  exact hdom.trans (hcount ε hε)

end

end Tao2026
