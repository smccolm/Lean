import Tao2026.FactorialLargeSieveMaximal

open Filter Asymptotics
open scoped BigOperators Chebyshev

namespace Tao2026

noncomputable section

theorem prod_factorialUpperHalfPrimes_dvd_squarefreeComponent_factorial
    (a : ℕ) :
    ∏ p ∈ factorialUpperHalfPrimes a, p ∣
      squarefreeComponent a.factorial := by
  rw [← Nat.prod_primeFactors_of_squarefree
    (squarefree_squarefreeComponent a.factorial)]
  apply Finset.prod_dvd_prod_of_subset
  intro p hp
  rw [mem_primeFactors_squarefreeComponent_iff]
  have hpData := Finset.mem_filter.mp hp
  have hpBounds := Finset.mem_Ioc.mp hpData.1
  have hfac := factorization_factorial_eq_one_of_half_lt
    hpData.2 hpBounds.1 hpBounds.2
  refine ⟨?_, ?_⟩
  · rw [Nat.mem_primeFactors]
    exact ⟨hpData.2, Nat.dvd_factorial hpData.2.pos hpBounds.2,
      Nat.factorial_ne_zero a⟩
  · rw [hfac]
    exact odd_one

theorem eventually_log_squarefreeComponent_factorial_lower :
    ∀ᶠ a : ℕ in atTop,
      (a : ℝ) / 4 ≤ Real.log (squarefreeComponent a.factorial : ℝ) := by
  filter_upwards [eventually_nat_factorialUpperHalfTheta_lower] with a ha
  let Q := factorialUpperHalfPrimes a
  have hprodPos : 0 < ∏ p ∈ Q, p := by
    apply Finset.prod_pos
    intro p hp
    exact_mod_cast (Finset.mem_filter.mp hp).2.pos
  have hcomponentPos : 0 < squarefreeComponent a.factorial :=
    squarefreeComponent_pos_of_positive ⟨a.factorial, Nat.factorial_pos a⟩
  have hprodLe : ∏ p ∈ Q, p ≤ squarefreeComponent a.factorial :=
    Nat.le_of_dvd hcomponentPos
      (prod_factorialUpperHalfPrimes_dvd_squarefreeComponent_factorial a)
  have hlogLe : Real.log (∏ p ∈ Q, p : ℕ) ≤
      Real.log (squarefreeComponent a.factorial : ℝ) := by
    apply Real.strictMonoOn_log.monotoneOn
    · show (0 : ℝ) < (∏ p ∈ Q, p : ℕ)
      exact_mod_cast hprodPos
    · show (0 : ℝ) < squarefreeComponent a.factorial
      exact_mod_cast hcomponentPos
    · exact_mod_cast hprodLe
  calc
    (a : ℝ) / 4 ≤
        Chebyshev.theta a - Chebyshev.theta ((a / 2 : ℕ) : ℝ) := ha
    _ = ∑ p ∈ Q, Real.log p := by
      symm
      exact sum_log_factorialUpperHalfPrimes_eq_theta_sub a
    _ = Real.log (∏ p ∈ Q, p : ℕ) := by
      symm
      push_cast
      rw [Real.log_prod]
      intro p hp
      exact_mod_cast (Finset.mem_filter.mp hp).2.ne_zero
    _ ≤ Real.log (squarefreeComponent a.factorial : ℝ) := hlogLe

noncomputable def factorialSquarefreeGrowthThreshold : ℕ :=
  Classical.choose
    (eventually_atTop.1 eventually_log_squarefreeComponent_factorial_lower)

theorem log_squarefreeComponent_factorial_lower
    {a : ℕ} (ha : factorialSquarefreeGrowthThreshold ≤ a) :
    (a : ℝ) / 4 ≤ Real.log (squarefreeComponent a.factorial : ℝ) :=
  Classical.choose_spec
    (eventually_atTop.1 eventually_log_squarefreeComponent_factorial_lower) a ha

noncomputable def factorialOneTermIndexBudget (x : ℕ) : ℕ :=
  factorialSquarefreeGrowthThreshold + logarithmicSmoothnessBudget 4 x

theorem factorialOneTerm_index_le_budget
    {x n a r : ℕ} (hn : n ≤ x) (hnpos : 1 ≤ n)
    (heq : n = r ^ 2 * squarefreeComponent a.factorial) :
    a ≤ factorialOneTermIndexBudget x := by
  by_cases haSmall : a < factorialSquarefreeGrowthThreshold
  · exact le_trans haSmall.le (Nat.le_add_right _ _)
  · have haThreshold : factorialSquarefreeGrowthThreshold ≤ a :=
      Nat.le_of_not_gt haSmall
    have hr : 1 ≤ r := by
      by_contra hr
      have : r = 0 := by omega
      simp [this] at heq
      omega
    have hsPos : 0 < squarefreeComponent a.factorial :=
      squarefreeComponent_pos_of_positive ⟨a.factorial, Nat.factorial_pos a⟩
    have hsLeN : squarefreeComponent a.factorial ≤ n := by
      rw [heq]
      have hrpow : 1 ≤ r ^ 2 := by nlinarith
      simpa only [one_mul] using
        Nat.mul_le_mul_right (squarefreeComponent a.factorial) hrpow
    have hsLeX2 : (squarefreeComponent a.factorial : ℝ) ≤ (x : ℝ) + 2 := by
      exact_mod_cast (hsLeN.trans (hn.trans (by omega : x ≤ x + 2)))
    have hlogLe : Real.log (squarefreeComponent a.factorial : ℝ) ≤
        Real.log ((x : ℝ) + 2) := by
      exact Real.strictMonoOn_log.monotoneOn
        (show (0 : ℝ) < squarefreeComponent a.factorial by
          exact_mod_cast hsPos)
        (show (0 : ℝ) < (x : ℝ) + 2 by positivity) hsLeX2
    have haReal : (a : ℝ) ≤ 4 * Real.log ((x : ℝ) + 2) := by
      have hgrowth := log_squarefreeComponent_factorial_lower haThreshold
      linarith
    have haCeil : a ≤ logarithmicSmoothnessBudget 4 x := by
      have hceilReal : (a : ℝ) ≤
          (⌈(4 : ℝ) * Real.log ((x : ℝ) + 2)⌉₊ : ℕ) :=
        haReal.trans (Nat.le_ceil _)
      change a ≤ ⌈(4 : ℝ) * Real.log ((x : ℝ) + 2)⌉₊
      exact_mod_cast hceilReal
    exact haCeil.trans (Nat.le_add_left _ _)

noncomputable def factorialThreeOneTermNumbersUpTo (x : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 x).filter fun n => n ∈ factorialThreeOneTermSet

theorem card_factorialThreeOneTermNumbersUpTo (x : ℕ) :
    (factorialThreeOneTermNumbersUpTo x).card =
      factorialThreeOneTermCount x := by
  rfl

noncomputable def factorialOneTermRepresentationsUpTo (x : ℕ) :
    Finset (ℕ × ℕ) :=
  (Finset.Icc 1 (factorialOneTermIndexBudget x)).product
    (Finset.Icc 1 (Nat.sqrt x))

noncomputable def factorialOneTermRepresentationEndpointsUpTo
    (x : ℕ) : Finset ℕ :=
  (factorialOneTermRepresentationsUpTo x).image fun ar =>
    ar.2 ^ 2 * squarefreeComponent ar.1.factorial

theorem factorialThreeOneTermNumbersUpTo_subset_representationEndpoints
    (x : ℕ) :
    factorialThreeOneTermNumbersUpTo x ⊆
      factorialOneTermRepresentationEndpointsUpTo x := by
  classical
  intro n hn
  have hnData := Finset.mem_filter.mp hn
  have hnRange := Finset.mem_Icc.mp hnData.1
  obtain ⟨a, r, ha, han, heq⟩ :=
    mem_factorialThreeOneTermSet_iff_exists_sq_mul.mp hnData.2
  have hsPos : 0 < squarefreeComponent a.factorial :=
    squarefreeComponent_pos_of_positive ⟨a.factorial, Nat.factorial_pos a⟩
  have hr : 1 ≤ r := by
    by_contra hr
    have : r = 0 := by omega
    simp [this] at heq
    omega
  have hrSqLeN : r ^ 2 ≤ n := by
    rw [heq]
    have hsOne : 1 ≤ squarefreeComponent a.factorial := hsPos
    nlinarith
  have hrSqrt : r ≤ Nat.sqrt x := by
    rw [Nat.le_sqrt']
    exact hrSqLeN.trans hnRange.2
  have haBudget : a ≤ factorialOneTermIndexBudget x :=
    factorialOneTerm_index_le_budget hnRange.2 hnRange.1 heq
  rw [factorialOneTermRepresentationEndpointsUpTo, Finset.mem_image]
  refine ⟨(a, r), ?_, heq.symm⟩
  simp [factorialOneTermRepresentationsUpTo, ha, haBudget, hr, hrSqrt]

theorem factorialThreeOneTermCount_le_indexBudget_mul_sqrt (x : ℕ) :
    factorialThreeOneTermCount x ≤
      factorialOneTermIndexBudget x * Nat.sqrt x := by
  rw [← card_factorialThreeOneTermNumbersUpTo]
  calc
    (factorialThreeOneTermNumbersUpTo x).card ≤
        (factorialOneTermRepresentationEndpointsUpTo x).card :=
      Finset.card_le_card
        (factorialThreeOneTermNumbersUpTo_subset_representationEndpoints x)
    _ ≤ (factorialOneTermRepresentationsUpTo x).card :=
      Finset.card_image_le
    _ = (Finset.Icc 1 (factorialOneTermIndexBudget x)).card *
        (Finset.Icc 1 (Nat.sqrt x)).card := by
      simp [factorialOneTermRepresentationsUpTo]
    _ ≤ factorialOneTermIndexBudget x * Nat.sqrt x := by
      gcongr <;> simp

theorem natConstant_powerUpperBound_zero (C : ℕ) :
    PowerUpperBound (fun _x : ℕ => (C : ℝ)) 0 := by
  intro ε hε
  refine IsBigO.of_bound (C : ℝ) ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with x hx
  have hxOne : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hpowOne : (1 : ℝ) ≤ (x : ℝ) ^ ε :=
    Real.one_le_rpow hxOne hε.le
  rw [Real.norm_of_nonneg (Nat.cast_nonneg C),
    Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg x) _), zero_add]
  exact le_mul_of_one_le_right (Nat.cast_nonneg C) hpowOne

theorem factorialOneTermIndexBudget_powerUpperBound_zero :
    PowerUpperBound (fun x => (factorialOneTermIndexBudget x : ℝ)) 0 := by
  simpa only [factorialOneTermIndexBudget, Nat.cast_add] using
    (natConstant_powerUpperBound_zero factorialSquarefreeGrowthThreshold).add
      (logarithmicSmoothnessBudget_powerUpperBound_zero
        (by norm_num : (0 : ℝ) < 4))

theorem natSqrt_powerUpperBound_half :
    PowerUpperBound (fun x => (Nat.sqrt x : ℝ)) (1 / 2 : ℝ) := by
  intro ε hε
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with x hx
  have hxOne : (1 : ℝ) ≤ x := by exact_mod_cast hx
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _),
    Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg x) _), one_mul]
  calc
    (Nat.sqrt x : ℝ) ≤ Real.sqrt (x : ℝ) := Real.nat_sqrt_le_real_sqrt
    _ = (x : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow x
    _ ≤ (x : ℝ) ^ ((1 / 2 : ℝ) + ε) :=
      Real.rpow_le_rpow_of_exponent_le hxOne (by linarith)

theorem factorialThreeOneTermCount_powerUpperBound :
    PowerUpperBound
      (fun x => (factorialThreeOneTermCount x : ℝ)) (1 / 2 : ℝ) := by
  have hproduct : PowerUpperBound
      (fun x => (factorialOneTermIndexBudget x : ℝ) *
        (Nat.sqrt x : ℝ)) ((0 : ℝ) + 1 / 2) :=
    factorialOneTermIndexBudget_powerUpperBound_zero.mul
      natSqrt_powerUpperBound_half
  have hdom : (fun x => (factorialThreeOneTermCount x : ℝ)) =O[atTop]
      (fun x => (factorialOneTermIndexBudget x : ℝ) *
        (Nat.sqrt x : ℝ)) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards with x
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _),
      Real.norm_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)),
      one_mul]
    exact_mod_cast factorialThreeOneTermCount_le_indexBudget_mul_sqrt x
  simpa only [zero_add] using fun ε hε => hdom.trans (hproduct ε hε)

theorem factorialThreeCount_powerUpperBound_of_lemma42
    (h42 : TaoLemma42Conclusion) :
    PowerUpperBound
      (fun x => (factorialThreeCount x : ℝ)) (1 / 2 : ℝ) := by
  have hsum :=
    (nontrivialFactorialThreeCount_powerUpperBound_of_lemma42 h42).add
      factorialThreeOneTermCount_powerUpperBound
  simpa only [← Nat.cast_add,
    nontrivialFactorialThreeCount_add_factorialThreeOneTermCount] using hsum

theorem factorialThreeCount_powerScale_of_lemma42
    (h42 : TaoLemma42Conclusion) :
    PowerScale (fun x => (factorialThreeCount x : ℝ)) (1 / 2 : ℝ) := by
  intro ε hε
  exact ⟨factorialThreeCount_powerUpperBound_of_lemma42 h42 ε hε,
    factorialThreeCount_powerScale_lower ε hε⟩

theorem taoTheorem19_of_lemma42
    (h42 : TaoLemma42Conclusion) : TaoTheorem19Conclusion :=
  ⟨nontrivialFactorialThreeCount_powerUpperBound_of_lemma42 h42,
    factorialThreeCount_powerScale_of_lemma42 h42⟩

theorem taoTheorem19_of_analytic_inputs
    (h25 : TaoTheorem25SpecializedConclusion)
    (h23ii : TaoProposition23iiConclusion) : TaoTheorem19Conclusion :=
  taoTheorem19_of_lemma42 (taoLemma42_of_inputs h25 h23ii)

theorem taoTheorem19_of_source_inputs
    (h25 : TaoTheorem25SpecializedConclusion)
    (hBHP : BakerHarmanPintzTheorem1Conclusion) : TaoTheorem19Conclusion :=
  taoTheorem19_of_lemma42 (taoLemma42_of_bakerHarmanPintz h25 hBHP)

/-- With Theorem 1.9 now internal, the factorial-equation conclusion needs
only the two genuinely external inputs used by Section 4. -/
theorem taoTheorem110_of_lemma42_and_erdosSelfridge
    (hES : ErdosSelfridgeSquareConclusion)
    (h42 : TaoLemma42Conclusion) : TaoTheorem110Conclusion :=
  taoTheorem110_of_theorem19_and_lemma42 hES
    (taoTheorem19_of_lemma42 h42) h42

theorem taoTheorem110_of_analytic_inputs_direct
    (hES : ErdosSelfridgeSquareConclusion)
    (h25 : TaoTheorem25SpecializedConclusion)
    (h23ii : TaoProposition23iiConclusion) : TaoTheorem110Conclusion :=
  taoTheorem110_of_lemma42_and_erdosSelfridge hES
    (taoLemma42_of_inputs h25 h23ii)

theorem taoTheorem110_of_source_inputs_direct
    (hES : ErdosSelfridgeSquareConclusion)
    (h25 : TaoTheorem25SpecializedConclusion)
    (hBHP : BakerHarmanPintzTheorem1Conclusion) : TaoTheorem110Conclusion :=
  taoTheorem110_of_lemma42_and_erdosSelfridge hES
    (taoLemma42_of_bakerHarmanPintz h25 hBHP)

end

end Tao2026
