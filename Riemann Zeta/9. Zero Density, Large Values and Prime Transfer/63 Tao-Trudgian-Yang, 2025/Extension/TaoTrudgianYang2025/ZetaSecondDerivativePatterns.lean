import TaoTrudgianYang2025.ZetaShortPatterns

/-!
# Full second-derivative nonexistence range for sharp zeta patterns

The actual sharp-interval bound excludes every ordinate when
`1/2 < sigma <= 1` and `1 <= tau < 2*sigma`.
The strict upper endpoint and the factor two in the height slab are retained.
-/

noncomputable section
open Complex Filter MeasureTheory Set
namespace TaoTrudgianYang2025

theorem exists_zetaSecondDerivative_empty_uniform_threshold {σ τ : ℝ}
    (hσLower : 1 / 2 < σ) (hσ : σ ≤ 1) (hτ : 1 ≤ τ) (hτhi : τ < 2 * σ) :
    ∃ C δ : ℝ, 1 ≤ C ∧ 0 < δ ∧ ∀ P : ZetaLargeValuePattern, C ≤ P.N →
      P.N ^ (τ - δ) ≤ P.T → P.T ≤ P.N ^ (τ + δ) →
      P.N ^ (σ - δ) ≤ P.V → P.ordinates = ∅ := by
  let δ : ℝ := min ((2 * σ - τ) / 16) (min ((2 - τ) / 16) (1 / 16))
  let β : ℝ := σ - 2 * δ
  let K : ℝ := 2 + 200 * Real.sqrt 2 + 12 * Real.pi
  have hτtwo : τ < 2 := by linarith
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδgap : δ ≤ (2 * σ - τ) / 16 := min_le_left _ _
  have hδtwo : δ ≤ (2 - τ) / 16 := (min_le_right _ _).trans (min_le_left _ _)
  have hδhi : δ ≤ 1 / 16 := (min_le_right _ _).trans (min_le_right _ _)
  have hβ : 0 ≤ β := by dsimp [β]; linarith only [hσLower, hδhi]
  have hβδ : δ ≤ β := by dsimp [β]; linarith
  have hevent : ∀ᶠ N : ℝ in atTop, max K 2 < N ^ δ :=
    (tendsto_rpow_atTop hδ).eventually (eventually_gt_atTop (max K 2))
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 hevent
  refine ⟨max 2 N₀, δ, (by have := le_max_left (2 : ℝ) N₀; linarith), hδ, ?_⟩
  intro P hN hTl hTu hVl
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro t ht
  have hNpos : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have htint : t ∈ Icc P.T (2 * P.T) := by
    simpa only [P.intervalLeft_eq, P.intervalRight_eq] using P.ordinates_in_interval t ht
  have htone : 1 ≤ t := (Real.one_le_rpow P.one_lt_N.le
    (by linarith : 0 ≤ τ - δ)).trans (hTl.trans htint.1)
  have hNδ : max K 2 < P.N ^ δ := hN₀ P.N ((le_max_right _ _).trans hN)
  have htNsq : t ≤ P.N ^ 2 := by
    calc
      _ ≤ 2 * P.N ^ (τ + δ) :=
        htint.2.trans (mul_le_mul_of_nonneg_left hTu (by norm_num))
      _ ≤ P.N ^ δ * P.N ^ (τ + δ) :=
        mul_le_mul_of_nonneg_right
          ((le_max_right K 2).trans hNδ.le) (Real.rpow_nonneg hNpos.le _)
      _ = P.N ^ (δ + (τ + δ)) := (Real.rpow_add hNpos _ _).symm
      _ ≤ _ := by
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by
          norm_num only [Nat.cast_ofNat]
          linarith)
  have hsqrt : Real.sqrt t ≤ Real.sqrt 2 * P.N ^ β := by
    have hpow : t ≤ 2 * P.N ^ (2 * β) := htint.2.trans
      ((mul_le_mul_of_nonneg_left hTu (by norm_num)).trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le
          (by dsimp [β]; linarith : τ + δ ≤ 2 * β)) (by norm_num)))
    calc
      _ ≤ Real.sqrt (2 * P.N ^ (2 * β)) := Real.sqrt_le_sqrt hpow
      _ = _ := by
        rw [Real.sqrt_mul (by norm_num), Real.sqrt_eq_rpow (P.N ^ (2 * β)),
          ← Real.rpow_mul hNpos.le]
        congr 2
        ring
  have hquot : P.N / t ≤ P.N ^ β := by
    apply (div_le_iff₀ (zero_lt_one.trans_le htone)).2
    calc
      _ = P.N ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ P.N ^ (β + (τ - δ)) :=
        Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith)
      _ = P.N ^ β * P.N ^ (τ - δ) := Real.rpow_add hNpos _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (hTl.trans htint.1) (Real.rpow_nonneg hNpos.le _)
  have hmajorant : 2 + 200 * Real.sqrt t + 12 * Real.pi * P.N / t ≤ K * P.N ^ β := by
    have hone := Real.one_le_rpow P.one_lt_N.le hβ
    have hq := mul_le_mul_of_nonneg_left hquot (by positivity : 0 ≤ 12 * Real.pi)
    dsimp [K]
    rw [← mul_div_assoc] at hq
    nlinarith
  have hstrict : K * P.N ^ β < P.N ^ (σ - δ) := by
    calc
      _ < P.N ^ δ * P.N ^ β := mul_lt_mul_of_pos_right
        ((le_max_left K 2).trans_lt hNδ) (Real.rpow_pos_of_pos hNpos _)
      _ = P.N ^ (δ + β) := (Real.rpow_add hNpos _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by dsimp [β]; linarith)
  exact (not_lt_of_ge hVl) (((P.large t ht).trans
    ((P.polynomial_norm_le_short_majorant htone htNsq).trans hmajorant)).trans_lt hstrict)

theorem zetaSecondDerivative_largeValueBound_any {σ τ : ℝ}
    (hσLower : 1 / 2 < σ) (hσ : σ ≤ 1) (hτ : 1 ≤ τ) (hτhi : τ < 2 * σ) (B : ℝ) :
    IsZetaLargeValueBound σ τ B := by
  obtain ⟨C, δ, hC, hδ, h⟩ := exists_zetaSecondDerivative_empty_uniform_threshold hσLower hσ hτ hτhi
  intro ε _
  refine ⟨C, hC, δ, hδ, ?_⟩
  intro P hN hTl hTu hVl _
  rw [h P hN hTl hTu hVl, Finset.card_empty, Nat.cast_zero]
  exact mul_nonneg (zero_le_one.trans hC) (Real.rpow_nonneg (zero_lt_one.trans P.one_lt_N).le _)

theorem zetaSecondDerivative_energyBound_any {σ τ : ℝ}
    (hσLower : 1 / 2 < σ) (hσ : σ ≤ 1) (hτ : 1 ≤ τ) (hτhi : τ < 2 * σ) (B : ℝ) :
    IsZetaLargeValueEnergyBound σ τ B := by
  have h := (zetaSecondDerivative_largeValueBound_any hσLower hσ hτ hτhi (B / 3)).toEnergyBound_three_mul
  convert h using 1
  ring

theorem zetaSecondDerivative_largeValueExponent_eq_bot {σ τ : ℝ}
    (hσLower : 1 / 2 < σ) (hσ : σ ≤ 1) (hτ : 1 ≤ τ) (hτhi : τ < 2 * σ) :
    zetaLargeValueExponent σ τ = ⊥ := by
  apply zetaLargeValueExponent_eq_bot_of_neg
  exact (zetaLargeValueExponent_le_of_bound
    (zetaSecondDerivative_largeValueBound_any hσLower hσ hτ hτhi (-1))).trans_lt (by norm_num)

/-- The short-range cancellation theorem also gives the source-shaped
strict power saving on every literal sharp interval, not just a predicate
about cardinalities of supplied patterns. -/
theorem zetaSecondDerivative_pointwise_powerSaving {σ τ : ℝ}
    (hσLower : 1 / 2 < σ) (hσ : σ ≤ 1) (hτ : 1 ≤ τ) (hτhi : τ < 2 * σ) :
    ∃ C δ : ℝ, 1 ≤ C ∧ 0 < δ ∧ ∀ (N : ℕ) (I : Finset ℕ) (t : ℝ),
      C ≤ (N : ℝ) → IsIntegerInterval I → I ⊆ Finset.Icc N (2 * N) →
      (N : ℝ) ^ (τ - δ) ≤ t → t ≤ (N : ℝ) ^ (τ + δ) →
      ‖∑ n ∈ I, dirichletPhase n t‖ < (N : ℝ) ^ (σ - δ) :=
  exists_zetaPointwise_powerSaving_of_exponent_eq_bot
    (zetaSecondDerivative_largeValueExponent_eq_bot hσLower hσ hτ hτhi)

end TaoTrudgianYang2025
