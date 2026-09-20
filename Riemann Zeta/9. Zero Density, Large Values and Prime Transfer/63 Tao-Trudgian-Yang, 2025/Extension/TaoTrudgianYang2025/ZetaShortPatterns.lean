import TaoTrudgianYang2025.ZetaIntervalCutoff
import TaoTrudgianYang2025.ZetaPointwiseNonexistence
import TaoTrudgianYang2025.EnergyExponents
import GuthMaynard.TerminalTypeI
import GuthMaynard.TypeIFiniteEstimates

/-!
# Short coefficient-one patterns

First- and second-derivative bounds apply to the actual sharp interval,
including the possible left endpoint of the closed dyadic support.
-/

noncomputable section

open Complex Filter MeasureTheory Set
open RiemannZeta.GuthMaynard

namespace TaoTrudgianYang2025

private theorem dirichletPhase_eq_logarithmicPhase {n : ℕ} (hn : 0 < n) (t : ℝ) :
    dirichletPhase n t = unitaryPhase (logarithmicPhase t n) := by
  rw [unitaryPhase_logarithmicPhase_eq_cpow t n hn]
  unfold dirichletPhase
  congr 1
  ring

private theorem norm_closed_prefix_le {N : ℕ} (hN : 0 < N) (t B : ℝ) (hB : 0 ≤ B)
    (hprefix : ∀ j : ℕ, j ≤ N →
      ‖∑ n ∈ Finset.range j, unitaryPhase (logarithmicPhase t (N + 1 + n))‖ ≤ B)
    (j : ℕ) (hj : j ≤ N + 1) :
    ‖∑ n ∈ Finset.range j, dirichletPhase (N + n) t‖ ≤ 1 + B := by
  cases j with
  | zero => simpa using (show (0 : ℝ) ≤ 1 + B by linarith)
  | succ j =>
    rw [Finset.sum_range_succ']
    have htail : ‖∑ n ∈ Finset.range j, dirichletPhase (N + (n + 1)) t‖ ≤ B := by
      convert hprefix j (by omega) using 1
      congr 1
      apply Finset.sum_congr rfl
      intro n _
      rw [dirichletPhase_eq_logarithmicPhase (by omega)]
      congr 2
      push_cast
      ring
    have hphase : ‖dirichletPhase (N + 0) t‖ = 1 := by
      rw [Nat.add_zero, dirichletPhase_eq_logarithmicPhase hN]
      exact norm_unitaryPhase _
    exact (norm_add_le _ _).trans (by linarith)

private theorem norm_interval_le_of_prefix {N a b : ℕ} (hN : 0 < N)
    (hNa : N ≤ a) (hab : a ≤ b) (hb : b ≤ 2 * N) (t B : ℝ) (hB : 0 ≤ B)
    (hprefix : ∀ j : ℕ, j ≤ N →
      ‖∑ n ∈ Finset.range j, unitaryPhase (logarithmicPhase t (N + 1 + n))‖ ≤ B) :
    ‖∑ n ∈ Finset.Icc a b, dirichletPhase n t‖ ≤ 2 * (1 + B) := by
  have hbound (c : ℕ) (hc : c ≤ 2 * N + 1) :
      ‖∑ n ∈ Finset.Ico N c, dirichletPhase n t‖ ≤ 1 + B := by
    rw [Finset.sum_Ico_eq_sum_range]
    simpa only [Nat.add_comm] using norm_closed_prefix_le hN t B hB hprefix (c - N) (by omega)
  have heq : (∑ n ∈ Finset.Icc a b, dirichletPhase n t) =
      (∑ n ∈ Finset.Ico N (b + 1), dirichletPhase n t) -
        ∑ n ∈ Finset.Ico N a, dirichletPhase n t := by
    have hsets : Finset.Icc a b = Finset.Ico a (b + 1) := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega
    rw [hsets, ← Finset.sum_Ico_consecutive (fun n => dirichletPhase n t) hNa
      (by omega : a ≤ b + 1)]
    ring
  rw [heq]
  exact (norm_sub_le _ _).trans (by linarith [hbound (b + 1) (by omega), hbound a (by omega)])

theorem ZetaLargeValuePattern.polynomial_norm_le_short_majorant (P : ZetaLargeValuePattern)
    {t : ℝ} (ht : 1 ≤ t) (htN : t ≤ P.N ^ 2) :
    ‖∑ n ∈ P.indices, P.coeff n * dirichletPhase n t‖ ≤
      2 + 200 * Real.sqrt t + 12 * Real.pi * P.N / t := by
  let B : ℝ := 100 * Real.sqrt t + 6 * Real.pi * P.N / t
  have hNpos : 0 < P.scale := by
    have := zero_lt_one.trans P.one_lt_N
    rw [P.N_eq_scale] at this
    exact_mod_cast this
  have hB : 0 ≤ B := by
    dsimp [B]
    have := (zero_lt_one.trans P.one_lt_N).le
    positivity
  have hprefix : ∀ j : ℕ, j ≤ P.scale →
      ‖∑ n ∈ Finset.range j, unitaryPhase (logarithmicPhase t (P.scale + 1 + n))‖ ≤ B := by
    intro j hj
    by_cases hNt : P.N ≤ t
    · apply (norm_logarithmicPhase_prefix_le_sqrt P.scale j t hNpos hj
        (P.N_eq_scale ▸ hNt) (P.N_eq_scale ▸ htN)).trans
      dsimp [B]
      have := (zero_lt_one.trans P.one_lt_N).le
      exact le_add_of_nonneg_right (by positivity)
    · apply (norm_logarithmicPhase_prefix_le_div P.scale j t hNpos hj ht
        (P.N_eq_scale ▸ (le_of_not_ge hNt))).trans
      rw [← P.N_eq_scale]
      dsimp [B]
      exact le_add_of_nonneg_left (by positivity)
  rw [P.polynomial_eq_active_sum]
  by_cases hne : P.active.Nonempty
  · obtain ⟨a, b, ha⟩ := P.active_isInterval
    obtain ⟨hab, hNa, hb⟩ := P.active_interval_bounds ha hne
    rw [P.N_eq_scale] at hNa hb
    have h := norm_interval_le_of_prefix hNpos (by exact_mod_cast hNa) hab
      (by exact_mod_cast hb) t B hB hprefix
    rw [← ha] at h
    convert h using 1
    dsimp [B]
    ring
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty, norm_zero]
    have := (zero_lt_one.trans P.one_lt_N).le
    positivity

/-- A uniform actual-pattern nonexistence statement. The empty ordinate
set is derived from cancellation, not imposed in the pattern definition. -/
theorem exists_zetaShort_empty_uniform_threshold {σ τ : ℝ}
    (hσ : 3 / 4 ≤ σ) (hτ : 1 ≤ τ) (hτhi : τ < 3 / 2) :
    ∃ C δ : ℝ, 1 ≤ C ∧ 0 < δ ∧ ∀ P : ZetaLargeValuePattern, C ≤ P.N →
      P.N ^ (τ - δ) ≤ P.T → P.T ≤ P.N ^ (τ + δ) →
      P.N ^ (σ - δ) ≤ P.V → P.ordinates = ∅ := by
  let δ : ℝ := (3 / 2 - τ) / 8
  let β : ℝ := 3 / 4 - 2 * δ
  let K : ℝ := 2 + 200 * Real.sqrt 2 + 12 * Real.pi
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hδhi : δ ≤ 1 / 16 := by dsimp [δ]; linarith
  have hτδ : τ + 8 * δ = 3 / 2 := by dsimp [δ]; ring
  have hβ : 0 ≤ β := by dsimp [β]; linarith
  have hβδ : δ ≤ β := by dsimp [β]; linarith
  have hevent : ∀ᶠ N : ℝ in atTop, K < N ^ δ :=
    (tendsto_rpow_atTop hδ).eventually (eventually_gt_atTop K)
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 hevent
  refine ⟨max 4 N₀, δ, (by have := le_max_left (4 : ℝ) N₀; linarith), hδ, ?_⟩
  intro P hN hTl hTu hVl
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro t ht
  have hNfour : 4 ≤ P.N := (le_max_left _ _).trans hN
  have hNpos : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have htint : t ∈ Icc P.T (2 * P.T) := by
    simpa only [P.intervalLeft_eq, P.intervalRight_eq] using P.ordinates_in_interval t ht
  have htone : 1 ≤ t := (Real.one_le_rpow P.one_lt_N.le
    (by linarith : 0 ≤ τ - δ)).trans (hTl.trans htint.1)
  have htupper : t ≤ 2 * P.N ^ (3 / 2 : ℝ) := htint.2.trans
    ((mul_le_mul_of_nonneg_left hTu (by norm_num)).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le
        (by linarith : τ + δ ≤ 3 / 2)) (by norm_num)))
  have hhalf : 2 ≤ P.N ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    exact (by norm_num : (2 : ℝ) = Real.sqrt 4) ▸ Real.sqrt_le_sqrt hNfour
  have htNsq : t ≤ P.N ^ 2 := by
    calc
      _ ≤ 2 * P.N ^ (3 / 2 : ℝ) := htupper
      _ ≤ P.N ^ (1 / 2 : ℝ) * P.N ^ (3 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right hhalf (Real.rpow_nonneg hNpos.le _)
      _ = _ := by rw [← Real.rpow_add hNpos]; norm_num
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
        (hN₀ P.N ((le_max_right _ _).trans hN)) (Real.rpow_pos_of_pos hNpos _)
      _ = P.N ^ (δ + β) := (Real.rpow_add hNpos _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by dsimp [β]; linarith)
  exact (not_lt_of_ge hVl) (((P.large t ht).trans
    ((P.polynomial_norm_le_short_majorant htone htNsq).trans hmajorant)).trans_lt hstrict)

theorem zetaShort_largeValueBound_any {σ τ : ℝ}
    (hσ : 3 / 4 ≤ σ) (hτ : 1 ≤ τ) (hτhi : τ < 3 / 2) (B : ℝ) :
    IsZetaLargeValueBound σ τ B := by
  obtain ⟨C, δ, hC, hδ, h⟩ := exists_zetaShort_empty_uniform_threshold hσ hτ hτhi
  intro ε _
  refine ⟨C, hC, δ, hδ, ?_⟩
  intro P hN hTl hTu hVl _
  rw [h P hN hTl hTu hVl, Finset.card_empty, Nat.cast_zero]
  exact mul_nonneg (zero_le_one.trans hC) (Real.rpow_nonneg (zero_lt_one.trans P.one_lt_N).le _)

theorem zetaShort_energyBound_any {σ τ : ℝ}
    (hσ : 3 / 4 ≤ σ) (hτ : 1 ≤ τ) (hτhi : τ < 3 / 2) (B : ℝ) :
    IsZetaLargeValueEnergyBound σ τ B := by
  have h := (zetaShort_largeValueBound_any hσ hτ hτhi (B / 3)).toEnergyBound_three_mul
  convert h using 1
  ring

theorem zetaShort_largeValueExponent_eq_bot {σ τ : ℝ}
    (hσ : 3 / 4 ≤ σ) (hτ : 1 ≤ τ) (hτhi : τ < 3 / 2) :
    zetaLargeValueExponent σ τ = ⊥ := by
  apply zetaLargeValueExponent_eq_bot_of_neg
  exact (zetaLargeValueExponent_le_of_bound
    (zetaShort_largeValueBound_any hσ hτ hτhi (-1))).trans_lt (by norm_num)

/-- The short-range cancellation theorem also gives the source-shaped
strict power saving on every literal sharp interval, not just a predicate
about cardinalities of supplied patterns. -/
theorem zetaShort_pointwise_powerSaving {σ τ : ℝ}
    (hσ : 3 / 4 ≤ σ) (hτ : 1 ≤ τ) (hτhi : τ < 3 / 2) :
    ∃ C δ : ℝ, 1 ≤ C ∧ 0 < δ ∧ ∀ (N : ℕ) (I : Finset ℕ) (t : ℝ),
      C ≤ (N : ℝ) → IsIntegerInterval I → I ⊆ Finset.Icc N (2 * N) →
      (N : ℝ) ^ (τ - δ) ≤ t → t ≤ (N : ℝ) ^ (τ + δ) →
      ‖∑ n ∈ I, dirichletPhase n t‖ < (N : ℝ) ^ (σ - δ) :=
  exists_zetaPointwise_powerSaving_of_exponent_eq_bot
    (zetaShort_largeValueExponent_eq_bot hσ hτ hτhi)

end TaoTrudgianYang2025
