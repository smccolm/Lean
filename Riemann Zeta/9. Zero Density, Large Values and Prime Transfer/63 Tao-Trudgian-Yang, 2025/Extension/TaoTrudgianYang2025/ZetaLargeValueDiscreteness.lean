import TaoTrudgianYang2025.LargeValueExponent
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Discreteness of the zeta large-value exponent

A negative cardinality exponent forces the actual finite ordinate set to
be empty in one uniform parameter window. This proves the negative-exponent
part of ANTEDB Lemma 8.4, including the infimum-to-uniform-bound bridge.

The final maximum-to-double lemma is the algebraic/discreteness step in the
twelfth-moment argument. It does not supply Ivić's analytic large-values
estimate. In particular, the maximum in Lemma 8.11 is not replaced by a
minimum as in the displayed online proof of Theorem 9.7.
-/

noncomputable section

open Filter Set

namespace TaoTrudgianYang2025

/-- Infimum upper bounds give the exact epsilon--delta formulation. The
epsilon slack pays for approximating the infimum by a genuine candidate. -/
theorem isZetaLargeValueBound_of_exponent_le {σ τ B : ℝ}
    (h : zetaLargeValueExponent σ τ ≤ (B : EReal)) :
    IsZetaLargeValueBound σ τ B := by
  intro ε hε
  have hlt : zetaLargeValueExponent σ τ < ((B + ε / 2 : ℝ) : EReal) :=
    h.trans_lt (EReal.coe_lt_coe_iff.mpr (by linarith))
  obtain ⟨x, ⟨ρ, hρ, rfl⟩, hx⟩ := sInf_lt_iff.mp hlt
  have hρB : ρ < B + ε / 2 := EReal.coe_lt_coe_iff.mp hx
  obtain ⟨C, hC, δ, hδ, hbound⟩ := hρ (ε / 2) (by linarith)
  refine ⟨C, hC, δ, hδ, ?_⟩
  intro P hN hTl hTu hVl hVu
  exact (hbound P hN hTl hTu hVl hVu).trans
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith))
      (zero_le_one.trans hC))

theorem zetaLargeValueExponent_le_iff {σ τ B : ℝ} :
    zetaLargeValueExponent σ τ ≤ (B : EReal) ↔ IsZetaLargeValueBound σ τ B :=
  ⟨isZetaLargeValueBound_of_exponent_le, zetaLargeValueExponent_le_of_bound⟩

/-- A negative bound produces one common threshold and parameter radius
for which every actual admissible pattern has no ordinates. -/
theorem IsZetaLargeValueBound.exists_empty_threshold_of_neg {σ τ B : ℝ}
    (h : IsZetaLargeValueBound σ τ B) (hB : B < 0) :
    ∃ C δ : ℝ, 1 ≤ C ∧ 0 < δ ∧ ∀ P : ZetaLargeValuePattern, C ≤ P.N →
      P.N ^ (τ - δ) ≤ P.T → P.T ≤ P.N ^ (τ + δ) →
      P.N ^ (σ - δ) ≤ P.V → P.V ≤ P.N ^ (σ + δ) → P.ordinates = ∅ := by
  let ε : ℝ := -B / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨C, hC, δ, hδ, hbound⟩ := h ε hε
  have hlimit : Tendsto (fun N : ℝ => C * N ^ (-ε)) atTop (nhds (0 : ℝ)) := by
    simpa using tendsto_const_nhds.mul (tendsto_rpow_neg_atTop hε)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    ((tendsto_order.mp hlimit).2 (1 : ℝ) (by norm_num))
  refine ⟨max C N₀, δ, hC.trans (le_max_left _ _), hδ, ?_⟩
  intro P hN hTl hTu hVl hVu
  have hcard := hbound P ((le_max_left _ _).trans hN) hTl hTu hVl hVu
  have hexp : B + ε = -ε := by dsimp [ε]; ring
  rw [hexp] at hcard
  have hsmall : (P.ordinates.card : ℝ) < 1 :=
    hcard.trans_lt (hN₀ P.N ((le_max_right _ _).trans hN))
  have hnat : P.ordinates.card < 1 := by exact_mod_cast hsmall
  exact Finset.card_eq_zero.mp (by omega)

/-- Eventual emptiness derived for the actual patterns gives every real
cardinality bound; no replacement pattern or extra separation is used. -/
theorem zetaLargeValueBound_of_empty_threshold {σ τ : ℝ}
    (h : ∃ C δ : ℝ, 1 ≤ C ∧ 0 < δ ∧ ∀ P : ZetaLargeValuePattern, C ≤ P.N →
      P.N ^ (τ - δ) ≤ P.T → P.T ≤ P.N ^ (τ + δ) →
      P.N ^ (σ - δ) ≤ P.V → P.V ≤ P.N ^ (σ + δ) → P.ordinates = ∅)
    (B : ℝ) : IsZetaLargeValueBound σ τ B := by
  obtain ⟨C, δ, hC, hδ, hbound⟩ := h
  intro ε _
  refine ⟨C, hC, δ, hδ, ?_⟩
  intro P hN hTl hTu hVl hVu
  rw [hbound P hN hTl hTu hVl hVu, Finset.card_empty, Nat.cast_zero]
  exact mul_nonneg (zero_le_one.trans hC)
    (Real.rpow_nonneg (zero_lt_one.trans P.one_lt_N).le _)

theorem IsZetaLargeValueBound.any_of_neg {σ τ B : ℝ}
    (h : IsZetaLargeValueBound σ τ B) (hB : B < 0) (A : ℝ) :
    IsZetaLargeValueBound σ τ A :=
  zetaLargeValueBound_of_empty_threshold (h.exists_empty_threshold_of_neg hB) A

/-- A negative extended-real zeta exponent is necessarily negative infinity,
because the objects being bounded are actual finite-set cardinalities. -/
theorem zetaLargeValueExponent_eq_bot_of_neg {σ τ : ℝ}
    (h : zetaLargeValueExponent σ τ < 0) : zetaLargeValueExponent σ τ = ⊥ := by
  obtain ⟨x, ⟨B, hB, rfl⟩, hx⟩ := sInf_lt_iff.mp h
  have hneg : B < 0 := EReal.coe_lt_coe_iff.mp hx
  apply (EReal.eq_bot_iff_forall_lt _).mpr
  intro A
  exact (zetaLargeValueExponent_le_of_bound (hB.any_of_neg hneg (A - 1))).trans_lt
    (EReal.coe_lt_coe_iff.mpr (by linarith))

theorem zetaLargeValueExponent_eq_bot_iff_neg (σ τ : ℝ) :
    zetaLargeValueExponent σ τ = ⊥ ↔ zetaLargeValueExponent σ τ < 0 := by
  constructor
  · intro h
    rw [h]
    exact EReal.bot_lt_coe 0
  · exact zetaLargeValueExponent_eq_bot_of_neg

/-- The exact uniform-window characterization of negative infinity. -/
theorem zetaLargeValueExponent_eq_bot_iff_empty_threshold (σ τ : ℝ) :
    zetaLargeValueExponent σ τ = ⊥ ↔
      ∃ C δ : ℝ, 1 ≤ C ∧ 0 < δ ∧ ∀ P : ZetaLargeValuePattern, C ≤ P.N →
        P.N ^ (τ - δ) ≤ P.T → P.T ≤ P.N ^ (τ + δ) →
        P.N ^ (σ - δ) ≤ P.V → P.V ≤ P.N ^ (σ + δ) → P.ordinates = ∅ := by
  constructor
  · intro h
    have hb : IsZetaLargeValueBound σ τ (-1) :=
      isZetaLargeValueBound_of_exponent_le (by rw [h]; exact bot_le)
    exact hb.exists_empty_threshold_of_neg (by norm_num)
  · intro h
    apply zetaLargeValueExponent_eq_bot_of_neg
    exact (zetaLargeValueExponent_le_of_bound
      (zetaLargeValueBound_of_empty_threshold h (-1))).trans_lt (by norm_num)

/-- The legitimate branch reduction in the twelfth-moment argument. If
`a ≥ 0`, the maximum is `2a`; otherwise discreteness gives negative infinity.
This is not a proof of the analytic maximum bound supplied as input. -/
theorem zetaLargeValueExponent_le_double_of_le_max {σ τ a : ℝ}
    (h : zetaLargeValueExponent σ τ ≤ ((max a (2 * a) : ℝ) : EReal)) :
    zetaLargeValueExponent σ τ ≤ ((2 * a : ℝ) : EReal) := by
  by_cases ha : 0 ≤ a
  · simpa only [max_eq_right (by linarith : a ≤ 2 * a)] using h
  · have ha : a < 0 := lt_of_not_ge ha
    have hneg : zetaLargeValueExponent σ τ < 0 :=
      h.trans_lt (by exact_mod_cast (max_lt ha (by linarith : 2 * a < 0)))
    rw [zetaLargeValueExponent_eq_bot_of_neg hneg]
    exact bot_le

end TaoTrudgianYang2025
