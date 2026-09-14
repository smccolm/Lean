import Tao2026.BadIntervalProbabilityUniform

/-!
# Finite typical-tuple summation

After Proposition 6.6, the source fixes dyadic prime scales and sums the
typical tuple count over every smooth remainder and every power-of-two interval
length.  This module formalizes that finite summation.  It deliberately stops
before enlarging the prime bands and mapping the resulting representations
into `B¹`; that bounded-multiplicity map is the next distinct counting step.
-/

namespace Tao2026

open Filter
open scoped Classical BigOperators

noncomputable section

set_option maxRecDepth 4000

/-- The product of the lower endpoints of the fixed dyadic prime bands, with
the distinguished zeroth coordinate occurring twice. -/
def taoPrimeTupleScaleDenominator (P : Fin 1001 → ℕ) : ℕ :=
  (P 0) ^ 2 * ∏ j ∈ (Finset.univ.erase (0 : Fin 1001)), P j

/-- The source's enlarged upper budget for the smooth remainder at fixed
dyadic prime scales. -/
def taoPrimeTupleRemainderBudget (x : ℕ) (P : Fin 1001 → ℕ) : ℕ :=
  2 * x / taoPrimeTupleScaleDenominator P

/-- The smoothness cutoff used when the last selected prime lies in its fixed
dyadic band. -/
def taoPrimeTupleRemainderSmoothnessCutoff (P : Fin 1001 → ℕ) : ℕ :=
  2 * P (Fin.last 1000)

/-- All smooth remainders in the source's enlarged fixed-scale budget. -/
def taoPrimeTupleSmoothRemainders
    (x : ℕ) (P : Fin 1001 → ℕ) : Finset ℕ :=
  Nat.smoothNumbersUpTo (taoPrimeTupleRemainderBudget x P)
    (taoPrimeTupleRemainderSmoothnessCutoff P + 1)

theorem mem_taoPrimeTupleSmoothRemainders
    {x : ℕ} {P : Fin 1001 → ℕ} {m' : ℕ} :
    m' ∈ taoPrimeTupleSmoothRemainders x P ↔
      m' ≤ taoPrimeTupleRemainderBudget x P ∧
        IsSmooth m' (taoPrimeTupleRemainderSmoothnessCutoff P) := by
  simp [taoPrimeTupleSmoothRemainders, mem_smoothNumbersUpTo_source]

theorem card_taoPrimeTupleSmoothRemainders
    (x : ℕ) (P : Fin 1001 → ℕ) :
    (taoPrimeTupleSmoothRemainders x P).card =
      psiNat (taoPrimeTupleRemainderBudget x P)
        (taoPrimeTupleRemainderSmoothnessCutoff P) := by
  rfl

/-- Pairs consisting of a permitted smooth remainder and a supported typical
prime tuple at one fixed interval length. -/
def taoPrimeTupleTypicalRemainderPairs
    (P : Fin 1001 → ℕ) (x H lowerPrime upperPrime : ℕ) :
    Finset (Σ _m' : ℕ, TaoPrimeTuple) :=
  (taoPrimeTupleSmoothRemainders x P).sigma fun m' =>
    taoPrimeTupleTypicalSupport P x H lowerPrime upperPrime m'

theorem mem_taoPrimeTupleTypicalRemainderPairs
    {P : Fin 1001 → ℕ} {x H lowerPrime upperPrime : ℕ}
    {a : Σ _m' : ℕ, TaoPrimeTuple} :
    a ∈ taoPrimeTupleTypicalRemainderPairs P x H lowerPrime upperPrime ↔
      a.1 ∈ taoPrimeTupleSmoothRemainders x P ∧
        a.2 ∈ taoPrimeTupleTypicalSupport P x H lowerPrime upperPrime a.1 := by
  simp [taoPrimeTupleTypicalRemainderPairs]

/-- Exact cardinality of the fixed-length remainder/tuple sigma family. -/
theorem card_taoPrimeTupleTypicalRemainderPairs
    (P : Fin 1001 → ℕ) (x H lowerPrime upperPrime : ℕ) :
    (taoPrimeTupleTypicalRemainderPairs P x H lowerPrime upperPrime).card =
      ∑ m' ∈ taoPrimeTupleSmoothRemainders x P,
        (taoPrimeTupleTypicalSupport P x H lowerPrime upperPrime m').card := by
  rw [taoPrimeTupleTypicalRemainderPairs, Finset.card_sigma]

/-- A pointwise supported-tuple estimate sums over all smooth remainders with
exactly the expected `Psi` factor. -/
theorem card_taoPrimeTupleTypicalRemainderPairs_cast_le
    (P : Fin 1001 → ℕ) (x H lowerPrime upperPrime : ℕ) {Q : ℝ}
    (hQ : ∀ m' ∈ taoPrimeTupleSmoothRemainders x P,
      ((taoPrimeTupleTypicalSupport P x H lowerPrime upperPrime m').card : ℝ) ≤ Q) :
    ((taoPrimeTupleTypicalRemainderPairs P x H lowerPrime upperPrime).card : ℝ) ≤
      (psiNat (taoPrimeTupleRemainderBudget x P)
          (taoPrimeTupleRemainderSmoothnessCutoff P) : ℝ) * Q := by
  rw [card_taoPrimeTupleTypicalRemainderPairs, Nat.cast_sum]
  calc
    (∑ m' ∈ taoPrimeTupleSmoothRemainders x P,
        ((taoPrimeTupleTypicalSupport P x H lowerPrime upperPrime m').card : ℝ)) ≤
        ∑ _m' ∈ taoPrimeTupleSmoothRemainders x P, Q := by
      exact Finset.sum_le_sum fun m' hm' => hQ m' hm'
    _ = ((taoPrimeTupleSmoothRemainders x P).card : ℝ) * Q := by simp
    _ = (psiNat (taoPrimeTupleRemainderBudget x P)
          (taoPrimeTupleRemainderSmoothnessCutoff P) : ℝ) * Q := by
      rw [card_taoPrimeTupleSmoothRemainders]

/-- Burgess-conditional fixed-scale tuple count after summing over every
smooth remainder, with the named constant independent of the scale family. -/
theorem eventually_forall_card_taoPrimeTupleTypicalRemainderPairs_le_withLower_uniformConstant_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    (hP : ∀ x j, (taoDyadicPrimeBand (P x j)).Nonempty)
    (lowerPrime : ℕ → ℕ) :
    ∀ᶠ x : ℕ in atTop, ∀ H : ℕ,
      1 ≤ H → H ≤ taoTypicalLengthCutoff x →
      ((taoPrimeTupleTypicalRemainderPairs (P x) x H
          (lowerPrime x)
          (taoLargePrimeSourceUpperCutoff x)).card : ℝ) ≤
        (psiNat (taoPrimeTupleRemainderBudget x (P x))
            (taoPrimeTupleRemainderSmoothnessCutoff (P x)) : ℝ) *
          ((taoPrimeTupleTypicalUniformSourceConstant hC hburgess *
                (8 * iteratedLog x) ^ (50 : ℕ) /
              ((H : ℝ) * Real.log (taoZ x) ^ (2 : ℕ))) *
            ∏ j, ((taoDyadicPrimeBand (P x j)).card : ℝ)) := by
  have htuple :=
    eventually_forall_card_taoPrimeTupleTypicalSupport_le_source_withLower_uniformConstant_of_explicitBurgess
      hC hburgess hscale hP lowerPrime
  filter_upwards [htuple] with x hx H hH hHcut
  apply card_taoPrimeTupleTypicalRemainderPairs_cast_le
  intro m' hm'
  exact hx H m' hH hHcut

/-- Existential compatibility wrapper for the fixed-scale remainder count. -/
theorem exists_eventually_forall_card_taoPrimeTupleTypicalRemainderPairs_le_withLower_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    (hP : ∀ x j, (taoDyadicPrimeBand (P x j)).Nonempty)
    (lowerPrime : ℕ → ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ x : ℕ in atTop, ∀ H : ℕ,
      1 ≤ H → H ≤ taoTypicalLengthCutoff x →
      ((taoPrimeTupleTypicalRemainderPairs (P x) x H
          (lowerPrime x)
          (taoLargePrimeSourceUpperCutoff x)).card : ℝ) ≤
        (psiNat (taoPrimeTupleRemainderBudget x (P x))
            (taoPrimeTupleRemainderSmoothnessCutoff (P x)) : ℝ) *
          ((B * (8 * iteratedLog x) ^ (50 : ℕ) /
              ((H : ℝ) * Real.log (taoZ x) ^ (2 : ℕ))) *
            ∏ j, ((taoDyadicPrimeBand (P x j)).card : ℝ)) := by
  exact ⟨taoPrimeTupleTypicalUniformSourceConstant hC hburgess,
    taoPrimeTupleTypicalUniformSourceConstant_pos hC hburgess,
    eventually_forall_card_taoPrimeTupleTypicalRemainderPairs_le_withLower_uniformConstant_of_explicitBurgess
      hC hburgess hscale hP lowerPrime⟩

/-- Fixed-`z^(9/10)` specialization of the smooth-remainder tuple count. -/
theorem exists_eventually_forall_card_taoPrimeTupleTypicalRemainderPairs_le_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    (hP : ∀ x j, (taoDyadicPrimeBand (P x j)).Nonempty) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ x : ℕ in atTop, ∀ H : ℕ,
      1 ≤ H → H ≤ taoTypicalLengthCutoff x →
      ((taoPrimeTupleTypicalRemainderPairs (P x) x H
          (taoZPowerFloor (9 / 10 : ℝ) x)
          (taoLargePrimeSourceUpperCutoff x)).card : ℝ) ≤
        (psiNat (taoPrimeTupleRemainderBudget x (P x))
            (taoPrimeTupleRemainderSmoothnessCutoff (P x)) : ℝ) *
          ((B * (8 * iteratedLog x) ^ (50 : ℕ) /
              ((H : ℝ) * Real.log (taoZ x) ^ (2 : ℕ))) *
            ∏ j, ((taoDyadicPrimeBand (P x j)).card : ℝ)) := by
  exact
    exists_eventually_forall_card_taoPrimeTupleTypicalRemainderPairs_le_withLower_of_explicitBurgess
      hC hburgess hscale hP (fun x => taoZPowerFloor (9 / 10 : ℝ) x)

/-- The full fixed-prime-scale sigma family after also summing over all
power-of-two lengths below the typical cutoff. -/
def taoPrimeTupleTypicalDyadicRemainderTriples
    (P : Fin 1001 → ℕ) (x lowerPrime upperPrime : ℕ) :
    Finset (Σ _r : ℕ, Σ _m' : ℕ, TaoPrimeTuple) :=
  (badIntervalTypicalDyadicExponents x).sigma fun r =>
    taoPrimeTupleTypicalRemainderPairs P x (2 ^ r) lowerPrime upperPrime

theorem mem_taoPrimeTupleTypicalDyadicRemainderTriples
    {P : Fin 1001 → ℕ} {x lowerPrime upperPrime : ℕ}
    {a : Σ _r : ℕ, Σ _m' : ℕ, TaoPrimeTuple} :
    a ∈ taoPrimeTupleTypicalDyadicRemainderTriples P x lowerPrime upperPrime ↔
      a.1 ∈ badIntervalTypicalDyadicExponents x ∧
        a.2 ∈ taoPrimeTupleTypicalRemainderPairs P x (2 ^ a.1)
          lowerPrime upperPrime := by
  simp [taoPrimeTupleTypicalDyadicRemainderTriples]

/-- Exact cardinality after the finite dyadic-length sum. -/
theorem card_taoPrimeTupleTypicalDyadicRemainderTriples
    (P : Fin 1001 → ℕ) (x lowerPrime upperPrime : ℕ) :
    (taoPrimeTupleTypicalDyadicRemainderTriples P x lowerPrime upperPrime).card =
      ∑ r ∈ badIntervalTypicalDyadicExponents x,
        (taoPrimeTupleTypicalRemainderPairs P x (2 ^ r)
          lowerPrime upperPrime).card := by
  rw [taoPrimeTupleTypicalDyadicRemainderTriples, Finset.card_sigma]

/-- The reciprocal power-of-two weights over the admissible dyadic-length
index set have total mass at most two. -/
theorem sum_badIntervalTypicalDyadicExponents_inv_two_pow_le_two (x : ℕ) :
    (∑ r ∈ badIntervalTypicalDyadicExponents x,
      (1 / (2 : ℝ)) ^ r) ≤ 2 := by
  exact sum_geometric_two_le _

/-- Burgess-conditional source count after the finite smooth-remainder and
dyadic-length sums, using the named scale-independent constant. -/
theorem eventually_card_taoPrimeTupleTypicalDyadicRemainderTriples_le_withLower_uniformConstant_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    (hP : ∀ x j, (taoDyadicPrimeBand (P x j)).Nonempty)
    (lowerPrime : ℕ → ℕ) :
    ∀ᶠ x : ℕ in atTop,
      ((taoPrimeTupleTypicalDyadicRemainderTriples (P x) x
          (lowerPrime x)
          (taoLargePrimeSourceUpperCutoff x)).card : ℝ) ≤
        ∑ r ∈ badIntervalTypicalDyadicExponents x,
          (psiNat (taoPrimeTupleRemainderBudget x (P x))
              (taoPrimeTupleRemainderSmoothnessCutoff (P x)) : ℝ) *
            ((taoPrimeTupleTypicalUniformSourceConstant hC hburgess *
                  (8 * iteratedLog x) ^ (50 : ℕ) /
                (((2 ^ r : ℕ) : ℝ) * Real.log (taoZ x) ^ (2 : ℕ))) *
              ∏ j, ((taoDyadicPrimeBand (P x j)).card : ℝ)) := by
  have hfixed :=
    eventually_forall_card_taoPrimeTupleTypicalRemainderPairs_le_withLower_uniformConstant_of_explicitBurgess
      hC hburgess hscale hP lowerPrime
  filter_upwards [hfixed, eventually_ge_atTop (2 : ℕ)] with x hx hxTwo
  rw [card_taoPrimeTupleTypicalDyadicRemainderTriples, Nat.cast_sum]
  apply Finset.sum_le_sum
  intro r hr
  have hcutoff : 0 < taoTypicalLengthCutoff x := by
    have hlog : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast hxTwo)
    have hcutoffReal : (0 : ℝ) < taoTypicalLengthCutoff x :=
      (pow_pos hlog 20).trans_le (taoTypicalLengthCutoff_spec x)
    exact_mod_cast hcutoffReal
  have hrle : r ≤ Nat.log 2 (taoTypicalLengthCutoff x) := by
    simp only [badIntervalTypicalDyadicExponents, Finset.mem_range] at hr
    omega
  have hpowle : 2 ^ r ≤ taoTypicalLengthCutoff x :=
    (Nat.pow_le_pow_right (by norm_num) hrle).trans
      (Nat.pow_log_le_self 2 hcutoff.ne')
  have hpowpos : 1 ≤ (2 : ℕ) ^ r := by
    have : 0 < (2 : ℕ) ^ r := pow_pos (by norm_num) r
    omega
  exact hx (2 ^ r) hpowpos hpowle

/-- Existential compatibility wrapper after the dyadic-length sum. -/
theorem exists_eventually_card_taoPrimeTupleTypicalDyadicRemainderTriples_le_withLower_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    (hP : ∀ x j, (taoDyadicPrimeBand (P x j)).Nonempty)
    (lowerPrime : ℕ → ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ x : ℕ in atTop,
      ((taoPrimeTupleTypicalDyadicRemainderTriples (P x) x
          (lowerPrime x)
          (taoLargePrimeSourceUpperCutoff x)).card : ℝ) ≤
        ∑ r ∈ badIntervalTypicalDyadicExponents x,
          (psiNat (taoPrimeTupleRemainderBudget x (P x))
              (taoPrimeTupleRemainderSmoothnessCutoff (P x)) : ℝ) *
            ((B * (8 * iteratedLog x) ^ (50 : ℕ) /
                (((2 ^ r : ℕ) : ℝ) * Real.log (taoZ x) ^ (2 : ℕ))) *
              ∏ j, ((taoDyadicPrimeBand (P x j)).card : ℝ)) := by
  exact ⟨taoPrimeTupleTypicalUniformSourceConstant hC hburgess,
    taoPrimeTupleTypicalUniformSourceConstant_pos hC hburgess,
    eventually_card_taoPrimeTupleTypicalDyadicRemainderTriples_le_withLower_uniformConstant_of_explicitBurgess
      hC hburgess hscale hP lowerPrime⟩

/-- Fixed-`z^(9/10)` specialization after summing the dyadic lengths. -/
theorem exists_eventually_card_taoPrimeTupleTypicalDyadicRemainderTriples_le_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    (hP : ∀ x j, (taoDyadicPrimeBand (P x j)).Nonempty) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ x : ℕ in atTop,
      ((taoPrimeTupleTypicalDyadicRemainderTriples (P x) x
          (taoZPowerFloor (9 / 10 : ℝ) x)
          (taoLargePrimeSourceUpperCutoff x)).card : ℝ) ≤
        ∑ r ∈ badIntervalTypicalDyadicExponents x,
          (psiNat (taoPrimeTupleRemainderBudget x (P x))
              (taoPrimeTupleRemainderSmoothnessCutoff (P x)) : ℝ) *
            ((B * (8 * iteratedLog x) ^ (50 : ℕ) /
                (((2 ^ r : ℕ) : ℝ) * Real.log (taoZ x) ^ (2 : ℕ))) *
              ∏ j, ((taoDyadicPrimeBand (P x j)).card : ℝ)) := by
  exact
    exists_eventually_card_taoPrimeTupleTypicalDyadicRemainderTriples_le_withLower_of_explicitBurgess
      hC hburgess hscale hP (fun x => taoZPowerFloor (9 / 10 : ℝ) x)

/-- The same source count with the dyadic-length sum evaluated and the named
scale-independent constant.  The geometric weights cost only factor two. -/
theorem eventually_card_taoPrimeTupleTypicalDyadicRemainderTriples_le_two_mul_withLower_uniformConstant_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    (hP : ∀ x j, (taoDyadicPrimeBand (P x j)).Nonempty)
    (lowerPrime : ℕ → ℕ) :
    ∀ᶠ x : ℕ in atTop,
      ((taoPrimeTupleTypicalDyadicRemainderTriples (P x) x
          (lowerPrime x)
          (taoLargePrimeSourceUpperCutoff x)).card : ℝ) ≤
        2 * (psiNat (taoPrimeTupleRemainderBudget x (P x))
            (taoPrimeTupleRemainderSmoothnessCutoff (P x)) : ℝ) *
          ((taoPrimeTupleTypicalUniformSourceConstant hC hburgess *
                (8 * iteratedLog x) ^ (50 : ℕ) /
              Real.log (taoZ x) ^ (2 : ℕ)) *
            ∏ j, ((taoDyadicPrimeBand (P x j)).card : ℝ)) := by
  let B := taoPrimeTupleTypicalUniformSourceConstant hC hburgess
  have hB : 0 < B := taoPrimeTupleTypicalUniformSourceConstant_pos hC hburgess
  have hsum :=
    eventually_card_taoPrimeTupleTypicalDyadicRemainderTriples_le_withLower_uniformConstant_of_explicitBurgess
      hC hburgess hscale hP lowerPrime
  filter_upwards [hsum,
    (Real.tendsto_log_atTop.comp tendsto_taoZ_atTop).eventually
      (eventually_gt_atTop (0 : ℝ))] with x hx hlog
  let S : ℝ :=
    (psiNat (taoPrimeTupleRemainderBudget x (P x))
      (taoPrimeTupleRemainderSmoothnessCutoff (P x)) : ℝ)
  let K : ℝ :=
    S * ((B * (8 * iteratedLog x) ^ (50 : ℕ) /
      Real.log (taoZ x) ^ (2 : ℕ)) *
        ∏ j, ((taoDyadicPrimeBand (P x j)).card : ℝ))
  have hK : 0 ≤ K := by
    dsimp only [K, S]
    have hpowFifty : 0 ≤ (8 * iteratedLog x) ^ (50 : ℕ) := by positivity
    apply mul_nonneg (Nat.cast_nonneg _)
    apply mul_nonneg
    · exact div_nonneg (mul_nonneg hB.le hpowFifty) (sq_nonneg _)
    · exact Finset.prod_nonneg fun j hj => Nat.cast_nonneg _
  have hrearrange :
      (∑ r ∈ badIntervalTypicalDyadicExponents x,
          (psiNat (taoPrimeTupleRemainderBudget x (P x))
              (taoPrimeTupleRemainderSmoothnessCutoff (P x)) : ℝ) *
            ((B * (8 * iteratedLog x) ^ (50 : ℕ) /
                (((2 ^ r : ℕ) : ℝ) * Real.log (taoZ x) ^ (2 : ℕ))) *
              ∏ j, ((taoDyadicPrimeBand (P x j)).card : ℝ))) =
        K * ∑ r ∈ badIntervalTypicalDyadicExponents x,
          (1 / (2 : ℝ)) ^ r := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    dsimp only [K, S]
    simp only [Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv, mul_inv,
      ← inv_pow]
    ring
  calc
    ((taoPrimeTupleTypicalDyadicRemainderTriples (P x) x
        (lowerPrime x)
        (taoLargePrimeSourceUpperCutoff x)).card : ℝ) ≤
        K * ∑ r ∈ badIntervalTypicalDyadicExponents x,
          (1 / (2 : ℝ)) ^ r := by simpa only [B, hrearrange] using hx
    _ ≤ K * 2 := mul_le_mul_of_nonneg_left
      (sum_badIntervalTypicalDyadicExponents_inv_two_pow_le_two x) hK
    _ = 2 * (psiNat (taoPrimeTupleRemainderBudget x (P x))
            (taoPrimeTupleRemainderSmoothnessCutoff (P x)) : ℝ) *
          ((B * (8 * iteratedLog x) ^ (50 : ℕ) /
              Real.log (taoZ x) ^ (2 : ℕ)) *
            ∏ j, ((taoDyadicPrimeBand (P x j)).card : ℝ)) := by
      dsimp only [K, S]
      ring

/-- Existential compatibility wrapper for the evaluated dyadic-length sum. -/
theorem exists_eventually_card_taoPrimeTupleTypicalDyadicRemainderTriples_le_two_mul_withLower_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    (hP : ∀ x j, (taoDyadicPrimeBand (P x j)).Nonempty)
    (lowerPrime : ℕ → ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ x : ℕ in atTop,
      ((taoPrimeTupleTypicalDyadicRemainderTriples (P x) x
          (lowerPrime x)
          (taoLargePrimeSourceUpperCutoff x)).card : ℝ) ≤
        2 * (psiNat (taoPrimeTupleRemainderBudget x (P x))
            (taoPrimeTupleRemainderSmoothnessCutoff (P x)) : ℝ) *
          ((B * (8 * iteratedLog x) ^ (50 : ℕ) /
              Real.log (taoZ x) ^ (2 : ℕ)) *
            ∏ j, ((taoDyadicPrimeBand (P x j)).card : ℝ)) := by
  exact ⟨taoPrimeTupleTypicalUniformSourceConstant hC hburgess,
    taoPrimeTupleTypicalUniformSourceConstant_pos hC hburgess,
    eventually_card_taoPrimeTupleTypicalDyadicRemainderTriples_le_two_mul_withLower_uniformConstant_of_explicitBurgess
      hC hburgess hscale hP lowerPrime⟩

/-- Fixed-`z^(9/10)` specialization of the evaluated dyadic-length sum. -/
theorem exists_eventually_card_taoPrimeTupleTypicalDyadicRemainderTriples_le_two_mul_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    (hP : ∀ x j, (taoDyadicPrimeBand (P x j)).Nonempty) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ x : ℕ in atTop,
      ((taoPrimeTupleTypicalDyadicRemainderTriples (P x) x
          (taoZPowerFloor (9 / 10 : ℝ) x)
          (taoLargePrimeSourceUpperCutoff x)).card : ℝ) ≤
        2 * (psiNat (taoPrimeTupleRemainderBudget x (P x))
            (taoPrimeTupleRemainderSmoothnessCutoff (P x)) : ℝ) *
          ((B * (8 * iteratedLog x) ^ (50 : ℕ) /
              Real.log (taoZ x) ^ (2 : ℕ)) *
            ∏ j, ((taoDyadicPrimeBand (P x j)).card : ℝ)) := by
  exact
    exists_eventually_card_taoPrimeTupleTypicalDyadicRemainderTriples_le_two_mul_withLower_of_explicitBurgess
      hC hburgess hscale hP (fun x => taoZPowerFloor (9 / 10 : ℝ) x)

/-! ## Evaluation into the one-term bad set -/

/-- The integer represented by a smooth remainder and prime tuple. -/
def taoPrimeTupleTypicalRemainderValue
    (a : Σ _m' : ℕ, TaoPrimeTuple) : ℕ :=
  taoPrimeTupleStart a.1 a.2

/-- Every fixed-length pair counted above evaluates to a member of
`B¹ ∩ [1,2x]`.  This uses the normalized bad-interval data contained in the
typical event, rather than an enlarged surrogate set. -/
theorem taoPrimeTupleTypicalRemainderValue_mem_badOneTermNumbersUpTo
    {P : Fin 1001 → ℕ} {x H lowerPrime upperPrime : ℕ}
    {a : Σ _m' : ℕ, TaoPrimeTuple}
    (ha : a ∈ taoPrimeTupleTypicalRemainderPairs P x H lowerPrime upperPrime) :
    taoPrimeTupleTypicalRemainderValue a ∈ badOneTermNumbersUpTo (2 * x) := by
  have ha' := mem_taoPrimeTupleTypicalRemainderPairs.mp ha
  have htyp :=
    (mem_taoPrimeTupleTypicalSupport.mp ha'.2).2
  have hnorm := htyp.1.1
  obtain ⟨hHTwo, _hbad, hp, _hHltp, _hpMax, hk, hmSmooth, hkm,
    _hendpoint, _hpow⟩ := hnorm
  have hkBounds := Finset.mem_Ioc.mp hk
  have hright := htyp.1.2.2.1
  have hforward := htyp.2
  rw [badOneTermNumbersUpTo, Finset.mem_filter, Finset.mem_Icc]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · dsimp only [taoPrimeTupleTypicalRemainderValue]
    omega
  · dsimp only [taoPrimeTupleTypicalRemainderValue]
    omega
  · apply mem_badOneTermSet_iff_exists_prime_sq_mul_smooth.mpr
    refine ⟨a.2 0, taoPrimeTupleTailProduct a.2 * a.1, hp, hmSmooth, ?_⟩
    simpa only [taoPrimeTupleTypicalRemainderValue] using hkm

/-- Evaluation of the complete dyadic-length/remainder/prime-tuple family. -/
def taoPrimeTupleTypicalDyadicRemainderValue
    (a : Σ _r : ℕ, Σ _m' : ℕ, TaoPrimeTuple) : ℕ :=
  taoPrimeTupleTypicalRemainderValue a.2

/-- The image of the full fixed-prime-scale counting family is contained in
the literal finite one-term bad set. -/
theorem image_taoPrimeTupleTypicalDyadicRemainderTriples_subset_badOneTermNumbersUpTo
    (P : Fin 1001 → ℕ) (x lowerPrime upperPrime : ℕ) :
    (taoPrimeTupleTypicalDyadicRemainderTriples P x lowerPrime upperPrime).image
        taoPrimeTupleTypicalDyadicRemainderValue ⊆
      badOneTermNumbersUpTo (2 * x) := by
  intro n hn
  rw [Finset.mem_image] at hn
  obtain ⟨a, ha, rfl⟩ := hn
  have ha' := mem_taoPrimeTupleTypicalDyadicRemainderTriples.mp ha
  exact taoPrimeTupleTypicalRemainderValue_mem_badOneTermNumbersUpTo ha'.2

/-- Consequently, the number of distinct represented values is bounded by
the literal one-term count at `2x`. -/
theorem card_image_taoPrimeTupleTypicalDyadicRemainderTriples_le_badOneTermCount
    (P : Fin 1001 → ℕ) (x lowerPrime upperPrime : ℕ) :
    ((taoPrimeTupleTypicalDyadicRemainderTriples P x lowerPrime upperPrime).image
        taoPrimeTupleTypicalDyadicRemainderValue).card ≤
      badOneTermCount (2 * x) := by
  change ((taoPrimeTupleTypicalDyadicRemainderTriples P x lowerPrime
      upperPrime).image taoPrimeTupleTypicalDyadicRemainderValue).card ≤
    (badOneTermNumbersUpTo (2 * x)).card
  exact Finset.card_le_card
    (image_taoPrimeTupleTypicalDyadicRemainderTriples_subset_badOneTermNumbersUpTo
      P x lowerPrime upperPrime)

/-- Exact reduction of the remaining representation issue.  Any uniform
fiber bound for the evaluation map turns the tuple count into that constant
times the literal `B¹` count. -/
theorem card_taoPrimeTupleTypicalDyadicRemainderTriples_le_badOneTermCount_mul_of_fiber_le
    (P : Fin 1001 → ℕ) (x lowerPrime upperPrime M : ℕ)
    (hM : ∀ n ∈
      (taoPrimeTupleTypicalDyadicRemainderTriples P x lowerPrime upperPrime).image
        taoPrimeTupleTypicalDyadicRemainderValue,
      ((taoPrimeTupleTypicalDyadicRemainderTriples P x lowerPrime upperPrime).filter
        fun a => taoPrimeTupleTypicalDyadicRemainderValue a = n).card ≤ M) :
    (taoPrimeTupleTypicalDyadicRemainderTriples P x lowerPrime upperPrime).card ≤
      badOneTermCount (2 * x) * M := by
  calc
    (taoPrimeTupleTypicalDyadicRemainderTriples P x lowerPrime upperPrime).card ≤
        ((taoPrimeTupleTypicalDyadicRemainderTriples P x lowerPrime upperPrime).image
          taoPrimeTupleTypicalDyadicRemainderValue).card * M := by
      exact card_le_card_image_mul_of_fiber_le _ _ _ hM
    _ ≤ badOneTermCount (2 * x) * M :=
      Nat.mul_le_mul_right M
        (card_image_taoPrimeTupleTypicalDyadicRemainderTriples_le_badOneTermCount
          P x lowerPrime upperPrime)

end

end Tao2026
