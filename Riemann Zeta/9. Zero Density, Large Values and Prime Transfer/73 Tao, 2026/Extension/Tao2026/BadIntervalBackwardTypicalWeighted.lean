import Tao2026.BadIntervalTypicalWeighted
import Tao2026.BadIntervalBackwardTypicalAntiSieve

/-!
# Backward typical intervals: length-weighted global assembly

The right-endpoint tuple support has the same cardinality majorant as the
forward support.  This module sums that bound over smooth remainders, dyadic
lengths, and the slow 1001-scale grid.
-/

namespace Tao2026

open Filter Topology Asymptotics
open scoped Classical BigOperators

noncomputable section

set_option maxRecDepth 12000
set_option maxHeartbeats 800000

def taoPrimeTupleBackwardTypicalRemainderPairs
    (P : Fin 1001 → ℕ) (x H lowerPrime upperPrime : ℕ) :
    Finset (Σ _m' : ℕ, TaoPrimeTuple) :=
  (taoPrimeTupleSmoothRemainders x P).sigma fun m' =>
    taoPrimeTupleBackwardTypicalSupport P x H lowerPrime upperPrime m'

theorem mem_taoPrimeTupleBackwardTypicalRemainderPairs
    {P : Fin 1001 → ℕ} {x H lowerPrime upperPrime : ℕ}
    {a : Σ _m' : ℕ, TaoPrimeTuple} :
    a ∈ taoPrimeTupleBackwardTypicalRemainderPairs P x H lowerPrime upperPrime ↔
      a.1 ∈ taoPrimeTupleSmoothRemainders x P ∧
        a.2 ∈ taoPrimeTupleBackwardTypicalSupport P x H lowerPrime upperPrime a.1 := by
  simp [taoPrimeTupleBackwardTypicalRemainderPairs]

theorem card_taoPrimeTupleBackwardTypicalRemainderPairs
    (P : Fin 1001 → ℕ) (x H lowerPrime upperPrime : ℕ) :
    (taoPrimeTupleBackwardTypicalRemainderPairs P x H lowerPrime upperPrime).card =
      ∑ m' ∈ taoPrimeTupleSmoothRemainders x P,
        (taoPrimeTupleBackwardTypicalSupport P x H lowerPrime upperPrime m').card := by
  rw [taoPrimeTupleBackwardTypicalRemainderPairs, Finset.card_sigma]

theorem card_taoPrimeTupleBackwardTypicalRemainderPairs_cast_le
    (P : Fin 1001 → ℕ) (x H lowerPrime upperPrime : ℕ) {Q : ℝ}
    (hQ : ∀ m' ∈ taoPrimeTupleSmoothRemainders x P,
      ((taoPrimeTupleBackwardTypicalSupport P x H lowerPrime upperPrime m').card : ℝ) ≤ Q) :
    ((taoPrimeTupleBackwardTypicalRemainderPairs P x H lowerPrime upperPrime).card : ℝ) ≤
      (psiNat (taoPrimeTupleRemainderBudget x P)
          (taoPrimeTupleRemainderSmoothnessCutoff P) : ℝ) * Q := by
  rw [card_taoPrimeTupleBackwardTypicalRemainderPairs, Nat.cast_sum]
  calc
    (∑ m' ∈ taoPrimeTupleSmoothRemainders x P,
        ((taoPrimeTupleBackwardTypicalSupport P x H lowerPrime upperPrime m').card : ℝ)) ≤
        ∑ _m' ∈ taoPrimeTupleSmoothRemainders x P, Q := by
      exact Finset.sum_le_sum fun m' hm' => hQ m' hm'
    _ = ((taoPrimeTupleSmoothRemainders x P).card : ℝ) * Q := by simp
    _ = (psiNat (taoPrimeTupleRemainderBudget x P)
          (taoPrimeTupleRemainderSmoothnessCutoff P) : ℝ) * Q := by
      rw [card_taoPrimeTupleSmoothRemainders]

theorem eventually_forall_card_taoPrimeTupleBackwardTypicalRemainderPairs_le_withLower_uniformConstant_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    (hP : ∀ x j, (taoDyadicPrimeBand (P x j)).Nonempty)
    (lowerPrime : ℕ → ℕ) :
    ∀ᶠ x : ℕ in atTop, ∀ H : ℕ,
      1 ≤ H → H ≤ taoTypicalLengthCutoff x →
      ((taoPrimeTupleBackwardTypicalRemainderPairs (P x) x H
          (lowerPrime x)
          (taoLargePrimeSourceUpperCutoff x)).card : ℝ) ≤
        (psiNat (taoPrimeTupleRemainderBudget x (P x))
            (taoPrimeTupleRemainderSmoothnessCutoff (P x)) : ℝ) *
          ((taoPrimeTupleTypicalUniformSourceConstant hC hburgess *
                (8 * iteratedLog x) ^ (50 : ℕ) /
              ((H : ℝ) * Real.log (taoZ x) ^ (2 : ℕ))) *
            ∏ j, ((taoDyadicPrimeBand (P x j)).card : ℝ)) := by
  have htuple :=
    eventually_forall_card_taoPrimeTupleBackwardTypicalSupport_le_source_withLower_uniformConstant_of_explicitBurgess
      hC hburgess hscale hP lowerPrime
  filter_upwards [htuple] with x hx H hH hHcut
  apply card_taoPrimeTupleBackwardTypicalRemainderPairs_cast_le
  intro m' hm'
  exact hx H m' hH hHcut

def taoPrimeTupleBackwardTypicalDyadicRemainderTriples
    (P : Fin 1001 → ℕ) (x lowerPrime upperPrime : ℕ) :
    Finset (Σ _r : ℕ, Σ _m' : ℕ, TaoPrimeTuple) :=
  (badIntervalTypicalDyadicExponents x).sigma fun r =>
    taoPrimeTupleBackwardTypicalRemainderPairs P x (2 ^ r) lowerPrime upperPrime

theorem mem_taoPrimeTupleBackwardTypicalDyadicRemainderTriples
    {P : Fin 1001 → ℕ} {x lowerPrime upperPrime : ℕ}
    {a : Σ _r : ℕ, Σ _m' : ℕ, TaoPrimeTuple} :
    a ∈ taoPrimeTupleBackwardTypicalDyadicRemainderTriples P x lowerPrime upperPrime ↔
      a.1 ∈ badIntervalTypicalDyadicExponents x ∧
        a.2 ∈ taoPrimeTupleBackwardTypicalRemainderPairs P x (2 ^ a.1)
          lowerPrime upperPrime := by
  simp [taoPrimeTupleBackwardTypicalDyadicRemainderTriples]

def taoPrimeTupleBackwardTypicalDyadicLengthWeight
    (P : Fin 1001 → ℕ) (x lowerPrime upperPrime : ℕ) : ℕ :=
  ∑ a ∈ taoPrimeTupleBackwardTypicalDyadicRemainderTriples P x lowerPrime upperPrime,
    2 ^ a.1

theorem taoPrimeTupleBackwardTypicalDyadicLengthWeight_eq_sum
    (P : Fin 1001 → ℕ) (x lowerPrime upperPrime : ℕ) :
    taoPrimeTupleBackwardTypicalDyadicLengthWeight P x lowerPrime upperPrime =
      ∑ r ∈ badIntervalTypicalDyadicExponents x,
        2 ^ r * (taoPrimeTupleBackwardTypicalRemainderPairs P x (2 ^ r)
          lowerPrime upperPrime).card := by
  rw [taoPrimeTupleBackwardTypicalDyadicLengthWeight,
    taoPrimeTupleBackwardTypicalDyadicRemainderTriples, Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro r hr
  simp [Nat.mul_comm]

theorem eventually_taoPrimeTupleBackwardTypicalDyadicLengthWeight_le
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    (hP : ∀ x j, (taoDyadicPrimeBand (P x j)).Nonempty)
    (lowerPrime : ℕ → ℕ) :
    ∀ᶠ x : ℕ in atTop,
      (taoPrimeTupleBackwardTypicalDyadicLengthWeight (P x) x (lowerPrime x)
          (taoLargePrimeSourceUpperCutoff x) : ℝ) ≤
        ((badIntervalTypicalDyadicExponents x).card : ℝ) *
          (psiNat (taoPrimeTupleRemainderBudget x (P x))
            (taoPrimeTupleRemainderSmoothnessCutoff (P x)) : ℝ) *
          ((taoPrimeTupleTypicalUniformSourceConstant hC hburgess *
              (8 * iteratedLog x) ^ (50 : ℕ) /
                Real.log (taoZ x) ^ (2 : ℕ)) *
            ∏ j, ((taoDyadicPrimeBand (P x j)).card : ℝ)) := by
  have hpair :=
    eventually_forall_card_taoPrimeTupleBackwardTypicalRemainderPairs_le_withLower_uniformConstant_of_explicitBurgess
      hC hburgess hscale hP lowerPrime
  filter_upwards [hpair, eventually_ge_atTop (2 : ℕ)] with x hx hxTwo
  rw [taoPrimeTupleBackwardTypicalDyadicLengthWeight_eq_sum, Nat.cast_sum]
  let K : ℝ :=
    (psiNat (taoPrimeTupleRemainderBudget x (P x))
        (taoPrimeTupleRemainderSmoothnessCutoff (P x)) : ℝ) *
      ((taoPrimeTupleTypicalUniformSourceConstant hC hburgess *
          (8 * iteratedLog x) ^ (50 : ℕ) /
            Real.log (taoZ x) ^ (2 : ℕ)) *
        ∏ j, ((taoDyadicPrimeBand (P x j)).card : ℝ))
  have hcutoff : 0 < taoTypicalLengthCutoff x := by
    have hlog : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast hxTwo)
    have hcutoffReal : (0 : ℝ) < taoTypicalLengthCutoff x :=
      (pow_pos hlog 20).trans_le (taoTypicalLengthCutoff_spec x)
    exact_mod_cast hcutoffReal
  calc
    (∑ r ∈ badIntervalTypicalDyadicExponents x,
        ((2 ^ r * (taoPrimeTupleBackwardTypicalRemainderPairs (P x) x (2 ^ r)
          (lowerPrime x) (taoLargePrimeSourceUpperCutoff x)).card : ℕ) : ℝ)) ≤
        ∑ _r ∈ badIntervalTypicalDyadicExponents x, K := by
      apply Finset.sum_le_sum
      intro r hr
      have hrle : r ≤ Nat.log 2 (taoTypicalLengthCutoff x) := by
        simp only [badIntervalTypicalDyadicExponents, Finset.mem_range] at hr
        omega
      have hpowle : 2 ^ r ≤ taoTypicalLengthCutoff x :=
        (Nat.pow_le_pow_right (by norm_num) hrle).trans
          (Nat.pow_log_le_self 2 hcutoff.ne')
      have hpowpos : 1 ≤ (2 : ℕ) ^ r := by
        have : 0 < (2 : ℕ) ^ r := pow_pos (by norm_num) r
        omega
      have hbound := hx (2 ^ r) hpowpos hpowle
      have hcastPos : (0 : ℝ) ≤ ((2 : ℕ) ^ r : ℕ) := by positivity
      calc
        ((2 ^ r * (taoPrimeTupleBackwardTypicalRemainderPairs (P x) x (2 ^ r)
            (lowerPrime x) (taoLargePrimeSourceUpperCutoff x)).card : ℕ) : ℝ) =
            (((2 : ℕ) ^ r : ℕ) : ℝ) *
              ((taoPrimeTupleBackwardTypicalRemainderPairs (P x) x (2 ^ r)
                (lowerPrime x) (taoLargePrimeSourceUpperCutoff x)).card : ℝ) := by
          push_cast
          rfl
        _ ≤ (((2 : ℕ) ^ r : ℕ) : ℝ) *
            ((psiNat (taoPrimeTupleRemainderBudget x (P x))
                (taoPrimeTupleRemainderSmoothnessCutoff (P x)) : ℝ) *
              ((taoPrimeTupleTypicalUniformSourceConstant hC hburgess *
                    (8 * iteratedLog x) ^ (50 : ℕ) /
                  ((((2 : ℕ) ^ r : ℕ) : ℝ) *
                    Real.log (taoZ x) ^ (2 : ℕ))) *
                ∏ j, ((taoDyadicPrimeBand (P x j)).card : ℝ))) :=
          mul_le_mul_of_nonneg_left hbound hcastPos
        _ = K := by
          dsimp only [K]
          field_simp [show ((((2 : ℕ) ^ r : ℕ) : ℝ)) ≠ 0 by positivity]
    _ = ((badIntervalTypicalDyadicExponents x).card : ℝ) * K := by simp
    _ = ((badIntervalTypicalDyadicExponents x).card : ℝ) *
          (psiNat (taoPrimeTupleRemainderBudget x (P x))
            (taoPrimeTupleRemainderSmoothnessCutoff (P x)) : ℝ) *
          ((taoPrimeTupleTypicalUniformSourceConstant hC hburgess *
              (8 * iteratedLog x) ^ (50 : ℕ) /
                Real.log (taoZ x) ^ (2 : ℕ)) *
            ∏ j, ((taoDyadicPrimeBand (P x j)).card : ℝ)) := by
      dsimp only [K]
      ring

def TaoPrimeTupleBackwardSlowScaleWeightedCountBound
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    (q : ℕ → ℕ) (x : ℕ) (R : Fin 1001 → ℕ) : Prop :=
  (taoPrimeTupleBackwardTypicalDyadicLengthWeight (fun j => 2 ^ R j) x
      (taoPrimeTupleSlowLowerCutoff q x)
      (taoLargePrimeSourceUpperCutoff x) : ℝ) ≤
    ((badIntervalTypicalDyadicExponents x).card : ℝ) *
      (psiNat
        (taoPrimeTupleRemainderBudget x (fun j => 2 ^ R j))
        (taoPrimeTupleRemainderSmoothnessCutoff
          (fun j => 2 ^ R j)) : ℝ) *
      ((taoPrimeTupleTypicalUniformSourceConstant hC hburgess *
          (8 * iteratedLog x) ^ (50 : ℕ) /
            Real.log (taoZ x) ^ (2 : ℕ)) *
        ∏ j, ((taoDyadicPrimeBand (2 ^ R j)).card : ℝ))

theorem eventually_taoPrimeTupleBackwardSlowScaleWeightedCountBound_of_selector
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {q : ℕ → ℕ} (hq : Tendsto q atTop atTop)
    {R : ℕ → Fin 1001 → ℕ}
    (hR : ∀ᶠ x : ℕ in atTop,
      R x ∈ taoPrimeTupleSlowScaleExponentTuples q x) :
    ∀ᶠ x : ℕ in atTop,
      TaoPrimeTupleBackwardSlowScaleWeightedCountBound hC hburgess q x (R x) := by
  let P : ℕ → Fin 1001 → ℕ := fun x =>
    taoPrimeTupleRepairScale (fun j => 2 ^ R x j)
  have hscale : TaoPrimeTupleSourceScaleFamily P := by
    simpa only [P] using
      taoPrimeTupleSourceScaleFamily_repaired_slowScaleExponentTupleSelector
        hq hR
  have hP : ∀ x j, (taoDyadicPrimeBand (P x j)).Nonempty := by
    intro x j
    exact taoPrimeTupleRepairScale_band_nonempty _ _
  have hcount := eventually_taoPrimeTupleBackwardTypicalDyadicLengthWeight_le
    hC hburgess hscale hP (taoPrimeTupleSlowLowerCutoff q)
  filter_upwards [hcount,
    eventually_taoPrimeTupleRepairScale_slowSelector_eq hR] with x hx heq
  simpa only [P, heq, TaoPrimeTupleBackwardSlowScaleWeightedCountBound] using hx

theorem eventually_forall_taoPrimeTupleBackwardSlowOrderedScaleWeightedCountBound_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {q : ℕ → ℕ} (hq : Tendsto q atTop atTop) :
    ∀ᶠ x : ℕ in atTop,
      ∀ R ∈ taoPrimeTupleSlowOrderedScaleExponentTuples q x,
        TaoPrimeTupleBackwardSlowScaleWeightedCountBound hC hburgess q x R := by
  let S : ℕ → (Fin 1001 → ℕ) → Prop := fun x R =>
    R ∈ taoPrimeTupleSlowScaleExponentTuples q x
  let Q : ℕ → (Fin 1001 → ℕ) → Prop := fun x R =>
    TaoPrimeTupleBackwardSlowScaleWeightedCountBound hC hburgess q x R
  have hne : ∀ᶠ x : ℕ in atTop, ∃ R, S x R :=
    Filter.Eventually.of_forall fun x => by
      simpa only [S] using taoPrimeTupleSlowScaleExponentTuples_nonempty q x
  have hselector : ∀ f : ℕ → (Fin 1001 → ℕ),
      (∀ᶠ x : ℕ in atTop, S x (f x)) →
        ∀ᶠ x : ℕ in atTop, Q x (f x) := by
    intro f hf
    have hcount := eventually_taoPrimeTupleBackwardSlowScaleWeightedCountBound_of_selector
      hC hburgess hq (by simpa only [S] using hf)
    simpa only [Q] using hcount
  have hu := eventually_forall_of_forall_selector hne hselector
  filter_upwards [hu] with x hx R hR
  exact hx R
    (mem_taoPrimeTupleSlowScaleExponentTuples.mpr
      (mem_taoPrimeTupleSlowOrderedScaleExponentTuples.mp hR).1)

theorem taoPrimeTupleBackwardSlowScaleWeightedCountBound_le_assemblyFactor_mul_enlarged
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {q : ℕ → ℕ} {x : ℕ} {R : Fin 1001 → ℕ}
    (hcount : TaoPrimeTupleBackwardSlowScaleWeightedCountBound
      hC hburgess q x R)
    (hprod :
      (∏ j, ((taoDyadicPrimeBand
          (taoPrimeTupleDyadicScales R j)).card : ℝ)) ≤
        8 ^ (1001 : ℕ) *
          ∏ j, ((taoDyadicPrimeBand
            (taoPrimeTupleEnlargedScale
              (taoPrimeTupleDyadicScales R) j)).card : ℝ)) :
    (taoPrimeTupleBackwardTypicalDyadicLengthWeight
        (taoPrimeTupleDyadicScales R) x
        (taoPrimeTupleSlowLowerCutoff q x)
        (taoLargePrimeSourceUpperCutoff x) : ℝ) ≤
      taoPrimeTupleTypicalWeightedAssemblyFactor hC hburgess x *
        ((taoPrimeTupleEnlargedRemainderPairs
          (taoPrimeTupleDyadicScales R) x).card : ℝ) := by
  let A : ℝ :=
    ((badIntervalTypicalDyadicExponents x).card : ℝ) *
      (psiNat
        (taoPrimeTupleRemainderBudget x (taoPrimeTupleDyadicScales R))
        (taoPrimeTupleRemainderSmoothnessCutoff
          (taoPrimeTupleDyadicScales R)) : ℝ) *
      (taoPrimeTupleTypicalUniformSourceConstant hC hburgess *
        (8 * iteratedLog x) ^ (50 : ℕ) /
          Real.log (taoZ x) ^ (2 : ℕ))
  have hAnonneg : 0 ≤ A := by
    dsimp only [A]
    have hB := taoPrimeTupleTypicalUniformSourceConstant_pos hC hburgess
    positivity
  calc
    (taoPrimeTupleBackwardTypicalDyadicLengthWeight
        (taoPrimeTupleDyadicScales R) x
        (taoPrimeTupleSlowLowerCutoff q x)
        (taoLargePrimeSourceUpperCutoff x) : ℝ) ≤
      ((badIntervalTypicalDyadicExponents x).card : ℝ) *
        (psiNat
          (taoPrimeTupleRemainderBudget x (taoPrimeTupleDyadicScales R))
          (taoPrimeTupleRemainderSmoothnessCutoff
            (taoPrimeTupleDyadicScales R)) : ℝ) *
        ((taoPrimeTupleTypicalUniformSourceConstant hC hburgess *
            (8 * iteratedLog x) ^ (50 : ℕ) /
              Real.log (taoZ x) ^ (2 : ℕ)) *
          ∏ j, ((taoDyadicPrimeBand
            (taoPrimeTupleDyadicScales R j)).card : ℝ)) := by
      simpa only [TaoPrimeTupleBackwardSlowScaleWeightedCountBound,
        taoPrimeTupleDyadicScales] using hcount
    _ = A * (∏ j, ((taoDyadicPrimeBand
        (taoPrimeTupleDyadicScales R j)).card : ℝ)) := by
      dsimp only [A]
      ring
    _ ≤ A * (8 ^ (1001 : ℕ) *
          ∏ j, ((taoDyadicPrimeBand
            (taoPrimeTupleEnlargedScale
              (taoPrimeTupleDyadicScales R) j)).card : ℝ)) :=
      mul_le_mul_of_nonneg_left hprod hAnonneg
    _ = taoPrimeTupleTypicalWeightedAssemblyFactor hC hburgess x *
        ((taoPrimeTupleEnlargedRemainderPairs
          (taoPrimeTupleDyadicScales R) x).card : ℝ) := by
      rw [card_taoPrimeTupleEnlargedRemainderPairs, Nat.cast_mul,
        Nat.cast_prod]
      unfold taoPrimeTupleTypicalWeightedAssemblyFactor A
      rw [mul_div_assoc]
      ac_rfl

theorem eventually_forall_taoPrimeTupleBackwardSlowOrderedScaleWeight_le_assembly
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {q : ℕ → ℕ} (hq : Tendsto q atTop atTop) :
    ∀ᶠ x : ℕ in atTop,
      ∀ R ∈ taoPrimeTupleSlowOrderedScaleExponentTuples q x,
        (taoPrimeTupleBackwardTypicalDyadicLengthWeight
            (taoPrimeTupleDyadicScales R) x
            (taoPrimeTupleSlowLowerCutoff q x)
            (taoLargePrimeSourceUpperCutoff x) : ℝ) ≤
          taoPrimeTupleTypicalWeightedAssemblyFactor hC hburgess x *
            ((taoPrimeTupleEnlargedRemainderPairs
              (taoPrimeTupleDyadicScales R) x).card : ℝ) := by
  filter_upwards
    [eventually_forall_taoPrimeTupleBackwardSlowOrderedScaleWeightedCountBound_of_explicitBurgess
      hC hburgess hq,
     eventually_forall_taoPrimeTuple_originalBandProduct_le_enlargedBandProduct q]
      with x hcount hprod R hR
  apply taoPrimeTupleBackwardSlowScaleWeightedCountBound_le_assemblyFactor_mul_enlarged
    hC hburgess (hcount R hR)
  exact hprod R
    (mem_taoPrimeTupleSlowScaleExponentTuples.mpr
      (mem_taoPrimeTupleSlowOrderedScaleExponentTuples.mp hR).1)

def taoPrimeTupleGlobalBackwardTypicalDyadicRemainderQuadruples
    (q : ℕ → ℕ) (x : ℕ) :
    Finset (Σ _R : (Fin 1001 → ℕ), Σ _r : ℕ, Σ _m' : ℕ, TaoPrimeTuple) :=
  (taoPrimeTupleSlowOrderedScaleExponentTuples q x).sigma fun R =>
    taoPrimeTupleBackwardTypicalDyadicRemainderTriples
      (taoPrimeTupleDyadicScales R) x
      (taoPrimeTupleSlowLowerCutoff q x)
      (taoLargePrimeSourceUpperCutoff x)

theorem mem_taoPrimeTupleGlobalBackwardTypicalDyadicRemainderQuadruples
    {q : ℕ → ℕ} {x : ℕ}
    {a : Σ _R : (Fin 1001 → ℕ), Σ _r : ℕ, Σ _m' : ℕ, TaoPrimeTuple} :
    a ∈ taoPrimeTupleGlobalBackwardTypicalDyadicRemainderQuadruples q x ↔
      a.1 ∈ taoPrimeTupleSlowOrderedScaleExponentTuples q x ∧
        a.2 ∈ taoPrimeTupleBackwardTypicalDyadicRemainderTriples
          (taoPrimeTupleDyadicScales a.1) x
          (taoPrimeTupleSlowLowerCutoff q x)
          (taoLargePrimeSourceUpperCutoff x) := by
  simp [taoPrimeTupleGlobalBackwardTypicalDyadicRemainderQuadruples]

def taoPrimeTupleGlobalBackwardTypicalDyadicLengthWeight
    (q : ℕ → ℕ) (x : ℕ) : ℕ :=
  ∑ a ∈ taoPrimeTupleGlobalBackwardTypicalDyadicRemainderQuadruples q x,
    2 ^ a.2.1

theorem taoPrimeTupleGlobalBackwardTypicalDyadicLengthWeight_eq_sum
    (q : ℕ → ℕ) (x : ℕ) :
    taoPrimeTupleGlobalBackwardTypicalDyadicLengthWeight q x =
      ∑ R ∈ taoPrimeTupleSlowOrderedScaleExponentTuples q x,
        taoPrimeTupleBackwardTypicalDyadicLengthWeight
          (taoPrimeTupleDyadicScales R) x
          (taoPrimeTupleSlowLowerCutoff q x)
          (taoLargePrimeSourceUpperCutoff x) := by
  rw [taoPrimeTupleGlobalBackwardTypicalDyadicLengthWeight,
    taoPrimeTupleGlobalBackwardTypicalDyadicRemainderQuadruples,
    Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro R hR
  rfl

theorem eventually_taoPrimeTupleGlobalBackwardTypicalLengthWeight_le_assemblyFactor_mul_enlarged
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {q : ℕ → ℕ} (hq : Tendsto q atTop atTop) :
    ∀ᶠ x : ℕ in atTop,
      (taoPrimeTupleGlobalBackwardTypicalDyadicLengthWeight q x : ℝ) ≤
        taoPrimeTupleTypicalWeightedAssemblyFactor hC hburgess x *
          ((taoPrimeTupleGlobalEnlargedRemainderPairs q x).card : ℝ) := by
  filter_upwards
    [eventually_forall_taoPrimeTupleBackwardSlowOrderedScaleWeight_le_assembly
      hC hburgess hq] with x hx
  rw [taoPrimeTupleGlobalBackwardTypicalDyadicLengthWeight_eq_sum, Nat.cast_sum,
    card_taoPrimeTupleGlobalEnlargedRemainderPairs, Nat.cast_sum]
  calc
    (∑ R ∈ taoPrimeTupleSlowOrderedScaleExponentTuples q x,
        (taoPrimeTupleBackwardTypicalDyadicLengthWeight
          (taoPrimeTupleDyadicScales R) x
          (taoPrimeTupleSlowLowerCutoff q x)
          (taoLargePrimeSourceUpperCutoff x) : ℝ)) ≤
      ∑ R ∈ taoPrimeTupleSlowOrderedScaleExponentTuples q x,
        taoPrimeTupleTypicalWeightedAssemblyFactor hC hburgess x *
          ((taoPrimeTupleEnlargedRemainderPairs
            (taoPrimeTupleDyadicScales R) x).card : ℝ) := by
      exact Finset.sum_le_sum fun R hR => hx R hR
    _ = taoPrimeTupleTypicalWeightedAssemblyFactor hC hburgess x *
        ∑ R ∈ taoPrimeTupleSlowOrderedScaleExponentTuples q x,
          ((taoPrimeTupleEnlargedRemainderPairs
            (taoPrimeTupleDyadicScales R) x).card : ℝ) := by
      rw [Finset.mul_sum]

theorem eventually_taoPrimeTupleGlobalBackwardTypicalLengthWeight_le_assemblyFactor_mul_badOneTermCount
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {q : ℕ → ℕ} (hq : Tendsto q atTop atTop) :
    ∀ᶠ x : ℕ in atTop,
      (taoPrimeTupleGlobalBackwardTypicalDyadicLengthWeight q x : ℝ) ≤
        taoPrimeTupleTypicalWeightedAssemblyFactor hC hburgess x *
          ((badOneTermCount
              (2 * taoPrimeTupleEnlargementFactor * x) *
            (1000 ^ 1000) : ℕ) : ℝ) := by
  filter_upwards
    [eventually_taoPrimeTupleGlobalBackwardTypicalLengthWeight_le_assemblyFactor_mul_enlarged
      hC hburgess hq,
     (tendsto_taoPrimeTupleSlowLowerCutoff_atTop q).eventually
      (eventually_ge_atTop 2)] with x hweight hlower
  calc
    (taoPrimeTupleGlobalBackwardTypicalDyadicLengthWeight q x : ℝ) ≤
        taoPrimeTupleTypicalWeightedAssemblyFactor hC hburgess x *
          ((taoPrimeTupleGlobalEnlargedRemainderPairs q x).card : ℝ) :=
      hweight
    _ ≤ taoPrimeTupleTypicalWeightedAssemblyFactor hC hburgess x *
          ((badOneTermCount
              (2 * taoPrimeTupleEnlargementFactor * x) *
            (1000 ^ 1000) : ℕ) : ℝ) := by
      apply mul_le_mul_of_nonneg_left _
        (taoPrimeTupleTypicalWeightedAssemblyFactor_nonneg hC hburgess x)
      exact_mod_cast
        card_taoPrimeTupleGlobalEnlargedRemainderPairs_le_badOneTermCount_mul
          hlower

theorem taoPrimeTupleGlobalBackwardTypicalLengthWeight_isLittleO_dilatedBadOneTermCount
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    {q : ℕ → ℕ} (hq : Tendsto q atTop atTop) :
    (fun x : ℕ => (taoPrimeTupleGlobalBackwardTypicalDyadicLengthWeight q x : ℝ)) =o[atTop]
      (fun x : ℕ =>
        (badOneTermCount
          (2 * taoPrimeTupleEnlargementFactor * x) : ℝ)) := by
  apply IsLittleO.of_bound
  intro ε hε
  let M : ℝ := (1000 : ℝ) ^ (1000 : ℕ)
  have hMpos : 0 < M := pow_pos (by norm_num) 1000
  have hsmall := (tendsto_taoPrimeTupleTypicalWeightedAssemblyFactor_zero
    hC hburgess).eventually (Iio_mem_nhds (div_pos hε hMpos))
  filter_upwards
    [eventually_taoPrimeTupleGlobalBackwardTypicalLengthWeight_le_assemblyFactor_mul_badOneTermCount
      hC hburgess hq, hsmall] with x hbound hfactor
  have hfactorM :
      taoPrimeTupleTypicalWeightedAssemblyFactor hC hburgess x * M ≤ ε :=
    (le_div_iff₀ hMpos).mp hfactor.le
  simp only [Real.norm_eq_abs, abs_of_nonneg (by positivity :
    (0 : ℝ) ≤ taoPrimeTupleGlobalBackwardTypicalDyadicLengthWeight q x),
    abs_of_nonneg (by positivity :
      (0 : ℝ) ≤ badOneTermCount
        (2 * taoPrimeTupleEnlargementFactor * x))]
  calc
    (taoPrimeTupleGlobalBackwardTypicalDyadicLengthWeight q x : ℝ) ≤
        taoPrimeTupleTypicalWeightedAssemblyFactor hC hburgess x *
          ((badOneTermCount
              (2 * taoPrimeTupleEnlargementFactor * x) *
            (1000 ^ 1000) : ℕ) : ℝ) := hbound
    _ = (taoPrimeTupleTypicalWeightedAssemblyFactor hC hburgess x * M) *
          (badOneTermCount
            (2 * taoPrimeTupleEnlargementFactor * x) : ℝ) := by
      rw [Nat.cast_mul, Nat.cast_pow]
      change taoPrimeTupleTypicalWeightedAssemblyFactor hC hburgess x *
        ((badOneTermCount
          (2 * taoPrimeTupleEnlargementFactor * x) : ℝ) * M) = _
      ac_rfl
    _ ≤ ε *
          (badOneTermCount
            (2 * taoPrimeTupleEnlargementFactor * x) : ℝ) :=
      mul_le_mul_of_nonneg_right hfactorM (by positivity)

end

end Tao2026
