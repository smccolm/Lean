import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Independence.Basic
import Tao2026.BadIntervalSlowCutoff

/-!
# Finite independent-prime model for Proposition 6.6

This module gives the phrase “draw `p₀, …, p₁₀₀₀` uniformly and
independently from their dyadic prime intervals” a literal probability-space
meaning.  The sample space is the finite product `Fin 1001 → ℕ`; each
coordinate law is the uniform PMF on its prescribed prime band, and the joint
law is Mathlib's finite product measure.
-/

namespace Tao2026

open MeasureTheory ProbabilityTheory
open scoped Classical

noncomputable section

/-- The primes in the source half-open dyadic interval `[P, 2P)`. -/
def taoDyadicPrimeBand (P : ℕ) : Finset ℕ :=
  (Finset.Ico P (2 * P)).filter Nat.Prime

theorem mem_taoDyadicPrimeBand {P p : ℕ} :
    p ∈ taoDyadicPrimeBand P ↔ Nat.Prime p ∧ P ≤ p ∧ p < 2 * P := by
  simp only [taoDyadicPrimeBand, Finset.mem_filter, Finset.mem_Ico]
  tauto

/-- The exact 1001-coordinate tuple occurring in Proposition 6.6. -/
abbrev TaoPrimeTuple := Fin 1001 → ℕ

/-- Uniform law on the `j`th dyadic prime band. -/
noncomputable def taoPrimeCoordinateMeasure
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (j : Fin 1001) : Measure ℕ :=
  (PMF.uniformOfFinset (taoDyadicPrimeBand (P j)) (hP j)).toMeasure

instance taoPrimeCoordinateMeasure_isProbability
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (j : Fin 1001) :
    IsProbabilityMeasure (taoPrimeCoordinateMeasure P hP j) := by
  unfold taoPrimeCoordinateMeasure
  infer_instance

/-- Joint law of the independently sampled prime tuple. -/
noncomputable def taoPrimeTupleMeasure
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty) :
    Measure TaoPrimeTuple :=
  Measure.pi (taoPrimeCoordinateMeasure P hP)

instance taoPrimeTupleMeasure_isProbability
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty) :
    IsProbabilityMeasure (taoPrimeTupleMeasure P hP) := by
  unfold taoPrimeTupleMeasure
  infer_instance

/-- Each coordinate of the joint sample has exactly its declared uniform
prime-band law. -/
theorem map_eval_taoPrimeTupleMeasure
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (j : Fin 1001) :
    (taoPrimeTupleMeasure P hP).map (fun ω => ω j) =
      taoPrimeCoordinateMeasure P hP j := by
  unfold taoPrimeTupleMeasure
  exact (measurePreserving_eval (taoPrimeCoordinateMeasure P hP) j).map_eq

/-- Exact uniform mass formula for one coordinate. -/
theorem taoPrimeCoordinateMeasure_apply
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (j : Fin 1001) (S : Set ℕ) :
    taoPrimeCoordinateMeasure P hP j S =
      (((taoDyadicPrimeBand (P j)).filter (fun p => p ∈ S)).card : ENNReal) /
        (taoDyadicPrimeBand (P j)).card := by
  unfold taoPrimeCoordinateMeasure
  simp

/-- Exact uniform mass formula for a cylinder event in the joint space. -/
theorem taoPrimeTupleMeasure_eval_mem
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (j : Fin 1001) (S : Set ℕ) (hS : MeasurableSet S) :
    taoPrimeTupleMeasure P hP {ω | ω j ∈ S} =
      (((taoDyadicPrimeBand (P j)).filter (fun p => p ∈ S)).card : ENNReal) /
        (taoDyadicPrimeBand (P j)).card := by
  calc
    taoPrimeTupleMeasure P hP {ω | ω j ∈ S} =
        (taoPrimeTupleMeasure P hP).map (fun ω => ω j) S := by
      symm
      exact Measure.map_apply (measurable_pi_apply j) hS
    _ = taoPrimeCoordinateMeasure P hP j S := by
      rw [map_eval_taoPrimeTupleMeasure]
    _ = _ := taoPrimeCoordinateMeasure_apply P hP j S

/-- Every sampled coordinate belongs to its prescribed dyadic prime band
almost surely. -/
theorem taoPrimeTupleMeasure_eval_mem_band
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (j : Fin 1001) :
    taoPrimeTupleMeasure P hP
        {ω | ω j ∈ (taoDyadicPrimeBand (P j) : Set ℕ)} = 1 := by
  rw [taoPrimeTupleMeasure_eval_mem P hP j
    (taoDyadicPrimeBand (P j) : Set ℕ)
    ((Set.to_countable _).measurableSet)]
  have hcardNat : (taoDyadicPrimeBand (P j)).card ≠ 0 :=
    Finset.card_ne_zero.mpr (hP j)
  have hcard : ((taoDyadicPrimeBand (P j)).card : ENNReal) ≠ 0 := by
    exact_mod_cast hcardNat
  convert ENNReal.div_self hcard (by simp) using 1
  all_goals simp

/-- The 1001 coordinate projections are independent under the joint law. -/
theorem iIndepFun_taoPrimeTuple
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty) :
    iIndepFun (fun j (ω : TaoPrimeTuple) => ω j)
      (taoPrimeTupleMeasure P hP) := by
  unfold taoPrimeTupleMeasure
  exact ProbabilityTheory.iIndepFun_pi
    (μ := taoPrimeCoordinateMeasure P hP)
    (X := fun _ p => p) (fun _ => measurable_id.aemeasurable)

/-- Product of the coordinates `p₁⋯p₁₀₀₀`, excluding `p₀`. -/
def taoPrimeTupleTailProduct (ω : TaoPrimeTuple) : ℕ :=
  ∏ j ∈ (Finset.univ.erase (0 : Fin 1001)), ω j

/-- The source product `p₀²p₁⋯p₁₀₀₀m'`. -/
def taoPrimeTupleStart (m' : ℕ) (ω : TaoPrimeTuple) : ℕ :=
  (ω 0) ^ 2 * taoPrimeTupleTailProduct ω * m'

/-- Divisibility indicator used in the anti-sieve moment expansions. -/
def taoPrimeDivisibilityIndicator
    (m' l p : ℕ) (ω : TaoPrimeTuple) : ℝ :=
  if p ∣ taoPrimeTupleStart m' ω + l then 1 else 0

theorem taoPrimeDivisibilityIndicator_nonneg
    (m' l p : ℕ) (ω : TaoPrimeTuple) :
    0 ≤ taoPrimeDivisibilityIndicator m' l p ω := by
  unfold taoPrimeDivisibilityIndicator
  split_ifs <;> norm_num

theorem taoPrimeDivisibilityIndicator_le_one
    (m' l p : ℕ) (ω : TaoPrimeTuple) :
    taoPrimeDivisibilityIndicator m' l p ω ≤ 1 := by
  unfold taoPrimeDivisibilityIndicator
  split_ifs <;> norm_num

/-- Exact event that the sampled source product begins a forward typical
normalized interval for the supplied finite cutoffs. -/
def TaoPrimeTupleTypicalEvent
    (x H lowerPrime upperPrime m' : ℕ) (ω : TaoPrimeTuple) : Prop :=
  IsForwardTypicalScaleNormalizedBadInterval x
    (taoTypicalLengthCutoff x) (taoTypicalSquareThreshold x)
    lowerPrime upperPrime
    (taoPrimeTupleStart m' ω - 1) H (ω 0)
    (taoPrimeTupleStart m' ω) (taoPrimeTupleTailProduct ω * m')

/-- Literal probability of the Proposition 6.6 typical-tuple event. -/
noncomputable def taoPrimeTupleTypicalProbability
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (x H lowerPrime upperPrime m' : ℕ) : ENNReal :=
  taoPrimeTupleMeasure P hP
    {ω | TaoPrimeTupleTypicalEvent x H lowerPrime upperPrime m' ω}

end

end Tao2026
