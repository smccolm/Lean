import Tao2026.BadIntervalLargePrimeCrude

/-!
# Exact finite uniform law of the prime tuple

The Proposition 6.6 product measure is supported on the literal Cartesian
product of its 1001 dyadic prime bands.  This module proves that support has
measure one, computes every supported singleton mass, and converts the
probability of an arbitrary event into its exact supported-tuple cardinality
times the common atom mass.  This is the finite bridge needed to implement the
source's “freeze all other random variables” arguments without conditional
probability machinery.
-/

namespace Tao2026

open MeasureTheory
open scoped Classical

noncomputable section

set_option maxRecDepth 4000

/-- Literal finite support of the independent prime tuple. -/
def taoPrimeTupleSupport (P : Fin 1001 → ℕ) : Finset TaoPrimeTuple :=
  Fintype.piFinset fun j => taoDyadicPrimeBand (P j)

theorem mem_taoPrimeTupleSupport {P : Fin 1001 → ℕ} {ω : TaoPrimeTuple} :
    ω ∈ taoPrimeTupleSupport P ↔ ∀ j, ω j ∈ taoDyadicPrimeBand (P j) := by
  simp [taoPrimeTupleSupport]

/-- The finite Cartesian support carries the whole product measure. -/
theorem taoPrimeTupleSupport_measure_one
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty) :
    taoPrimeTupleMeasure P hP (taoPrimeTupleSupport P : Set TaoPrimeTuple) = 1 := by
  rw [show (taoPrimeTupleSupport P : Set TaoPrimeTuple) =
      Set.pi Set.univ (fun j => (taoDyadicPrimeBand (P j) : Set ℕ)) by
    ext ω
    simp [taoPrimeTupleSupport]]
  unfold taoPrimeTupleMeasure
  rw [Measure.pi_pi]
  apply Finset.prod_eq_one
  intro j hj
  rw [taoPrimeCoordinateMeasure_apply]
  have hcard : ((taoDyadicPrimeBand (P j)).card : ENNReal) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr (hP j)
  convert ENNReal.div_self hcard (by simp) using 1
  all_goals simp

/-- Every supported tuple has the product of the reciprocal coordinate
cardinalities as its exact atom mass. -/
theorem taoPrimeTupleMeasure_singleton
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    {ω : TaoPrimeTuple} (hω : ω ∈ taoPrimeTupleSupport P) :
    taoPrimeTupleMeasure P hP {ω} =
      (∏ j, ((taoDyadicPrimeBand (P j)).card : ENNReal))⁻¹ := by
  unfold taoPrimeTupleMeasure
  rw [Measure.pi_singleton]
  have hcoord : ∀ j, (taoPrimeCoordinateMeasure P hP j) {ω j} =
      (((taoDyadicPrimeBand (P j)).card : ENNReal))⁻¹ := by
    intro j
    have hmem := (mem_taoPrimeTupleSupport.mp hω) j
    rw [taoPrimeCoordinateMeasure_apply]
    simp only [Set.mem_singleton_iff]
    rw [show (taoDyadicPrimeBand (P j)).filter (fun p => p = ω j) = {ω j} by
      ext p
      rw [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · exact fun hp => hp.2
      · intro hp
        subst p
        exact ⟨hmem, rfl⟩]
    simp
  simp_rw [hcoord]
  simpa using (ENNReal.prod_inv_distrib
    (s := Finset.univ)
    (f := fun j => ((taoDyadicPrimeBand (P j)).card : ENNReal))
    (by
      intro i hi j hj hij
      right
      simp)).symm

/-- Exact finite counting formula for every event under the tuple law. -/
theorem taoPrimeTupleMeasure_apply_eq_card_mul_atom
    (P : Fin 1001 → ℕ) (hP : ∀ j, (taoDyadicPrimeBand (P j)).Nonempty)
    (E : Set TaoPrimeTuple) :
    taoPrimeTupleMeasure P hP E =
      ((taoPrimeTupleSupport P).filter (fun ω => ω ∈ E)).card *
        (∏ j, ((taoDyadicPrimeBand (P j)).card : ENNReal))⁻¹ := by
  let μ := taoPrimeTupleMeasure P hP
  let S := taoPrimeTupleSupport P
  have hS : μ (S : Set TaoPrimeTuple) = 1 :=
    taoPrimeTupleSupport_measure_one P hP
  have hSmeas : MeasurableSet (S : Set TaoPrimeTuple) :=
    (Set.to_countable _).measurableSet
  have hSfin : μ (S : Set TaoPrimeTuple) ≠ ⊤ := by rw [hS]; simp
  have hScompl : μ (S : Set TaoPrimeTuple)ᶜ = 0 := by
    rw [measure_compl hSmeas hSfin, measure_univ, hS]
    simp
  calc
    μ E = μ (E \ (S : Set TaoPrimeTuple)ᶜ) :=
      (measure_diff_null hScompl).symm
    _ = μ ((S.filter fun ω => ω ∈ E : Finset TaoPrimeTuple) : Set TaoPrimeTuple) := by
      congr 1
      ext ω
      simp [and_comm]
    _ = ∑ ω ∈ S.filter (fun ω => ω ∈ E), μ {ω} := by
      rw [sum_measure_singleton]
    _ = ∑ _ω ∈ S.filter (fun ω => ω ∈ E),
        (∏ j, ((taoDyadicPrimeBand (P j)).card : ENNReal))⁻¹ := by
      apply Finset.sum_congr rfl
      intro ω hω
      exact taoPrimeTupleMeasure_singleton P hP (Finset.mem_filter.mp hω).1
    _ = ((S.filter fun ω => ω ∈ E).card : ENNReal) *
        (∏ j, ((taoDyadicPrimeBand (P j)).card : ENNReal))⁻¹ := by
      simp

end

end Tao2026
