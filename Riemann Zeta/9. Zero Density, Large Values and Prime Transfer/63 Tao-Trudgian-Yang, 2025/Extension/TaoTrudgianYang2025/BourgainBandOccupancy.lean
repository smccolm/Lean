import TaoTrudgianYang2025.BourgainZetaBands

/-!
# Actual translated occupancy of a zeta band

Occupancy counts integer centres whose translates lie in the specified
measurable set. Both the trivial cardinality bound and the integer-window
overlap bound are retained before any asymptotic normalization.
-/

open MeasureTheory Set
open scoped Interval Classical

noncomputable section

namespace TaoTrudgianYang2025

/-- The actual number of translated integer centres in a measurable set. -/
def bourgainBandOccupancy (D : Finset ℤ) (S : Set ℝ) (u : ℝ) : ℝ :=
  ∑ ℓ ∈ D, S.indicator (fun _ => (1 : ℝ)) ((ℓ : ℝ)+u)

theorem bourgainBandOccupancy_eq_card (D : Finset ℤ) (S : Set ℝ) (u : ℝ) :
    bourgainBandOccupancy D S u =
      ((D.filter fun ℓ : ℤ => (ℓ : ℝ)+u ∈ S).card : ℝ) := by
  classical
  simp only [bourgainBandOccupancy, Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero]
  apply Finset.sum_congr rfl
  intro ℓ hℓ
  by_cases h : (ℓ : ℝ)+u ∈ S <;> simp [h]

theorem bourgainBandOccupancy_bounds (D : Finset ℤ) (S : Set ℝ) (u : ℝ) :
    0 ≤ bourgainBandOccupancy D S u ∧
      bourgainBandOccupancy D S u ≤ (D.card : ℝ) := by
  rw [bourgainBandOccupancy_eq_card]
  exact ⟨Nat.cast_nonneg _, by exact_mod_cast Finset.card_filter_le D (fun ℓ : ℤ => (ℓ : ℝ)+u ∈ S)⟩

/-- Translated measurable indicators are integrable on every finite interval. -/
theorem bourgain_indicator_intervalIntegrable {S : Set ℝ} (hS : MeasurableSet S)
    (c a b : ℝ) :
    IntervalIntegrable (fun u => S.indicator (fun _ => (1 : ℝ)) (c+u)) volume a b := by
  apply (intervalIntegrable_const : IntervalIntegrable (fun _ => (1 : ℝ)) volume a b).mono_fun'
  · exact ((measurable_const.indicator hS).comp
      (measurable_const.add measurable_id)).aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro u
    by_cases h : c+u ∈ S <;> simp [h]

theorem bourgainBandOccupancy_intervalIntegrable (D : Finset ℤ)
    {S : Set ℝ} (hS : MeasurableSet S) (a b : ℝ) :
    IntervalIntegrable (bourgainBandOccupancy D S) volume a b := by
  convert IntervalIntegrable.sum D
    (fun ℓ _ => bourgain_indicator_intervalIntegrable hS ℓ a b) using 1
  ext u
  simp only [bourgainBandOccupancy, Finset.sum_apply]

/-- Integrated occupancy, retaining the actual amplitude band. -/
def bourgainZetaBandMass (D : Finset ℤ) (H T V : ℝ) : ℝ :=
  ∫ u in -H..H, bourgainBandOccupancy D (bourgainZetaBand T V) u

theorem bourgainZetaBandMass_eq_sum (D : Finset ℤ) (H T V : ℝ) :
    bourgainZetaBandMass D H T V =
      ∑ ℓ ∈ D, ∫ u in -H..H,
        (bourgainZetaBand T V).indicator (fun _ => (1 : ℝ)) ((ℓ : ℝ)+u) := by
  exact intervalIntegral.integral_finsetSum (fun (ℓ : ℤ) _ =>
    bourgain_indicator_intervalIntegrable (measurableSet_bourgainZetaBand T V) ℓ (-H) H)

/-- The occupancy integral is nonnegative and at most the full window
length times the number of integer centres. -/
theorem bourgainZetaBandMass_bounds (D : Finset ℤ) {H : ℝ} (hH : 0 ≤ H) (T V : ℝ) :
    0 ≤ bourgainZetaBandMass D H T V ∧
      bourgainZetaBandMass D H T V ≤ 2*H*(D.card : ℝ) := by
  constructor
  · exact intervalIntegral.integral_nonneg (by linarith)
      (fun u _ => (bourgainBandOccupancy_bounds D (bourgainZetaBand T V) u).1)
  · calc
      _ ≤ ∫ _ in -H..H, (D.card : ℝ) :=
        intervalIntegral.integral_mono_on (by linarith)
          (bourgainBandOccupancy_intervalIntegrable D (measurableSet_bourgainZetaBand T V) _ _)
          intervalIntegrable_const
          (fun u _ => (bourgainBandOccupancy_bounds D (bourgainZetaBand T V) u).2)
      _ = _ := by rw [intervalIntegral.integral_const, smul_eq_mul]; ring

/-- Integer-window overlap bounds the actual integrated occupancy by
the measure of the set. No continuity of its indicator is presumed. -/
theorem bourgainBandOccupancy_integral_le_measure (D : Finset ℤ)
    {S : Set ℝ} (hS : MeasurableSet S) (hfin : volume S ≠ ⊤)
    {H : ℝ} (hH : 0 ≤ H) :
    (∫ u in -H..H, bourgainBandOccupancy D S u) ≤
      (2*Nat.ceil H+1 : ℕ) * volume.real S := by
  classical
  let f : ℝ → ℝ := S.indicator (fun _ => 1)
  let window := fun ℓ : ℤ => Ioc ((ℓ : ℝ)-H) ((ℓ : ℝ)+H)
  have hfi : Integrable f := (integrableOn_const hfin).integrable_indicator hS
  have hwi (ℓ : ℤ) : Integrable ((window ℓ).indicator f) :=
    hfi.indicator measurableSet_Ioc
  have hf0 (x : ℝ) : 0 ≤ f x := by
    dsimp only [f]
    by_cases h : x ∈ S <;> simp [h]
  have hpoint (x : ℝ) :
      (∑ ℓ ∈ D, (window ℓ).indicator f x) ≤ (2*Nat.ceil H+1 : ℕ)*f x := by
    have heq : (∑ ℓ ∈ D, (window ℓ).indicator f x) =
        ((D.filter fun ℓ => x ∈ window ℓ).card : ℝ)*f x := by
      calc
        _ = ∑ ℓ ∈ D.filter (fun ℓ => x ∈ window ℓ), f x := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro ℓ hℓ
          by_cases h : x ∈ window ℓ <;> simp [h]
        _ = _ := by simp
    rw [heq]
    exact mul_le_mul_of_nonneg_right
      (by exact_mod_cast bourgain_integer_window_count_le D H x) (hf0 x)
  have heq : (∫ u in -H..H, bourgainBandOccupancy D S u) =
      ∫ x, ∑ ℓ ∈ D, (window ℓ).indicator f x := by
    simp only [bourgainBandOccupancy]
    rw [intervalIntegral.integral_finsetSum (fun (ℓ : ℤ) _ =>
        bourgain_indicator_intervalIntegrable hS ℓ (-H) H),
      MeasureTheory.integral_finsetSum D (fun ℓ _ => hwi ℓ)]
    apply Finset.sum_congr rfl
    intro ℓ hℓ
    rw [MeasureTheory.integral_indicator measurableSet_Ioc]
    change (∫ u in -H..H, f ((ℓ : ℝ)+u)) = ∫ x in Ioc ((ℓ : ℝ)-H) ((ℓ : ℝ)+H), f x
    rw [intervalIntegral.integral_comp_add_left,
      intervalIntegral.integral_of_le (by linarith)]
    rfl
  rw [heq]
  calc
    _ ≤ ∫ x, (2*Nat.ceil H+1 : ℕ)*f x :=
      integral_mono (integrable_finsetSum D (fun ℓ _ => hwi ℓ)) (hfi.const_mul _) hpoint
    _ = _ := by rw [integral_const_mul]; simp only [f, integral_indicator_const (1 : ℝ) hS,
        smul_eq_mul, mul_one]

theorem bourgainZetaBandMass_le_measure (D : Finset ℤ)
    {H : ℝ} (hH : 0 ≤ H) (T V : ℝ) :
    bourgainZetaBandMass D H T V ≤
      (2*Nat.ceil H+1 : ℕ)*volume.real (bourgainZetaBand T V) :=
  bourgainBandOccupancy_integral_le_measure D (measurableSet_bourgainZetaBand T V)
    (bourgainZetaBand_measure_lt_top T V).ne hH

end TaoTrudgianYang2025
