import TaoTrudgianYang2025.BourgainBandShift

/-!
# The complete integer slice of an actual zeta-amplitude band

A fixed finite integer cover works for every shift in the integration window.
Membership is equivalent to membership in the translated band, not just a
truncation to one component's difference set. Both first and square-root
moments retain the exact integer-window overlap loss.
-/

open MeasureTheory Set
open scoped Interval Classical

noncomputable section

namespace TaoTrudgianYang2025

def bourgainIntegerCover (H T : ℝ) : Finset ℤ :=
  Finset.Icc (-(Nat.ceil (T+H) : ℤ)) (Nat.ceil (T+H) : ℤ)

def bourgainIntegerSlice (H T V u : ℝ) : Finset ℤ :=
  (bourgainIntegerCover H T).filter
    (fun ℓ : ℤ => (ℓ : ℝ)+u ∈ bourgainZetaBand T V)

/-- The cover contains every integer whose translate lies in the band. -/
theorem bourgain_mem_integerCover {H T V u : ℝ} (hu : u ∈ Icc (-H) H)
    {ℓ : ℤ} (hℓ : (ℓ : ℝ)+u ∈ bourgainZetaBand T V) :
    ℓ ∈ bourgainIntegerCover H T := by
  obtain ⟨hlo, hhi⟩ := bourgainZetaBand_subset_Icc T V hℓ
  have hc : T+H ≤ (Nat.ceil (T+H) : ℝ) := Nat.le_ceil _
  apply Finset.mem_Icc.mpr
  constructor
  · have hr : -(Nat.ceil (T+H) : ℝ) ≤ (ℓ : ℝ) := by linarith [hu.2]
    exact_mod_cast hr
  · have hr : (ℓ : ℝ) ≤ (Nat.ceil (T+H) : ℝ) := by linarith [hu.1]
    exact_mod_cast hr

theorem mem_bourgainIntegerSlice {H T V u : ℝ} (hu : u ∈ Icc (-H) H) (ℓ : ℤ) :
    ℓ ∈ bourgainIntegerSlice H T V u ↔ (ℓ : ℝ)+u ∈ bourgainZetaBand T V := by
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · exact fun h => Finset.mem_filter.mpr ⟨bourgain_mem_integerCover hu h, h⟩

theorem bourgainIntegerSlice_card (H T V u : ℝ) :
    ((bourgainIntegerSlice H T V u).card : ℝ) =
      bourgainBandOccupancy (bourgainIntegerCover H T) (bourgainZetaBand T V) u := by
  exact (bourgainBandOccupancy_eq_card _ _ _).symm

/-- Component occupancy is the cardinality of intersection with the full slice. -/
theorem bourgainIntegerSlice_inter_card (D : Finset ℤ) {H T V u : ℝ}
    (hu : u ∈ Icc (-H) H) :
    ((D ∩ bourgainIntegerSlice H T V u).card : ℝ) =
      bourgainBandOccupancy D (bourgainZetaBand T V) u := by
  rw [bourgainBandOccupancy_eq_card]
  apply congrArg (fun F : Finset ℤ => (F.card : ℝ))
  ext ℓ
  simp only [Finset.mem_inter, mem_bourgainIntegerSlice hu, Finset.mem_filter]

theorem bourgainBandOccupancy_measurable (D : Finset ℤ)
    {S : Set ℝ} (hS : MeasurableSet S) :
    Measurable (bourgainBandOccupancy D S) := by
  apply Finset.measurable_sum
  intro ℓ hℓ
  exact (measurable_const.indicator hS).comp (measurable_const.add measurable_id)

theorem bourgainBandOccupancy_sqrt_intervalIntegrable (D : Finset ℤ)
    {S : Set ℝ} (hS : MeasurableSet S) (a b : ℝ) :
    IntervalIntegrable (fun u => Real.sqrt (bourgainBandOccupancy D S u)) volume a b := by
  apply (intervalIntegrable_const :
    IntervalIntegrable (fun _ => Real.sqrt (D.card : ℝ)) volume a b).mono_fun'
  · exact (bourgainBandOccupancy_measurable D hS).sqrt.aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro u
    change ‖Real.sqrt (bourgainBandOccupancy D S u)‖ ≤ Real.sqrt (D.card : ℝ)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt (bourgainBandOccupancy_bounds D S u).2

/-- Cauchy--Schwarz for the actual finite occupancy, proved by integrating
a nonnegative square. No continuity of the integer-slice size is assumed. -/
theorem bourgainBandOccupancy_sqrt_integral_sq_le (D : Finset ℤ)
    {S : Set ℝ} (hS : MeasurableSet S) {H : ℝ} (hH : 0 ≤ H) :
    (∫ u in -H..H, Real.sqrt (bourgainBandOccupancy D S u))^2 ≤
      2*H*(∫ u in -H..H, bourgainBandOccupancy D S u) := by
  rcases hH.eq_or_lt with heq | hHp
  · subst H
    simp
  let M := ∫ u in -H..H, Real.sqrt (bourgainBandOccupancy D S u)
  let Q := ∫ u in -H..H, bourgainBandOccupancy D S u
  let c := M/(2*H)
  have hc : 2*H*c = M := by
    dsimp only [c]
    exact mul_div_cancel₀ M (by positivity : (2*H : ℝ) ≠ 0)
  have hi := bourgainBandOccupancy_intervalIntegrable D hS (-H) H
  have hs := bourgainBandOccupancy_sqrt_intervalIntegrable D hS (-H) H
  have hn : 0 ≤ ∫ u in -H..H,
      bourgainBandOccupancy D S u-2*c*Real.sqrt (bourgainBandOccupancy D S u)+c^2 := by
    apply intervalIntegral.integral_nonneg (by linarith)
    intro u hu
    have hsq := Real.sq_sqrt (bourgainBandOccupancy_bounds D S u).1
    nlinarith [sq_nonneg (Real.sqrt (bourgainBandOccupancy D S u)-c)]
  rw [intervalIntegral.integral_add (hi.sub (hs.const_mul (2*c))) intervalIntegrable_const,
    intervalIntegral.integral_sub hi (hs.const_mul (2*c)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul] at hn
  change 0 ≤ Q-2*c*M+(H- -H)*c^2 at hn
  have hm : M^2 ≤ 2*H*Q := by
    have hp := mul_nonneg (show 0 ≤ 2*H by positivity) hn
    nlinarith [sq_nonneg (2*H*c-M)]
  exact hm

theorem bourgainIntegerSlice_integral_card_le {H : ℝ} (hH : 0 ≤ H) (T V : ℝ) :
    (∫ u in -H..H, ((bourgainIntegerSlice H T V u).card : ℝ)) ≤
      (2*Nat.ceil H+1 : ℕ)*volume.real (bourgainZetaBand T V) := by
  simp only [bourgainIntegerSlice_card]
  exact bourgainZetaBandMass_le_measure _ hH T V

theorem bourgainIntegerSlice_integral_sqrt_card_le {H : ℝ} (hH : 0 ≤ H) (T V : ℝ) :
    (∫ u in -H..H, Real.sqrt ((bourgainIntegerSlice H T V u).card : ℝ)) ≤
      Real.sqrt (2*H*(2*Nat.ceil H+1 : ℕ)*volume.real (bourgainZetaBand T V)) := by
  simp only [bourgainIntegerSlice_card]
  have hsq := bourgainBandOccupancy_sqrt_integral_sq_le
    (bourgainIntegerCover H T) (measurableSet_bourgainZetaBand T V) hH
  have hb := bourgainZetaBandMass_le_measure (bourgainIntegerCover H T) hH T V
  apply Real.le_sqrt_of_sq_le
  calc
    _ ≤ 2*H*bourgainZetaBandMass (bourgainIntegerCover H T) H T V := hsq
    _ ≤ 2*H*((2*Nat.ceil H+1 : ℕ)*volume.real (bourgainZetaBand T V)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

end TaoTrudgianYang2025
