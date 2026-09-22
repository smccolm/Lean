import TaoTrudgianYang2025.BourgainPositiveBand
import Mathlib.MeasureTheory.Integral.Average

/-!
# Common shifts for actual band occupancy

The first moment method selects one shift for a whole finite weighted
family. This does not yet select common amplitude parameters across the
source's subdivided large-value families.
-/

open MeasureTheory Set
open scoped Interval Classical

noncomputable section

namespace TaoTrudgianYang2025

/-- An actual integrable function attains at least its interval mean at
some shift inside the half-open integration window. -/
theorem bourgain_interval_integral_common_shift {f : ℝ → ℝ} {H : ℝ}
    (hH : 0 < H) (hf : IntervalIntegrable f volume (-H) H) :
    ∃ u ∈ Ioc (-H) H, (∫ v in -H..H, f v) ≤ 2*H*f u := by
  have hvol : volume.real (Ioc (-H) H) = 2*H := by
    rw [measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
    ring
  have hne : volume (Ioc (-H) H) ≠ 0 := by
    rw [Real.volume_Ioc]
    exact (ENNReal.ofReal_pos.mpr (by linarith)).ne'
  obtain ⟨u, hu, hmean⟩ := exists_setAverage_le hne measure_Ioc_lt_top.ne hf.1
  rw [setAverage_eq, hvol, smul_eq_mul] at hmean
  have hm : (∫ v in Ioc (-H) H, f v)/(2*H) ≤ f u := by
    simpa only [div_eq_mul_inv, mul_comm] using hmean
  refine ⟨u, hu, ?_⟩
  rw [intervalIntegral.integral_of_le (by linarith)]
  have h := (div_le_iff₀ (by positivity : 0 < 2*H)).mp hm
  nlinarith

/-- One actual shift serves an entire finite weighted family of integer
sets. Its integrability is derived from measurable band occupancy. -/
theorem bourgainBandOccupancy_weighted_common_shift {ι : Type*}
    (A : Finset ι) (w : ι → ℝ) (D : ι → Finset ℤ)
    {S : Set ℝ} (hS : MeasurableSet S) {H : ℝ} (hH : 0 < H) :
    ∃ u ∈ Ioc (-H) H,
      (∑ i ∈ A, w i*(∫ v in -H..H, bourgainBandOccupancy (D i) S v)) ≤
        2*H*∑ i ∈ A, w i*bourgainBandOccupancy (D i) S u := by
  have hi (i : ι) : IntervalIntegrable
      (fun v => w i*bourgainBandOccupancy (D i) S v) volume (-H) H :=
    (bourgainBandOccupancy_intervalIntegrable (D i) hS _ _).const_mul _
  have hs : IntervalIntegrable
      (fun v => ∑ i ∈ A, w i*bourgainBandOccupancy (D i) S v) volume (-H) H := by
    convert IntervalIntegrable.sum A (fun i _ => hi i) using 1
    ext v
    simp only [Finset.sum_apply]
  obtain ⟨u, hu, hm⟩ := bourgain_interval_integral_common_shift hH hs
  refine ⟨u, hu, ?_⟩
  rw [intervalIntegral.integral_finsetSum (fun i _ => hi i)] at hm
  simpa only [intervalIntegral.integral_const_mul] using hm

/-- A positive band mass produces an actual nonempty shifted integer
slice and the exact averaging loss, not just an abstract scalar witness. -/
theorem bourgainZetaBandMass_common_shift (D : Finset ℤ) {H T V : ℝ}
    (hH : 0 < H) (hmass : 0 < bourgainZetaBandMass D H T V) :
    ∃ u ∈ Ioc (-H) H,
      (D.filter fun ℓ : ℤ => (ℓ : ℝ)+u ∈ bourgainZetaBand T V).Nonempty ∧
      bourgainZetaBandMass D H T V ≤
        2*H*((D.filter fun ℓ : ℤ => (ℓ : ℝ)+u ∈ bourgainZetaBand T V).card : ℝ) := by
  obtain ⟨u, hu, hm⟩ := bourgain_interval_integral_common_shift hH
    (bourgainBandOccupancy_intervalIntegrable D (measurableSet_bourgainZetaBand T V) _ _)
  rw [bourgainBandOccupancy_eq_card] at hm
  refine ⟨u, hu, ?_, hm⟩
  by_contra hn
  rw [Finset.not_nonempty_iff_eq_empty.mp hn, Finset.card_empty, Nat.cast_zero, mul_zero] at hm
  exact (not_le_of_gt hmass) hm

end TaoTrudgianYang2025
