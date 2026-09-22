import TaoTrudgianYang2025.BourgainIntegerSlice

/-!
# Physical geometry of the full integer slice

Casting the complete integer slice to real ordinates preserves its cardinality,
gives one-unit separation, and retains its actual translated zeta band.
-/

open MeasureTheory RiemannZeta.GuthMaynard Set
open scoped Classical

noncomputable section

namespace TaoTrudgianYang2025

def bourgainRealSlice (H T V u : ℝ) : Finset ℝ :=
  (bourgainIntegerSlice H T V u).image (fun ℓ : ℤ => (ℓ : ℝ))

theorem bourgainRealSlice_card (H T V u : ℝ) :
    (bourgainRealSlice H T V u).card = (bourgainIntegerSlice H T V u).card := by
  exact Finset.card_image_of_injective _ Int.cast_injective

/-- Integer casting supplies the exact separation used by the double-sum bound. -/
theorem bourgainRealSlice_separated (H T V u : ℝ) :
    IsSeparated 1 (bourgainRealSlice H T V u) := by
  intro x hx y hy hxy
  obtain ⟨ℓ, _, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨m, _, rfl⟩ := Finset.mem_image.mp hy
  have hne : ℓ ≠ m := by
    intro h
    exact hxy (congrArg (fun z : ℤ => (z : ℝ)) h)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hgap : (ℓ : ℝ)+1 ≤ (m : ℝ) := by exact_mod_cast Int.add_one_le_iff.mpr hlt
    rw [Real.dist_eq, abs_of_neg (by linarith : (ℓ : ℝ)-(m : ℝ) < 0)]
    linarith
  · have hgap : (m : ℝ)+1 ≤ (ℓ : ℝ) := by exact_mod_cast Int.add_one_le_iff.mpr hgt
    rw [Real.dist_eq, abs_of_nonneg (by linarith : 0 ≤ (ℓ : ℝ)-(m : ℝ))]
    linarith

theorem bourgainRealSlice_mem_band {H T V u x : ℝ}
    (hx : x ∈ bourgainRealSlice H T V u) :
    x+u ∈ bourgainZetaBand T V := by
  obtain ⟨ℓ, hℓ, rfl⟩ := Finset.mem_image.mp hx
  exact (Finset.mem_filter.mp hℓ).2

/-- The spatial bound uses the physical band and shift, not a larger ceiling cover. -/
theorem bourgainRealSlice_bounds {H T V u : ℝ} (hu : u ∈ Icc (-H) H) :
    ∀ x ∈ bourgainRealSlice H T V u, -(T+H) ≤ x ∧ x ≤ T+H := by
  intro x hx
  have hband := bourgainZetaBand_subset_Icc T V (bourgainRealSlice_mem_band hx)
  constructor <;> linarith [hu.1, hu.2, hband.1, hband.2]

theorem bourgainRealSlice_nonempty {H T V u : ℝ}
    (h : (bourgainIntegerSlice H T V u).Nonempty) :
    (bourgainRealSlice H T V u).Nonempty := by
  exact h.image _

end TaoTrudgianYang2025

