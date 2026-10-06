import Dubon2026.HaarChord
import Mathlib.Analysis.Convex.Continuous

/-! # Convexity and continuity of the actual Jessen function -/

namespace Dubon2026

open Set

theorem convexOn_univ_of_chord (f : ℝ → ℝ)
    (hchord : ∀ l u σ : ℝ, l < u → σ ∈ Icc l u →
      f σ ≤ (1 - (σ - l) / (u - l)) * f l + ((σ - l) / (u - l)) * f u) :
    ConvexOn ℝ Set.univ f := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  change f (a * x + b * y) ≤ a * f x + b * f y
  have haeq : a = 1 - b := by linarith
  have hbeq : b = 1 - a := by linarith
  rcases lt_trichotomy x y with hxy | rfl | hyx
  · have ht : a * x + b * y ∈ Icc x y := by
      rw [haeq]
      constructor <;> nlinarith [mul_nonneg ha (sub_pos.mpr hxy).le,
        mul_nonneg hb (sub_pos.mpr hxy).le]
    have hθ : (a * x + b * y - x) / (y - x) = b := by
      apply (div_eq_iff (sub_pos.mpr hxy).ne').mpr
      rw [haeq]
      ring
    have h := hchord x y (a * x + b * y) hxy ht
    simpa only [hθ, ← haeq] using h
  · simp only [← add_mul, hab, one_mul, le_rfl]
  · have ht : a * x + b * y ∈ Icc y x := by
      rw [hbeq]
      constructor <;> nlinarith [mul_nonneg ha (sub_pos.mpr hyx).le,
        mul_nonneg hb (sub_pos.mpr hyx).le]
    have hθ : (a * x + b * y - y) / (x - y) = a := by
      apply (div_eq_iff (sub_pos.mpr hyx).ne').mpr
      rw [hbeq]
      ring
    have h := hchord y x (a * x + b * y) hyx ht
    simpa only [hθ, ← hbeq, add_comm] using h

theorem convexOn_haarLogPotential {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) : ConvexOn ℝ Set.univ (haarLogPotential a N) :=
  convexOn_univ_of_chord _ (fun _ _ _ hlu hσ => haarLogPotential_le_chord hN ha hlu hσ)

theorem convexOn_jessenFunction {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) : ConvexOn ℝ Set.univ (jessenFunction a N) := by
  have he : jessenFunction a N = haarLogPotential a N := funext (jessenFunction_eq_haar hN ha)
  rw [he]
  exact convexOn_haarLogPotential hN ha

theorem continuous_jessenFunction {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) : Continuous (jessenFunction a N) :=
  continuousOn_univ.mp ((convexOn_jessenFunction hN ha).continuousOn isOpen_univ)

end Dubon2026
