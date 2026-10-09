import Dubon2026.HeckeRadialNormalization

/-! # Uniqueness from the exact original spherical radial recurrence -/

namespace Dubon2026

/-- The original one-step boundary equation and two-step radial recurrence force all coefficients to vanish when the original coefficient does. -/
theorem radial_recurrence_zero (p : ℕ) [NeZero p] (μ : ℂ) (φ : ℕ → ℂ)
    (hzero : φ 0 = 0) (hbase : μ * φ 0 = ((p : ℂ) + 1) * φ 1)
    (hrec : ∀ n, μ * φ (n + 1) = φ n + (p : ℂ) * φ (n + 2)) :
    ∀ n, φ n = 0 := by
  have hp : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)
  have hp1 : (p : ℂ) + 1 ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero p
  have hfirst : φ 1 = 0 := by
    rw [hzero, mul_zero] at hbase
    exact (mul_eq_zero.mp hbase.symm).resolve_left hp1
  refine Nat.twoStepInduction hzero hfirst ?_
  intro n hn hn1
  have he := hrec n
  rw [hn, hn1, mul_zero, zero_add] at he
  exact (mul_eq_zero.mp he.symm).resolve_left hp

/-- Two sequences satisfying the same genuine radial recurrence agree everywhere if their original coefficients agree. -/
theorem radial_recurrence_unique (p : ℕ) [NeZero p] (μ : ℂ) (φ ψ : ℕ → ℂ)
    (hzero : φ 0 = ψ 0)
    (hφbase : μ * φ 0 = ((p : ℂ) + 1) * φ 1)
    (hψbase : μ * ψ 0 = ((p : ℂ) + 1) * ψ 1)
    (hφrec : ∀ n, μ * φ (n + 1) = φ n + (p : ℂ) * φ (n + 2))
    (hψrec : ∀ n, μ * ψ (n + 1) = ψ n + (p : ℂ) * ψ (n + 2)) :
    φ = ψ := by
  have he := radial_recurrence_zero p μ (fun n => φ n - ψ n) (sub_eq_zero.mpr hzero)
    (by dsimp; linear_combination hφbase - hψbase)
    (fun n => by dsimp; linear_combination hφrec n - hψrec n)
  funext n
  exact sub_eq_zero.mp (he n)

end Dubon2026
