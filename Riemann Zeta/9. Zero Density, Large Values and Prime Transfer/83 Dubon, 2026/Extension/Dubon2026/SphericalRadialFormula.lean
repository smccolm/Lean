import Dubon2026.SphericalChebyshevCoefficient

/-! # A closed formula forced by the genuine local spherical recurrence -/

namespace Dubon2026

noncomputable section

/-- Every sequence satisfying the actual spherical Hecke boundary equation and recurrence has its exact normalized Chebyshev formula. -/
theorem radial_recurrence_chebyshev_formula (p : ℕ) [NeZero p] (r z : ℂ)
    (hr : r ≠ 0) (hs : r ^ 2 = (p : ℂ)) (φ : ℕ → ℂ)
    (hb : (r * z) * φ 0 = ((p : ℂ) + 1) * φ 1)
    (hrec : ∀ n, (r * z) * φ (n + 1) = φ n + (p : ℂ) * φ (n + 2)) (n : ℕ) :
    φ n = φ 0 * sphericalChebyshevCoefficient p r z n := by
  have hp1 : (p : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero p
  have he := radial_recurrence_unique p (r * z) φ
    (fun j => φ 0 * sphericalChebyshevCoefficient p r z j)
    (by dsimp only; rw [sphericalChebyshevCoefficient_zero _ _ _ hp1, mul_one]) hb
    (by
      have h := sphericalChebyshevCoefficient_boundary p r z hr hs hp1
      dsimp
      linear_combination φ 0 * h)
    hrec
    (fun j => by
      have h := sphericalChebyshevCoefficient_recurrence p r z hr hs hp1 j
      dsimp
      linear_combination φ 0 * h)
  exact congrFun he n

end
end Dubon2026
