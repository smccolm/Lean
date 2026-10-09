import Dubon2026.SphericalChebyshevCoefficient
import Dubon2026.SatakeSymmetricTrace

/-! # The spherical formula in the actual Satake roots, without dividing by their difference -/

namespace Dubon2026

noncomputable section
open Polynomial

/-- The exact spherical expression in determinant-one Satake traces remains valid when the two roots coincide. -/
theorem sphericalChebyshevCoefficient_satake {α β : ℂ} (hprod : α * β = 1)
    (q r : ℂ) (n : ℕ) :
    sphericalChebyshevCoefficient q r (α + β) (n + 2) =
      (r ^ (n + 2))⁻¹ *
        (q * satakeSymmetricTrace α β (n + 2) - satakeSymmetricTrace α β n) / (q + 1) := by
  rw [satakeSymmetricTrace_chebyshev hprod, satakeSymmetricTrace_chebyshev hprod]
  have hn : ((n + 2 : ℕ) : ℤ) - 2 = (n : ℤ) := by omega
  simp only [sphericalChebyshevCoefficient, sphericalChebyshevNumerator, hn]

/-- The genuine primitive prime-power coefficients give precisely the complete Chebyshev numerator of the local spherical formula. -/
theorem primitive_sphericalChebyshevCoefficient_primePower {Q : ℕ} [NeZero Q] {k : ℤ}
    (F : PrimitiveCuspForm Q k) {p : ℕ} (hp : Nat.Prime p) (hpQ : ¬p ∣ Q) (n : ℕ) :
    sphericalChebyshevCoefficient p (Real.sqrt p) (normalizedCuspCoefficients F.toCuspForm p) (n + 2) =
      ((Real.sqrt p : ℂ) ^ (n + 2))⁻¹ *
        ((p : ℂ) * normalizedCuspCoefficients F.toCuspForm (p ^ (n + 2)) -
          normalizedCuspCoefficients F.toCuspForm (p ^ n)) / ((p : ℂ) + 1) := by
  rw [primitive_primePower_eq_satakeTrace F hp hpQ, primitive_primePower_eq_satakeTrace F hp hpQ,
    ← (primitiveSatake_trace_det F p).1]
  exact sphericalChebyshevCoefficient_satake (primitiveSatake_trace_det F p).2 p (Real.sqrt p) n

end
end Dubon2026
