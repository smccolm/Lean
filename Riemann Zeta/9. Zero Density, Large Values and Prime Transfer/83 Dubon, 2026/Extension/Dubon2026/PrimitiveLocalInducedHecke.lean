import Dubon2026.NormalizedLocalHeckeEigenvalue
import Dubon2026.PrimitiveSatakeNonSpecial

/-! # The actual Fourier-root induced model and its exact original Hecke value

This constructs the genuine principal-series model at the original roots. An
identification with the original cusp local representation still requires proof.
-/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

/-- The genuine first Fourier-defined Satake root as a complex unit, with the original other root as its inverse. No unit-modulus claim is included. -/
def primitiveSatakePlusUnit {N : ℕ} [NeZero N] {k : ℤ}
    (F : PrimitiveCuspForm N k) (p : ℕ) : ℂˣ where
  val := primitiveSatakePlus F p
  inv := primitiveSatakeMinus F p
  val_inv := (primitiveSatake_trace_det F p).2
  inv_val := (mul_comm _ _).trans (primitiveSatake_trace_det F p).2

/-- The genuine complementary Fourier-defined root as the inverse of the original first unit. -/
def primitiveSatakeMinusUnit {N : ℕ} [NeZero N] {k : ℤ}
    (F : PrimitiveCuspForm N k) (p : ℕ) : ℂˣ := (primitiveSatakePlusUnit F p)⁻¹

/-- Both genuine parameter units retain exactly the original Fourier-defined complex roots. -/
theorem primitiveSatakeUnits_val {N : ℕ} [NeZero N] {k : ℤ}
    (F : PrimitiveCuspForm N k) (p : ℕ) :
    (primitiveSatakePlusUnit F p).val = primitiveSatakePlus F p ∧
      (primitiveSatakeMinusUnit F p).val = primitiveSatakeMinus F p := ⟨rfl, rfl⟩

/-- The two actual Fourier-root units have literal product one. -/
theorem primitiveSatakeUnits_product {N : ℕ} [NeZero N] {k : ℤ}
    (F : PrimitiveCuspForm N k) (p : ℕ) :
    primitiveSatakePlusUnit F p * primitiveSatakeMinusUnit F p = 1 := mul_inv_cancel _

/-- The genuine Fourier-root principal-series spherical section. This is a vector in the actual induced model, not an assumed vector identification with the cusp representation. -/
def primitiveLocalInducedSpherical {N : ℕ} [NeZero N] {k : ℤ}
    (F : PrimitiveCuspForm N k) (p : ℕ) (hp : p.Prime) :
    NormalizedLocalPrincipalSeries (rationalPrimePlace p hp)
      (primitiveSatakePlusUnit F p) (primitiveSatakeMinusUnit F p) :=
  finitePlaceInducedSpherical (rationalPrimePlace p hp)
    (primitiveSatakePlusUnit F p * finitePlaceSqrtResidueUnit (rationalPrimePlace p hp))
    (primitiveSatakeMinusUnit F p * (finitePlaceSqrtResidueUnit (rationalPrimePlace p hp))⁻¹)

/-- The actual intrinsic Hecke sum on the original Fourier-root induced spherical section has exactly the original normalized Fourier coefficient, with the genuine square-root-prime scaling. -/
theorem primitiveLocalInducedSpherical_hecke {N : ℕ} [NeZero N] {k : ℤ}
    (F : PrimitiveCuspForm N k) (p : ℕ) [NeZero p] [Fact p.Prime] :
    finitePlaceHeckeTrace 1 p (Nat.coprime_one_right p)
      (normalizedLocalPrincipalRepresentation (rationalPrimePlace p (Fact.out : p.Prime))
        (primitiveSatakePlusUnit F p) (primitiveSatakeMinusUnit F p))
      (primitiveLocalInducedSpherical F p Fact.out) =
    ((Real.sqrt p : ℂ) * normalizedCuspCoefficients F.toCuspForm p) •
      primitiveLocalInducedSpherical F p Fact.out := by
  have he := normalizedLocalPrincipal_hecke_eigenvalue p
    (primitiveSatakePlusUnit F p) (primitiveSatakeMinusUnit F p)
  rw [localSatake_inverse_trace _ _ (primitiveSatakeUnits_product F p),
    (primitiveSatakeUnits_val F p).1, (primitiveSatakeUnits_val F p).2,
    (primitiveSatake_trace_det F p).1] at he
  exact he

/-- At every original good prime, the actual Fourier-root inducing units avoid both exceptional parameter ratios by the proved Rankin estimate. -/
theorem primitiveLocalInduced_non_special {N : ℕ} [NeZero N] {k : ℤ}
    (F : PrimitiveCuspForm N k) (hk : 2 ≤ k) {p : ℕ} (hp : p.Prime) (hpN : ¬p ∣ N) :
    ((primitiveSatakePlusUnit F p / primitiveSatakeMinusUnit F p : ℂˣ) : ℂ) ≠ p ∧
      ((primitiveSatakePlusUnit F p / primitiveSatakeMinusUnit F p : ℂˣ) : ℂ) ≠ (p : ℂ)⁻¹ := by
  simpa only [Units.val_div_eq_div_val, (primitiveSatakeUnits_val F p).1,
    (primitiveSatakeUnits_val F p).2] using primitiveSatake_non_special F hk hp hpN

end
end Dubon2026
