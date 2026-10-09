import Dubon2026.AdelicLocalSphericalFormula
import Dubon2026.SphericalSatakeFormula

/-! # The original local spherical coefficients in the actual Fourier Satake roots -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

/-- The actual good-prime spherical matrix coefficient has the exact formula in the primitive form's own Satake roots, including repeated roots. -/
theorem adelicCyclicLocal_primitive_radial_satake {N p : ℕ} [NeZero N] [NeZero p]
    [Fact p.Prime] {k : ℤ} (F : PrimitiveCuspForm N k) (hpN : p.Coprime N)
    (x : AdelicCyclicHilbert F.toCuspForm)
    (hx : x ∈ adelicLocalFixedSpace F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))) (n : ℕ) :
    @finitePlaceRadialCoefficient (AdelicCyclicHilbert F.toCuspForm)
      inferInstance inferInstance p inferInstance inferInstance
      (adelicCyclicLocalRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))
      x (adelicCyclicHilbertGenerator F.toCuspForm) (n + 2) =
    inner ℂ x (adelicCyclicHilbertGenerator F.toCuspForm) *
      (((Real.sqrt p : ℂ) ^ (n + 2))⁻¹ *
        ((p : ℂ) * satakeSymmetricTrace (primitiveSatakePlus F p) (primitiveSatakeMinus F p) (n + 2) -
          satakeSymmetricTrace (primitiveSatakePlus F p) (primitiveSatakeMinus F p) n) / ((p : ℂ) + 1)) := by
  rw [adelicCyclicLocal_primitive_radial_formula F hpN x hx,
    ← (primitiveSatake_trace_det F p).1,
    sphericalChebyshevCoefficient_satake (primitiveSatake_trace_det F p).2]

/-- The actual local spherical matrix coefficient is expressed by the original primitive Fourier prime-power coefficients with the exact p+1 and square-root factors. -/
theorem adelicCyclicLocal_primitive_radial_primePowers {N p : ℕ} [NeZero N] [NeZero p]
    [Fact p.Prime] {k : ℤ} (F : PrimitiveCuspForm N k) (hpN : p.Coprime N)
    (x : AdelicCyclicHilbert F.toCuspForm)
    (hx : x ∈ adelicLocalFixedSpace F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))) (n : ℕ) :
    @finitePlaceRadialCoefficient (AdelicCyclicHilbert F.toCuspForm)
      inferInstance inferInstance p inferInstance inferInstance
      (adelicCyclicLocalRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))
      x (adelicCyclicHilbertGenerator F.toCuspForm) (n + 2) =
    inner ℂ x (adelicCyclicHilbertGenerator F.toCuspForm) *
      (((Real.sqrt p : ℂ) ^ (n + 2))⁻¹ *
        ((p : ℂ) * normalizedCuspCoefficients F.toCuspForm (p ^ (n + 2)) -
          normalizedCuspCoefficients F.toCuspForm (p ^ n)) / ((p : ℂ) + 1)) := by
  have hpN' : ¬p ∣ N := (Fact.out : p.Prime).coprime_iff_not_dvd.mp hpN
  rw [adelicCyclicLocal_primitive_radial_formula F hpN x hx,
    primitive_sphericalChebyshevCoefficient_primePower F (Fact.out : p.Prime) hpN']

end
end Dubon2026
