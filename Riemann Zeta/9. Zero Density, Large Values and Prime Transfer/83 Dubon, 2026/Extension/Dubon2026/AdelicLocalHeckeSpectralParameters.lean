import Dubon2026.AdelicLocalSphericalTrace
import Dubon2026.SymmetricEulerPolynomial

/-! # Original Fourier-root data recovered from the actual local fixed-line Hecke operator

These are the two roots of the intrinsic determinant-one Hecke quadratic.
Their comparison with the original Fourier roots is proved below. A full
Satake-transform theorem is not assumed by these definitions.
-/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Polynomial

variable {N p : ℕ} [NeZero N] [NeZero p] [Fact p.Prime] {k : ℤ} (F : PrimitiveCuspForm N k)

/-- The first root recovered from the actual normalized spherical fixed-line Hecke trace. -/
def adelicLocalHeckeRootPlus : ℂ :=
  satakeRootPlus (finitePlaceNormalizedSphericalTrace p
    (adelicLocalCyclicRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))))

/-- The second root recovered from the same actual local Hecke trace. -/
def adelicLocalHeckeRootMinus : ℂ :=
  satakeRootMinus (finitePlaceNormalizedSphericalTrace p
    (adelicLocalCyclicRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))))

/-- The first intrinsic local Hecke root equals the root constructed from the actual original Fourier coefficient. -/
theorem adelicLocalHeckeRootPlus_eq_fourier (hpN : p.Coprime N) :
    adelicLocalHeckeRootPlus (p := p) F = primitiveSatakePlus F p :=
  congrArg satakeRootPlus (adelicLocalNormalizedSphericalTrace_eq_fourier F hpN)

/-- The second intrinsic local Hecke root equals its original Fourier counterpart. -/
theorem adelicLocalHeckeRootMinus_eq_fourier (hpN : p.Coprime N) :
    adelicLocalHeckeRootMinus (p := p) F = primitiveSatakeMinus F p :=
  congrArg satakeRootMinus (adelicLocalNormalizedSphericalTrace_eq_fourier F hpN)

/-- Every original symmetric-power Fourier Euler polynomial is recovered from the roots of the genuine original local Hecke operator. -/
theorem adelicLocalHecke_symmetricEulerPolynomial (hpN : p.Coprime N) (r : ℕ) :
    symmetricEulerPolynomial (adelicLocalHeckeRootPlus (p := p) F) (adelicLocalHeckeRootMinus (p := p) F) r =
      primitiveSymmetricEulerPolynomial F p r := by
  rw [adelicLocalHeckeRootPlus_eq_fourier F hpN, adelicLocalHeckeRootMinus_eq_fourier F hpN]
  rfl

/-- The degree-one coefficient of every such actual Hecke-root polynomial is the negative original prime-power Fourier coefficient. -/
theorem adelicLocalHecke_symmetricEulerPolynomial_coeff_one (hpN : p.Coprime N) (r : ℕ) :
    (symmetricEulerPolynomial (adelicLocalHeckeRootPlus (p := p) F)
      (adelicLocalHeckeRootMinus (p := p) F) r).coeff 1 =
      -normalizedCuspCoefficients F.toCuspForm (p ^ r) := by
  rw [adelicLocalHecke_symmetricEulerPolynomial F hpN]
  have hp := (Fact.out : p.Prime)
  exact primitiveSymmetricEulerPolynomial_coeff_one F hp ((hp.coprime_iff_not_dvd).mp hpN) r

end
end Dubon2026
