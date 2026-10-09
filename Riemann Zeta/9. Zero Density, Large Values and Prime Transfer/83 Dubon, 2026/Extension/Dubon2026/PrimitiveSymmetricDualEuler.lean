import Dubon2026.HomogeneousSatakeEuler
import Dubon2026.PrimitiveInducedCyclicQuotient
import Dubon2026.PrimitiveSymmetricSpectral
import Dubon2026.PrimitiveHigherEulerConvergence

/-! # Original good-prime induced factors and genuine symmetric dual Euler determinants -/

namespace Dubon2026

noncomputable section
open Matrix MvPolynomial IsDedekindDomain

/-- The literal general-linear diagonal of the primitive form's own two Fourier-defined root units. Its representation interpretation below is restricted to genuine good primes. -/
def primitiveFourierRootMatrix {N : ℕ} [NeZero N] {k : ℤ}
    (F : PrimitiveCuspForm N k) (p : ℕ) : GeneralLinearGroup (Fin 2) ℂ :=
  gl2UnitDiagonalPair (primitiveSatakePlusUnit F p) (primitiveSatakeMinusUnit F p)

/-- Apply the original full degree-r homogeneous general-linear representation to the actual Fourier-root diagonal. -/
def primitiveSymmetricDualOperator {N : ℕ} [NeZero N] {k : ℤ}
    (F : PrimitiveCuspForm N k) (p r : ℕ) :
    Module.End ℂ (homogeneousSubmodule (Fin 2) ℂ r) :=
  homogeneousGLRepresentation r (primitiveFourierRootMatrix F p)

/-- The literal determinant of identity minus X times the actual homogeneous representation of the original Fourier-root diagonal. -/
def primitiveSymmetricMatrixEulerPolynomial {N : ℕ} [NeZero N] {k : ℤ}
    (F : PrimitiveCuspForm N k) (p r : ℕ) : Polynomial ℂ :=
  Matrix.det ((1 : Matrix (Fin (r + 1)) (Fin (r + 1)) (Polynomial ℂ)) - (Polynomial.X : Polynomial ℂ) •
    (LinearMap.toMatrix (binaryHomogeneousMonomialBasis r) (binaryHomogeneousMonomialBasis r)
      (primitiveSymmetricDualOperator F p r)).map Polynomial.C)

/-- The original spectral symmetric Euler polynomial is exactly the determinant polynomial of the genuine homogeneous representation of its own Fourier-root matrix. -/
theorem primitiveSymmetricMatrixEulerPolynomial_eq {N : ℕ} [NeZero N] {k : ℤ}
    (F : PrimitiveCuspForm N k) (p r : ℕ) :
    primitiveSymmetricMatrixEulerPolynomial F p r = primitiveSymmetricEulerPolynomial F p r := by
  change homogeneousMatrixEulerPolynomial r
    (gl2UnitDiagonalPair (primitiveSatakePlusUnit F p) (primitiveSatakeMinusUnit F p)).val = _
  rw [homogeneousUnitDiagonal_euler, (primitiveSatakeUnits_val F p).1,
    (primitiveSatakeUnits_val F p).2]
  rfl

/-- At each actual good prime, the original smooth cusp factor is its proved induced spherical subquotient, and the original symmetric spectral factor is the reciprocal determinant of the genuine symmetric homogeneous dual action of those same parameters. This does not assert a higher automorphic lift or analytic continuation. -/
theorem primitiveLocalInduced_actual_symmetric_factor {N p : ℕ} [NeZero N] [NeZero p]
    [Fact p.Prime] {k : ℤ} (F : PrimitiveCuspForm N k) (hpN : p.Coprime N) (r : ℕ) (s : ℂ) :
    Nonempty (Representation.Equiv (primitiveLocalInducedQuotientRepresentation F hpN)
      (adelicLocalSmoothRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))) ∧
    primeSpectralEulerFactor (primitiveSymmetricSpectralRoots F r) ⟨p, Fact.out⟩ s =
      ((primitiveSymmetricMatrixEulerPolynomial F p r).eval ((p : ℂ) ^ (-s)))⁻¹ := by
  refine ⟨(primitiveLocalInduced_spherical_constituent F hpN).1, ?_⟩
  rw [primitiveSymmetricMatrixEulerPolynomial_eq]
  exact primitiveSymmetricSpectralEulerFactor_good F r ⟨p, Fact.out⟩
    ((Fact.out : p.Prime).coprime_iff_not_dvd.mp hpN) s

/-- The original incomplete local factor formed from the actual symmetric dual determinant; exactly the primes dividing the original level are omitted. -/
def primitiveSymmetricMatrixLocalFactor {N : ℕ} [NeZero N] {k : ℤ}
    (F : PrimitiveCuspForm N k) (r : ℕ) (p : Nat.Primes) (s : ℂ) : ℂ :=
  if (p : ℕ) ∣ N then 1 else
    ((primitiveSymmetricMatrixEulerPolynomial F p r).eval (((p : ℕ) : ℂ) ^ (-s)))⁻¹

/-- The actual representation-determinant local factor equals the original spectral factor at every prime, with identical finite ramified omission. -/
theorem primitiveSymmetricMatrixLocalFactor_eq {N : ℕ} [NeZero N] {k : ℤ}
    (F : PrimitiveCuspForm N k) (r : ℕ) (p : Nat.Primes) (s : ℂ) :
    primitiveSymmetricMatrixLocalFactor F r p s =
      primeSpectralEulerFactor (primitiveSymmetricSpectralRoots F r) p s := by
  by_cases hpN : (p : ℕ) ∣ N
  · rw [primitiveSymmetricMatrixLocalFactor, if_pos hpN,
      primitiveSymmetricSpectralEulerFactor_bad F r p hpN]
  · rw [primitiveSymmetricMatrixLocalFactor, if_neg hpN,
      primitiveSymmetricMatrixEulerPolynomial_eq,
      primitiveSymmetricSpectralEulerFactor_good F r p hpN]

/-- In its proved original far convergence half-plane, the actual symmetric dual determinant Euler product converges to the same original incomplete symmetric L-function. No purity or higher continuation premise is used. -/
theorem primitiveSymmetricMatrix_hasProd_far {N : ℕ} [NeZero N] {k : ℤ}
    (F : PrimitiveCuspForm N k) (hk : 2 ≤ k) (r : ℕ) {s : ℂ} (hs : (r : ℝ) + 1 < s.re) :
    HasProd (fun p : Nat.Primes => primitiveSymmetricMatrixLocalFactor F r p s)
      (primitiveSymmetricLFunction F r s) := by
  have he : (fun p : Nat.Primes => primitiveSymmetricMatrixLocalFactor F r p s) =
      (fun p : Nat.Primes => primeSpectralEulerFactor (primitiveSymmetricSpectralRoots F r) p s) :=
    funext (fun p => primitiveSymmetricMatrixLocalFactor_eq F r p s)
  rw [he]
  exact primitive_higher_symmetric_hasProd_far F hk r hs

end
end Dubon2026
