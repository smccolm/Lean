import Dubon2026.AdelicLocalSphericalFixedLine

/-! # The actual intrinsic fixed-line Hecke trace equals the original Fourier coefficient -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

private theorem end_scalar_of_spanning_vector {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : Module.End ℂ V) (u : V) (z : ℂ) (hu : T u = z • u)
    (hs : ∀ x : V, ∃ c : ℂ, c • u = x) : T = z • 1 := by
  ext x
  obtain ⟨c, rfl⟩ := hs x
  rw [map_smul, hu]
  exact smul_comm c z u

private theorem trace_scalar_of_finrank_one {V : Type*} [AddCommGroup V] [Module ℂ V]
    (h : Module.finrank ℂ V = 1) (T : Module.End ℂ V) (z : ℂ) (hT : T = z • 1) :
    LinearMap.trace ℂ V T = z := by
  letI : Module.Finite ℂ V := Module.finite_of_finrank_eq_succ h
  rw [hT, map_smul, LinearMap.trace_one, h, Nat.cast_one, smul_eq_mul, mul_one]

variable {N p : ℕ} [NeZero N] [NeZero p] [Fact p.Prime] {k : ℤ}
    (F : PrimitiveCuspForm N k) (hpN : p.Coprime N)

include hpN

/-- The entire actual original spherical fixed-space endomorphism is the precise scalar dictated by the original Fourier coefficient. -/
theorem adelicLocalSphericalFixedHecke_scalar :
    finitePlaceSphericalFixedHecke p
      (adelicLocalCyclicRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))) =
    ((Real.sqrt p : ℂ) * normalizedCuspCoefficients F.toCuspForm p) • 1 := by
  have hu : finitePlaceSphericalFixedHecke p
      (adelicLocalCyclicRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))
      (adelicLocalSphericalUnit F hpN) =
        ((Real.sqrt p : ℂ) * normalizedCuspCoefficients F.toCuspForm p) • adelicLocalSphericalUnit F hpN :=
    Subtype.ext (adelicLocalClosedUnitReference_hecke_eigen F hpN)
  exact @end_scalar_of_spanning_vector
    (finitePlaceSphericalFixedSpace p (adelicLocalCyclicRepresentation F.toCuspForm _))
    inferInstance inferInstance _ (adelicLocalSphericalUnit F hpN) _ hu
    (adelicLocalSphericalUnit_spans F hpN)

/-- The genuine trace on the proved one-dimensional original spherical fixed space is the unnormalized original Fourier Hecke eigenvalue. -/
theorem adelicLocalSphericalFixedHecke_trace :
    LinearMap.trace ℂ (finitePlaceSphericalFixedSpace p
      (adelicLocalCyclicRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))))
      (finitePlaceSphericalFixedHecke p
        (adelicLocalCyclicRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime)))) =
      (Real.sqrt p : ℂ) * normalizedCuspCoefficients F.toCuspForm p := by
  exact @trace_scalar_of_finrank_one
    (finitePlaceSphericalFixedSpace p (adelicLocalCyclicRepresentation F.toCuspForm _))
    inferInstance inferInstance (adelicLocalSphericalFixedSpace_finrank F hpN) _ _
    (adelicLocalSphericalFixedHecke_scalar F hpN)

/-- The intrinsic normalized trace of the original local spherical operator is exactly the original normalized Fourier coefficient. -/
theorem adelicLocalNormalizedSphericalTrace_eq_fourier :
    finitePlaceNormalizedSphericalTrace p
      (adelicLocalCyclicRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))) =
      normalizedCuspCoefficients F.toCuspForm p := by
  have hr : (Real.sqrt p : ℂ) ≠ 0 := by
    exact_mod_cast Real.sqrt_ne_zero'.mpr (by exact_mod_cast (Fact.out : p.Prime).pos)
  unfold finitePlaceNormalizedSphericalTrace
  rw [adelicLocalSphericalFixedHecke_trace F hpN, mul_div_cancel_left₀ _ hr]

end
end Dubon2026
