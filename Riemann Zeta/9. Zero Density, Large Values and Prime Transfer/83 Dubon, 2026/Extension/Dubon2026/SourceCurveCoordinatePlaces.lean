import Dubon2026.SourceCurveCoordinateResidues

/-! DUB-17/18 -> principal-divisor degree zero. The actual primes over the
zero-coordinate ideal correspond exactly to positive-order places when the
chart is integral at those places. The integral-closure consumer supplies
that narrower chart-containment fact.
-/
namespace Dubon2026.SourceCurve
noncomputable section
open Polynomial IsDedekindDomain

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable [Algebra K R] [Algebra K[X] R] [IsScalarTower K K[X] R]
variable [Algebra R F] [IsFractionRing R F] [IsScalarTower K R F]
variable [Module.IsTorsionFree K[X] R]

omit [IsDedekindDomain R] [Algebra K R] [IsScalarTower K K[X] R]
  [Module.IsTorsionFree K[X] R] in
theorem liesOver_coordinateZero_iff (P : Ideal R) [P.IsPrime] :
    P.LiesOver (coordinateZeroIdeal K) ↔ algebraMap K[X] R X ∈ P := by
  constructor
  · intro h
    letI := h
    exact (Ideal.mem_of_liesOver P (coordinateZeroIdeal K) X).mp (Ideal.subset_span (by simp))
  · intro h
    refine ⟨(coordinateZeroIdeal_isMaximal K).eq_of_le
      (Ideal.IsPrime.ne_top (inferInstance : (P.under K[X]).IsPrime)) ?_⟩
    exact Ideal.span_le.mpr (by simpa only [Set.singleton_subset_iff, Ideal.mem_under] using h)

/-- The actual height-one prime attached to a prime over the zero coordinate. -/
def coordinatePrimeHeight (P : (coordinateZeroIdeal K).primesOver R) :
    HeightOneSpectrum R :=
  ⟨P.1, P.2.1, Ideal.ne_bot_of_mem_primesOver (coordinateZeroIdeal_ne_bot K) P.2⟩

omit [Algebra K R] [IsScalarTower K K[X] R] in
theorem coordinatePrimeHeight_mem (P : (coordinateZeroIdeal K).primesOver R) :
    algebraMap K[X] R X ∈ (coordinatePrimeHeight P).asIdeal := by
  letI : P.1.IsPrime := P.2.1
  exact (liesOver_coordinateZero_iff P.1).mp P.2.2

/-- Exact correspondence between zero-coordinate primes and positive-order places. -/
def coordinatePrimePlaceEquiv (hx : algebraMap K[X] R X ≠ 0)
    (hchart : ∀ v : Place K F,
      0 < v.ord (algebraMap R F (algebraMap K[X] R X)) →
        ∀ r : R, algebraMap R F r ∈ v.toValuationSubring) :
    (coordinateZeroIdeal K).primesOver R ≃
      {v : Place K F // 0 < v.ord (algebraMap R F (algebraMap K[X] R X))} where
  toFun P := ⟨Place.ofHeightOneSpectrum (coordinatePrimeHeight P), by
    rw [← Place.mem_center_iff_ord_pos _
      (Place.algebraMap_mem_ofHeightOneSpectrum (coordinatePrimeHeight P)) hx,
      Place.center_ofHeightOneSpectrum]
    exact coordinatePrimeHeight_mem P⟩
  invFun v := ⟨Place.center R v.1 (hchart v.1 v.2), inferInstance, by
    rw [liesOver_coordinateZero_iff]
    exact (Place.mem_center_iff_ord_pos v.1 (hchart v.1 v.2) hx).mpr v.2⟩
  left_inv P := by
    apply Subtype.ext
    exact Place.center_ofHeightOneSpectrum (coordinatePrimeHeight P)
  right_inv v := by
    apply Subtype.ext
    exact Place.ofHeightOneSpectrum_center v.1 (hchart v.1 v.2)

end
end Dubon2026.SourceCurve
