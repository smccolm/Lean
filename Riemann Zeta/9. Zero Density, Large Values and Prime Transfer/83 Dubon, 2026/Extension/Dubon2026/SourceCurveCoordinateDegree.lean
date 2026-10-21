import Dubon2026.SourceCurveCoordinatePlaces
import Mathlib.FieldTheory.RatFunc.Basic

/-! DUB-17/18 -> principal-divisor degree zero. Pinned Dedekind
ramification/inertia sums are transported to the actual positive-order places
with their normalized orders and literal residue degrees. Integral chart
containment is the only local input; the original-field consumer derives it.
-/
namespace Dubon2026.SourceCurve
noncomputable section
open Polynomial IsDedekindDomain

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable [Algebra K R] [Algebra K[X] R] [IsScalarTower K K[X] R]
variable [Algebra R F] [IsFractionRing R F] [IsScalarTower K R F]
variable [Module.IsTorsionFree K[X] R]

theorem coordinatePrimePlaceEquiv_weight (hx : algebraMap K[X] R X ≠ 0)
    (hchart : ∀ v : Place K F,
      0 < v.ord (algebraMap R F (algebraMap K[X] R X)) →
        ∀ r : R, algebraMap R F r ∈ v.toValuationSubring)
    (P : (coordinateZeroIdeal K).primesOver R) :
    let v := (coordinatePrimePlaceEquiv hx hchart P).1
    v.ord (algebraMap R F (algebraMap K[X] R X)) * (Module.finrank K v.ResidueField : ℤ) =
      ((coordinateZeroIdeal K).ramificationIdx P.1 : ℤ) *
        ((coordinateZeroIdeal K).inertiaDeg P.1 : ℤ) := by
  letI : (coordinatePrimeHeight P).asIdeal.LiesOver (coordinateZeroIdeal K) := P.2.2
  change (Place.ofHeightOneSpectrum (K := K) (F := F) (coordinatePrimeHeight P)).ord _ *
    (Module.finrank K (Place.ofHeightOneSpectrum (K := K) (F := F)
      (coordinatePrimeHeight P)).ResidueField : ℤ) = _
  rw [Place.ord_ofHeightOneSpectrum_eq_ramificationIdx (coordinatePrimeHeight P) hx,
    ← coordinateZero_inertiaDeg_eq_finrank (K := K) (F := F) (coordinatePrimeHeight P)]
  rfl

variable [Algebra (RatFunc K) F] [Algebra K[X] F]
variable [IsScalarTower K[X] R F] [IsScalarTower K[X] (RatFunc K) F]
variable [Module.Finite K[X] R]

theorem sum_positive_orders_eq_finrank_of_chart
    (hx : algebraMap K[X] R X ≠ 0)
    (hchart : ∀ v : Place K F,
      0 < v.ord (algebraMap R F (algebraMap K[X] R X)) →
        ∀ r : R, algebraMap R F r ∈ v.toValuationSubring) :
    (∑ᶠ v : {v : Place K F // 0 < v.ord (algebraMap R F (algebraMap K[X] R X))},
      v.1.ord (algebraMap R F (algebraMap K[X] R X)) *
        (Module.finrank K v.1.ResidueField : ℤ)) = (Module.finrank (RatFunc K) F : ℤ) := by
  classical
  rw [← finsum_comp_equiv (coordinatePrimePlaceEquiv hx hchart)]
  simp_rw [coordinatePrimePlaceEquiv_weight hx hchart]
  rw [finsum_set_coe_eq_finsum_mem (f := fun P : Ideal R =>
      ((coordinateZeroIdeal K).ramificationIdx P : ℤ) *
        ((coordinateZeroIdeal K).inertiaDeg P : ℤ)) ((coordinateZeroIdeal K).primesOver R),
    ← IsDedekindDomain.coe_primesOverFinset (coordinateZeroIdeal_ne_bot K) R,
    finsum_mem_coe_finset]
  exact_mod_cast Ideal.sum_ramification_inertia R (RatFunc K) F (coordinateZeroIdeal_ne_bot K)

end
end Dubon2026.SourceCurve
