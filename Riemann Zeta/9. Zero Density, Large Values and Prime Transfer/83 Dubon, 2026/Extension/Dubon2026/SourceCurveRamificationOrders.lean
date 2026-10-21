import Dubon2026.SourceCurvePrimeResidues
import Mathlib.NumberTheory.RamificationInertia.Basic

/-! DUB-17/18 -> original principal-divisor degree zero. The order of a
coordinate at an actual prime place is the ramification index of its principal
base ideal. This consumes the pinned multiplicity formulas on both sides.
-/
namespace Dubon2026.SourceCurve.Place
noncomputable section
open IsDedekindDomain WithZero
open IsDedekindDomain.HeightOneSpectrum

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]
variable [Algebra K R] [IsScalarTower K R F]

theorem ord_ofHeightOneSpectrum_eq_multiplicity (P : HeightOneSpectrum R)
    {r : R} (hr : r ≠ 0) :
    (ofHeightOneSpectrum (K := K) (F := F) P).ord (algebraMap R F r) =
      (multiplicity P.asIdeal (Ideal.span {r}) : ℤ) := by
  have hrF : algebraMap R F r ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective R F).ne hr
  rw [ord_ofHeightOneSpectrum P hrF,
    valuation_of_algebraMap, intValuation_eq_exp_neg_multiplicity _ hr, log_exp, neg_neg]

theorem ord_ofHeightOneSpectrum_eq_ramificationIdx
    {A : Type*} [CommRing A] [Algebra A R] (P : HeightOneSpectrum R)
    {a : A} (ha : algebraMap A R a ≠ 0) :
    (ofHeightOneSpectrum (K := K) (F := F) P).ord
        (algebraMap R F (algebraMap A R a)) =
      ((Ideal.span {a} : Ideal A).ramificationIdx P.asIdeal : ℤ) := by
  have hm : Ideal.map (algebraMap A R) (Ideal.span {a}) =
      Ideal.span {algebraMap A R a} := by rw [Ideal.map_span, Set.image_singleton]
  have hn : Ideal.map (algebraMap A R) (Ideal.span {a}) ≠ ⊥ := by
    rw [hm, ne_eq, Ideal.span_singleton_eq_bot]
    exact ha
  rw [ord_ofHeightOneSpectrum_eq_multiplicity P ha,
    Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity hn P.isPrime, hm]

end
end Dubon2026.SourceCurve.Place
