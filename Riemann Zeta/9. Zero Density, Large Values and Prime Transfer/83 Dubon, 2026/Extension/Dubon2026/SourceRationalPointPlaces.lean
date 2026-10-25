import Dubon2026.SourceRationalPlaceClassification
import Dubon2026.SourceCurveRamificationOrders
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! DUB-17/18 -> original Weil reciprocity -> the rational-coordinate
case. The actual finite places are the linear polynomial primes over closed
constants. Native prime orders give order one for X-a directly, avoiding
the external divisibility-based renormalization argument. -/
namespace Dubon2026.SourceCurve.RationalFunction
noncomputable section
open Polynomial IsDedekindDomain WithZero
open scoped Classical
variable (K : Type*) [Field K]

/-- The actual linear prime of the polynomial chart at a constant. -/
def pointPrime (a : K) : HeightOneSpectrum K[X] where
  asIdeal := Ideal.span {X - C a}
  isPrime := (PrincipalIdealRing.isMaximal_of_irreducible (irreducible_X_sub_C a)).isPrime
  ne_bot := by simpa only [ne_eq, Ideal.span_singleton_eq_bot] using X_sub_C_ne_zero a

/-- The actual finite place with coordinate value `a`. -/
def pointPlace (a : K) : Place K (RatFunc K) := Place.ofHeightOneSpectrum (pointPrime K a)

theorem pointPlace_ord_parameter (a : K) :
    (pointPlace K a).ord (algebraMap K[X] (RatFunc K) (X - C a)) = 1 := by
  have hn : algebraMap K[X] (RatFunc K) (X - C a) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr (X_sub_C_ne_zero a)
  rw [pointPlace, Place.ord_ofHeightOneSpectrum _ hn,
    HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_singleton _ (X_sub_C_ne_zero a) rfl, log_exp]
  norm_num

theorem prime_eq_point [IsAlgClosed K] (P : HeightOneSpectrum K[X]) :
    ∃ a : K, P = pointPrime K a := by
  obtain ⟨p, hp⟩ := (IsPrincipalIdealRing.principal P.asIdeal).principal
  rw [Ideal.submodule_span_eq] at hp
  have hp0 : p ≠ 0 := by
    rintro rfl
    exact P.ne_bot (hp.trans (by simp))
  have hprime := P.isPrime
  rw [hp] at hprime
  have hirr := ((Ideal.span_singleton_prime hp0).mp hprime).irreducible
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root p (by
    rw [IsAlgClosed.degree_eq_one_of_irreducible K hirr]
    exact one_ne_zero)
  refine ⟨a, HeightOneSpectrum.ext ?_⟩
  change P.asIdeal = Ideal.span {X - C a}
  rw [hp]
  exact (Ideal.span_singleton_eq_span_singleton.mpr
    ((irreducible_X_sub_C a).associated_of_dvd hirr (dvd_iff_isRoot.mpr ha))).symm

theorem eq_point_or_infinity [IsAlgClosed K] (v : Place K (RatFunc K)) :
    (∃ a : K, v = pointPlace K a) ∨ v = infinityPlace K := by
  rcases eq_prime_or_infinity K v with ⟨P, hP⟩ | h
  · obtain ⟨a, rfl⟩ := prime_eq_point K P
    exact Or.inl ⟨a, hP⟩
  · exact Or.inr h

end
end Dubon2026.SourceCurve.RationalFunction
