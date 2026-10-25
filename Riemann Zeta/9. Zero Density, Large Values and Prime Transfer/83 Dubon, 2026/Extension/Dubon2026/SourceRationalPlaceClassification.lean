import Dubon2026.SourceRationalInfinityPlace
import Mathlib.NumberTheory.RatFunc.Ostrowski

/-! DUB-17/18 -> Weil reciprocity in the rational coordinate -> finite
places and the unique pole. Pinned Ostrowski classification applies to the
existing normalized place valuation. The constant-unit and valuation-ring
identities discharge its premises; no place census is assumed. -/
namespace Dubon2026.SourceCurve.RationalFunction
noncomputable section
open IsDedekindDomain
open scoped Classical Polynomial
variable (K : Type*) [Field K]

theorem infinityPlace_ne_prime (P : HeightOneSpectrum K[X]) :
    infinityPlace K ≠ Place.ofHeightOneSpectrum (F := RatFunc K) P := by
  intro he
  have hm : (RatFunc.X : RatFunc K) ∈ (infinityPlace K).toValuationSubring := by
    rw [he]
    simpa only [RatFunc.algebraMap_X] using
      Place.algebraMap_mem_ofHeightOneSpectrum (F := RatFunc K) P Polynomial.X
  have ho := (infinityPlace K).ord_nonneg_of_mem hm
  rw [infinityPlace_ord_X] at ho
  norm_num at ho

theorem eq_prime_or_infinity (v : Place K (RatFunc K)) :
    (∃ P : HeightOneSpectrum K[X], v = Place.ofHeightOneSpectrum P) ∨ v = infinityPlace K := by
  letI : v.adicValuation.IsNontrivial :=
    inferInstanceAs (v.heightOneSpectrum.valuation (RatFunc K)).IsNontrivial
  letI : v.adicValuation.IsTrivialOn K := ⟨fun a ha => by
    exact (v.adicValuation_coe_eq_one_iff (algebraMap K v.toValuationSubring a)).mpr
      ((isUnit_iff_ne_zero.mpr ha).map _)⟩
  have hs : v.adicValuation.valuationSubring = v.toValuationSubring := by
    ext x
    exact v.adicValuation_le_one_iff
  rcases (RatFunc.valuation_isEquiv_infty_or_adic (v := v.adicValuation)).or with h | h
  · exact Or.inr (Place.ext (hs.symm.trans ((Valuation.isEquiv_iff_valuationSubring _ _).mp h)))
  · obtain ⟨P, hP, _⟩ := h
    exact Or.inl ⟨P, Place.ext (hs.symm.trans ((Valuation.isEquiv_iff_valuationSubring _ _).mp hP))⟩

end
end Dubon2026.SourceCurve.RationalFunction
