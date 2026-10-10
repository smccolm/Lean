import Dubon2026.UnramifiedIntegralValuations
import Mathlib.RingTheory.DedekindDomain.SelmerGroup

/-! # Original fraction-field and unit valuations at actual unramified primes -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain

variable {R S K L : Type*} [CommRing R] [CommRing S]
  [IsDedekindDomain R] [IsDedekindDomain S] [Algebra R S] [FaithfulSMul R S]
  [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
  [Algebra S L] [IsFractionRing S L] [Algebra K L] [Algebra R L]
  [IsScalarTower R K L] [IsScalarTower R S L]

/-- Actual fraction-field valuation restriction follows from the original integral valuation and actual fraction representations. -/
theorem unramified_valuation_algebraMap
    (v : HeightOneSpectrum R) (w : HeightOneSpectrum S) [w.asIdeal.LiesOver v.asIdeal]
    (he : v.asIdeal.ramificationIdx w.asIdeal = 1) (x : K) :
    w.valuation L (algebraMap K L x) = v.valuation K x := by
  have hcomm (r : R) : algebraMap K L (algebraMap R K r) =
      algebraMap S L (algebraMap R S r) :=
    (IsScalarTower.algebraMap_apply R K L r).symm.trans
      (IsScalarTower.algebraMap_apply R S L r)
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective R x
  simp only [map_div₀, hcomm, HeightOneSpectrum.valuation_of_algebraMap,
    unramified_intValuation_algebraMap v w he]

/-- The genuine integral-exponent valuation on original field units is preserved at actual primes of ramification index one. -/
theorem unramified_valuationOfNeZero_algebraMap
    (v : HeightOneSpectrum R) (w : HeightOneSpectrum S) [w.asIdeal.LiesOver v.asIdeal]
    (he : v.asIdeal.ramificationIdx w.asIdeal = 1) (x : Kˣ) :
    w.valuationOfNeZero (Units.map (algebraMap K L).toMonoidHom x) =
      v.valuationOfNeZero x := by
  apply WithZero.coe_injective
  rw [HeightOneSpectrum.valuationOfNeZero_eq, HeightOneSpectrum.valuationOfNeZero_eq]
  exact unramified_valuation_algebraMap v w he x.val

end
end Dubon2026
