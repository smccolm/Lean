import Dubon2026.LocalCoefficientReduction
import Dubon2026.AdicPowerQuotientTopology

/-! # Continuity of the actual residue reduction in the original adic topology -/

namespace Dubon2026

noncomputable section

variable {O A : Type*} [CommRing O] [IsLocalRing O]
  [TopologicalSpace (IsLocalRing.ResidueField O)]
  [CommRing A] [IsLocalRing A] [Algebra O A] [WithIdeal A]

/-- The original coefficient residue map is continuous for the genuine maximal-adic topology. The topology on the auxiliary quotient is constructed from the original quotient map. -/
theorem localCoefficientReduction_continuous
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (e : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O) :
    Continuous (localCoefficientReduction e) := by
  letI : TopologicalSpace (IsLocalRing.ResidueField A) :=
    inferInstanceAs (TopologicalSpace (A ⧸ IsLocalRing.maximalIdeal A))
  letI : DiscreteTopology (IsLocalRing.ResidueField A) := by
    apply QuotientAddGroup.discreteTopology (N := (IsLocalRing.maximalIdeal A).toAddSubgroup)
    simpa only [pow_one, hA] using
      (isAdic_iff.mp (rfl : IsAdic (WithIdeal.i : Ideal A))).1 1
  have he : Continuous e := continuous_of_discreteTopology
  exact he.comp (QuotientRing.isOpenQuotientMap_mk (IsLocalRing.maximalIdeal A)).continuous

end
end Dubon2026
