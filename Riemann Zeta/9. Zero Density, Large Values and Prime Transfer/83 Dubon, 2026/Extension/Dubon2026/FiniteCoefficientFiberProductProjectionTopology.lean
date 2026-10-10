import Dubon2026.FiniteCoefficientFiberProductTopology

/-! # Continuity of the genuine coefficient projections from the actual maximal-adic fiber product -/

namespace Dubon2026
noncomputable section

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  [IsLocalRing A] [IsLocalRing B] [Finite A] [Finite B] [WithIdeal A] [WithIdeal B]

/-- The actual first coefficient projection is continuous from the genuine fiber-product maximal-adic topology to the original first coefficient topology. -/
theorem finiteCoefficientFiberProductFst_adic_continuous
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (hB : (WithIdeal.i : Ideal B) = IsLocalRing.maximalIdeal B)
    (f : A →+* C) (g : B →+* C) [IsLocalHom g] :
    (letI := coefficientFiberProduct_isLocalRing f g
     @Continuous (CoefficientFiberProduct f g) A
       (IsLocalRing.maximalIdeal (CoefficientFiberProduct f g)).adicTopology
       inferInstance (coefficientFiberProductFst f g)) := by
  letI := coefficientFiberProduct_isLocalRing f g
  rw [finiteCoefficientFiberProduct_original_adicTopology_eq_product hA hB f g]
  exact continuous_fst.comp continuous_subtype_val

/-- The actual second coefficient projection is continuous from the genuine fiber-product maximal-adic topology to the original second coefficient topology. -/
theorem finiteCoefficientFiberProductSnd_adic_continuous
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (hB : (WithIdeal.i : Ideal B) = IsLocalRing.maximalIdeal B)
    (f : A →+* C) (g : B →+* C) [IsLocalHom g] :
    (letI := coefficientFiberProduct_isLocalRing f g
     @Continuous (CoefficientFiberProduct f g) B
       (IsLocalRing.maximalIdeal (CoefficientFiberProduct f g)).adicTopology
       inferInstance (coefficientFiberProductSnd f g)) := by
  letI := coefficientFiberProduct_isLocalRing f g
  rw [finiteCoefficientFiberProduct_original_adicTopology_eq_product hA hB f g]
  exact continuous_snd.comp continuous_subtype_val

end
end Dubon2026
