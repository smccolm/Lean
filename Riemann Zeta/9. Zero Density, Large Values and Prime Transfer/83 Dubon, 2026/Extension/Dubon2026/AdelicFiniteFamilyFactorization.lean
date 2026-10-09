import Dubon2026.AdelicFinitePlaceProduct

/-! # Exact factorization of original adelic GL2 at any finite family of genuine places -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

variable {I : Type*} (v : I → HeightOneSpectrum ℤ)

/-- Simultaneous evaluation of the actual original adelic group at the selected genuine places. -/
def adelicFinitePlaceEvaluation :
    RationalAdelicGL2 →* (∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) where
  toFun a i := adelicPlaceGL2Hom (v i) a
  map_one' := by funext i; exact map_one (adelicPlaceGL2Hom (v i))
  map_mul' a b := by funext i; exact map_mul (adelicPlaceGL2Hom (v i)) a b

/-- The genuine full complementary subgroup has identity at every selected original finite place. -/
def adelicFiniteFamilyAwayGroup : Subgroup RationalAdelicGL2 := (adelicFinitePlaceEvaluation v).ker

/-- Every actual element of the genuine full complementary subgroup has its literal selected coordinate equal to identity. -/
theorem adelicFiniteFamilyAwayGroup_place (a : adelicFiniteFamilyAwayGroup v) (i : I) :
    adelicPlaceGL2Hom (v i) a.val = 1 := congrFun a.property i

variable [Fintype I] (hv : Function.Injective v)

/-- The genuine selected local coordinates of an original product with its full complement are exactly the supplied local matrices. -/
theorem adelicFinitePlaceEvaluation_product_away
    (g : ∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ))
    (a : adelicFiniteFamilyAwayGroup v) :
    adelicFinitePlaceEvaluation v (adelicFinitePlaceProduct v hv g * a.val) = g := by
  funext i
  change adelicPlaceGL2Hom (v i) (adelicFinitePlaceProduct v hv g * a.val) = g i
  rw [map_mul, adelicPlaceGL2Hom_finitePlaceProduct, adelicFiniteFamilyAwayGroup_place, mul_one]

/-- Every genuine selected local product commutes with every original full complementary matrix. -/
theorem adelicFinitePlaceProduct_away_commute
    (g : ∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ))
    (a : adelicFiniteFamilyAwayGroup v) :
    Commute (adelicFinitePlaceProduct v hv g) a.val := by
  have hc (i : I) (x : GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) :
      Commute a.val (rationalAdelicFiniteGL2Embedding (finiteAdelicLocalGL2 (v i) x)) := by
    obtain ⟨b, hb⟩ := adelicFullAwayEmbedding_of_place_one (v i) a.val
      (adelicFiniteFamilyAwayGroup_place v a i)
    rw [← hb]
    exact (adelicLocal_fullAway_commute (v i) x b).symm
  exact (MonoidHom.commute_noncommPiCoprod
    (fun i => rationalAdelicFiniteGL2Embedding.comp (finiteAdelicLocalGL2Hom (v i))) hc g).symm

/-- Original adelic GL2 is exactly the genuine finite product of selected local groups times the actual remaining-coordinate subgroup. -/
def adelicFiniteFamilyEquiv :
    ((∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) × adelicFiniteFamilyAwayGroup v) ≃*
      RationalAdelicGL2 where
  toFun a := adelicFinitePlaceProduct v hv a.1 * a.2.val
  invFun a := (adelicFinitePlaceEvaluation v a,
    ⟨adelicFinitePlaceRemoval v hv a, funext (fun i => adelicFinitePlaceRemoval_same v hv i a)⟩)
  left_inv a := by
    apply Prod.ext
    · exact adelicFinitePlaceEvaluation_product_away v hv a.1 a.2
    · apply Subtype.ext
      change (adelicFinitePlaceProduct v hv
        (adelicFinitePlaceEvaluation v (adelicFinitePlaceProduct v hv a.1 * a.2.val)))⁻¹ *
          (adelicFinitePlaceProduct v hv a.1 * a.2.val) = a.2.val
      rw [adelicFinitePlaceEvaluation_product_away, inv_mul_cancel_left]
  right_inv a := adelicFinitePlaceProduct_mul_removal v hv a
  map_mul' a b := by
    change adelicFinitePlaceProduct v hv (a.1 * b.1) * (a.2.val * b.2.val) =
      (adelicFinitePlaceProduct v hv a.1 * a.2.val) * (adelicFinitePlaceProduct v hv b.1 * b.2.val)
    rw [map_mul]
    have hc := adelicFinitePlaceProduct_away_commute v hv b.1 a.2
    calc
      _ = adelicFinitePlaceProduct v hv a.1 * (adelicFinitePlaceProduct v hv b.1 * a.2.val) * b.2.val := by
        simp only [mul_assoc]
      _ = adelicFinitePlaceProduct v hv a.1 * (a.2.val * adelicFinitePlaceProduct v hv b.1) * b.2.val := by rw [hc.eq]
      _ = _ := by simp only [mul_assoc]

/-- The genuine finite-family factorization multiplies exactly the original finite-place product and actual full complement. -/
theorem adelicFiniteFamilyEquiv_apply
    (g : ∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ))
    (a : adelicFiniteFamilyAwayGroup v) :
    adelicFiniteFamilyEquiv v hv (g, a) = adelicFinitePlaceProduct v hv g * a.val := rfl

end
end Dubon2026
