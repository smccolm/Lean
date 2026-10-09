import Dubon2026.AdelicFiniteTupleCoefficients
import Dubon2026.AdelicLocalFullAwayTopology

/-! # The genuine finite-family adelic group factorization is a homeomorphism -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

/-- The original full-adelic insertion of one genuine local matrix is continuous. -/
theorem adelicSinglePlaceInsertion_continuous (v : HeightOneSpectrum ℤ) :
    Continuous (fun g => rationalAdelicFiniteGL2Embedding (finiteAdelicLocalGL2 v g)) := by
  apply ((adelicLocalFullAwayEquiv_continuous v).comp
    (continuous_id.prodMk (continuous_const : Continuous (fun _ : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ) =>
      (1 : AdelicFullAwayGroup v))))).congr
  intro g
  change adelicLocalFullAwayEquiv v (g, 1) = rationalAdelicFiniteGL2Embedding (finiteAdelicLocalGL2 v g)
  rw [adelicLocalFullAwayEquiv_factor, map_one, mul_one]

/-- Evaluation of any actual finite coordinate of the original full adelic group is continuous. -/
theorem adelicPlaceGL2Hom_continuous (v : HeightOneSpectrum ℤ) : Continuous (adelicPlaceGL2Hom v) :=
  (finiteAdelePlace_continuous v).generalLinearGroup_map.comp
    (continuous_snd.comp rationalAdelicGL2RealFiniteEquiv_continuous)

variable {I : Type*} [Fintype I] (v : I → HeightOneSpectrum ℤ) (hv : Function.Injective v)

/-- The actual finite product of distinct original local coordinates is continuous. -/
theorem adelicFinitePlaceProduct_continuous : Continuous (adelicFinitePlaceProduct v hv) := by
  classical
  apply (continuous_list_prod (Finset.univ : Finset I).toList
    (fun i _ => (adelicSinglePlaceInsertion_continuous (v i)).comp (continuous_apply i))).congr
  intro g
  exact (adelicFinitePlaceProduct_eq_list v hv g (Finset.univ : Finset I).toList
    (Finset.nodup_toList _) (Finset.toList_toFinset _)).symm

/-- Removing a finite family of actual local coordinates is continuous in the original full adelic topology. -/
theorem adelicFinitePlaceRemoval_continuous : Continuous (adelicFinitePlaceRemoval v hv) :=
  (((adelicFinitePlaceProduct_continuous v hv).comp
    (continuous_pi (fun i => adelicPlaceGL2Hom_continuous (v i)))).inv).mul continuous_id

/-- The actual finite-family/full-complement group product is continuous. -/
theorem adelicFiniteFamilyEquiv_continuous : Continuous (adelicFiniteFamilyEquiv v hv) :=
  ((adelicFinitePlaceProduct_continuous v hv).comp continuous_fst).mul
    (continuous_subtype_val.comp continuous_snd)

/-- The inverse original coordinate factorization is continuous for both genuine factors. -/
theorem adelicFiniteFamilyEquiv_symm_continuous : Continuous (adelicFiniteFamilyEquiv v hv).symm := by
  change Continuous (fun a : RationalAdelicGL2 =>
    ((fun i => adelicPlaceGL2Hom (v i) a),
      (⟨adelicFinitePlaceRemoval v hv a, funext (fun i => adelicFinitePlaceRemoval_same v hv i a)⟩ :
        adelicFiniteFamilyAwayGroup v)))
  exact (continuous_pi (fun i => adelicPlaceGL2Hom_continuous (v i))).prodMk
    ((adelicFinitePlaceRemoval_continuous v hv).subtype_mk _)

/-- The exact original finite-family adelic coordinates have the genuine product topology. -/
def adelicFiniteFamilyHomeomorph :
    ((∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) × adelicFiniteFamilyAwayGroup v) ≃ₜ
      RationalAdelicGL2 where
  toEquiv := (adelicFiniteFamilyEquiv v hv).toEquiv
  continuous_toFun := adelicFiniteFamilyEquiv_continuous v hv
  continuous_invFun := adelicFiniteFamilyEquiv_symm_continuous v hv

/-- The genuine finite-family homeomorphism retains the literal original group product map. -/
theorem adelicFiniteFamilyHomeomorph_apply
    (b : (∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) × adelicFiniteFamilyAwayGroup v) :
    adelicFiniteFamilyHomeomorph v hv b = adelicFiniteFamilyEquiv v hv b := rfl

end
end Dubon2026
