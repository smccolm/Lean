import Dubon2026.AdelicRealFiniteCoefficient
import Dubon2026.AdelicFiniteFamilyFactorization
import Dubon2026.AdelicFiniteProductRealCoordinate

/-! # The genuine real factor in actual selected finite-place coordinates -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

/-- Every actual finite place sees the identity in the genuine original real embedding. -/
theorem adelicPlaceGL2Hom_real (v : HeightOneSpectrum ℤ) (g : GeneralLinearGroup (Fin 2) ℝ) :
    adelicPlaceGL2Hom v (adelicRealGL2Embedding g) = 1 := by
  rw [adelicPlaceGL2Hom_apply, adelicRealGL2Embedding_coordinates]
  exact map_one (GeneralLinearGroup.map (finiteAdelePlace v))

/-- The original full real group is included in every genuine selected finite-place complement. -/
def adelicRealToFiniteAway {I : Type*} (v : I → HeightOneSpectrum ℤ) :
    GeneralLinearGroup (Fin 2) ℝ →* adelicFiniteFamilyAwayGroup v :=
  adelicRealGL2Embedding.codRestrict (adelicFiniteFamilyAwayGroup v)
    (fun g => funext (fun i => adelicPlaceGL2Hom_real (v i) g))

/-- The true real inclusion in any selected-place complement retains the identical original adelic matrix. -/
theorem adelicRealToFiniteAway_val {I : Type*} (v : I → HeightOneSpectrum ℤ)
    (g : GeneralLinearGroup (Fin 2) ℝ) : (adelicRealToFiniteAway v g).val = adelicRealGL2Embedding g := rfl

/-- Joint genuine selected finite and real coordinates give an original adelic group homomorphism. -/
def adelicFiniteRealJointHom {I : Type*} [Fintype I] (v : I → HeightOneSpectrum ℤ) (hv : Function.Injective v) :
    ((∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) × GeneralLinearGroup (Fin 2) ℝ) →* RationalAdelicGL2 :=
  (adelicFiniteFamilyEquiv v hv).toMonoidHom.comp ((MonoidHom.id _).prodMap (adelicRealToFiniteAway v))

/-- The genuine joint homomorphism multiplies the actual selected finite product and original real embedding. -/
theorem adelicFiniteRealJointHom_apply {I : Type*} [Fintype I] (v : I → HeightOneSpectrum ℤ)
    (hv : Function.Injective v)
    (a : (∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) × GeneralLinearGroup (Fin 2) ℝ) :
    adelicFiniteRealJointHom v hv a = adelicFinitePlaceProduct v hv a.1 * adelicRealGL2Embedding a.2 := rfl

end
end Dubon2026
