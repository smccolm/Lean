import Dubon2026.AdelicFiniteFamilyFactorization

/-! # Actual real coordinates of genuine finite-place products and their remainders -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

/-- The original real coordinate together with all genuine finite coordinates separates full adelic GL2. -/
theorem adelicRealFiniteCoordinates_ext {a b : RationalAdelicGL2}
    (hReal : (rationalAdelicGL2RealFiniteEquiv a).1 = (rationalAdelicGL2RealFiniteEquiv b).1)
    (hFinite : ∀ v, adelicPlaceGL2Hom v a = adelicPlaceGL2Hom v b) : a = b := by
  apply rationalAdelicGL2RealFiniteEquiv.injective
  apply Prod.ext hReal
  exact finiteAdelicGL2_ext hFinite

variable {I : Type*} [Fintype I] (v : I → HeightOneSpectrum ℤ) (hv : Function.Injective v)

/-- Every genuine finite-place product has exactly identity in the original real coordinate. -/
theorem adelicFinitePlaceProduct_real
    (g : ∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) :
    (rationalAdelicGL2RealFiniteEquiv (adelicFinitePlaceProduct v hv g)).1 = 1 := by
  classical
  let π : RationalAdelicGL2 →* GeneralLinearGroup (Fin 2) ℝ :=
    (MonoidHom.fst (GeneralLinearGroup (Fin 2) ℝ) (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ))).comp
      rationalAdelicGL2RealFiniteEquiv.toMonoidHom
  have he : π.comp (adelicFinitePlaceProduct v hv) = 1 := by
    apply MonoidHom.pi_ext
    intro i a
    change (rationalAdelicGL2RealFiniteEquiv (adelicFinitePlaceProduct v hv (Pi.mulSingle i a))).1 = 1
    rw [adelicFinitePlaceProduct_mulSingle, rationalAdelicFiniteGL2Embedding_coordinates]
  exact DFunLike.congr_fun he g

/-- Removing genuine finite-place coordinates leaves the original real coordinate unchanged. -/
theorem adelicFinitePlaceRemoval_real (a : RationalAdelicGL2) :
    (rationalAdelicGL2RealFiniteEquiv (adelicFinitePlaceRemoval v hv a)).1 =
      (rationalAdelicGL2RealFiniteEquiv a).1 := by
  change (rationalAdelicGL2RealFiniteEquiv
    ((adelicFinitePlaceProduct v hv (fun i => adelicPlaceGL2Hom (v i) a))⁻¹ * a)).1 = _
  simp only [map_mul, map_inv, Prod.fst_mul, Prod.fst_inv, adelicFinitePlaceProduct_real, inv_one, one_mul]

end
end Dubon2026
