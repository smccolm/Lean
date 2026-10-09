import Dubon2026.AdelicLocalFullAwayProduct
import Dubon2026.FinitePlaceLevelTopology

/-! # The genuine local/full-complement factorization preserves both original topologies -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

/-- Removal of one original finite coordinate is continuous in the genuine finite adelic topology. -/
theorem finiteAdelicPlaceRemoval_continuous (v : HeightOneSpectrum ℤ) :
    Continuous (finiteAdelicPlaceRemoval v) :=
  (((finiteAdelicLocalGL2_continuous v).comp
    (finiteAdelePlace_continuous v).generalLinearGroup_map).inv).mul continuous_id

/-- The genuine inverse local/full-complement factorization is continuous in the original full adelic topology. -/
theorem adelicLocalFullAwayEquiv_symm_continuous (v : HeightOneSpectrum ℤ) :
    Continuous (adelicLocalFullAwayEquiv v).symm := by
  change Continuous (fun a : RationalAdelicGL2 =>
    (GeneralLinearGroup.map (finiteAdelePlace v) (rationalAdelicGL2RealFiniteEquiv a).2,
      (rationalAdelicGL2RealFiniteEquiv a).1,
      (⟨finiteAdelicPlaceRemoval v (rationalAdelicGL2RealFiniteEquiv a).2,
        finiteAdelicPlaceRemoval_same v (rationalAdelicGL2RealFiniteEquiv a).2⟩ : finiteAdelicAwayGroup v)))
  have hc := continuous_snd.comp rationalAdelicGL2RealFiniteEquiv_continuous
  exact ((finiteAdelePlace_continuous v).generalLinearGroup_map.comp hc).prodMk
    ((continuous_fst.comp rationalAdelicGL2RealFiniteEquiv_continuous).prodMk
      (((finiteAdelicPlaceRemoval_continuous v).comp hc).subtype_mk _))

/-- The original full adelic group and its actual one-place/full-complement coordinates have exactly equivalent topologies. -/
def adelicLocalFullAwayHomeomorph (v : HeightOneSpectrum ℤ) :
    (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ) × AdelicFullAwayGroup v) ≃ₜ RationalAdelicGL2 where
  toEquiv := (adelicLocalFullAwayEquiv v).toEquiv
  continuous_toFun := adelicLocalFullAwayEquiv_continuous v
  continuous_invFun := adelicLocalFullAwayEquiv_symm_continuous v

/-- The genuine coordinate homeomorphism has exactly the original factorization map as its forward action. -/
theorem adelicLocalFullAwayHomeomorph_apply (v : HeightOneSpectrum ℤ)
    (a : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ) × AdelicFullAwayGroup v) :
    adelicLocalFullAwayHomeomorph v a = adelicLocalFullAwayEquiv v a := rfl

end
end Dubon2026
