import Dubon2026.FiniteAdelicLocalAwayProduct
import Dubon2026.AdelicRealFiniteCommute

/-! # Genuine local-place and full complementary coordinates of original adelic GL2 -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

/-- The actual complementary coordinates consist of the original real group and all original finite coordinates away from one specified place. -/
abbrev AdelicFullAwayGroup (v : HeightOneSpectrum ℤ) :=
  GeneralLinearGroup (Fin 2) ℝ × finiteAdelicAwayGroup v

/-- Reordering genuine group coordinates preserves their literal multiplication. -/
def groupProductSwapFirst {G H K : Type*} [Group G] [Group H] [Group K] :
    (G × (H × K)) ≃* (H × (G × K)) where
  toFun a := (a.2.1, a.1, a.2.2)
  invFun a := (a.2.1, a.1, a.2.2)
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The original full adelic group is the genuine product of a local place and the real-plus-away complement. -/
def adelicLocalFullAwayEquiv (v : HeightOneSpectrum ℤ) :
    (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ) × AdelicFullAwayGroup v) ≃* RationalAdelicGL2 :=
  groupProductSwapFirst.trans
    (((MulEquiv.refl (GeneralLinearGroup (Fin 2) ℝ)).prodCongr (finiteAdelicLocalAwayEquiv v)).trans
      rationalAdelicGL2RealFiniteEquiv.symm)

/-- The full genuine factorization has exactly its original real and finite coordinates. -/
theorem adelicLocalFullAwayEquiv_coordinates (v : HeightOneSpectrum ℤ)
    (g : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)) (a : AdelicFullAwayGroup v) :
    rationalAdelicGL2RealFiniteEquiv (adelicLocalFullAwayEquiv v (g, a)) =
      (a.1, finiteAdelicLocalGL2 v g * a.2.val) :=
  rationalAdelicGL2RealFiniteEquiv.apply_symm_apply _

/-- The true full complementary subgroup is inserted with identity at the original local place. -/
def adelicFullAwayEmbedding (v : HeightOneSpectrum ℤ) : AdelicFullAwayGroup v →* RationalAdelicGL2 :=
  (adelicLocalFullAwayEquiv v).toMonoidHom.comp
    ((1 : AdelicFullAwayGroup v →* GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)).prod
      (MonoidHom.id _))

/-- The original full complement embedding has the literal real and away finite coordinates. -/
theorem adelicFullAwayEmbedding_coordinates (v : HeightOneSpectrum ℤ) (a : AdelicFullAwayGroup v) :
    rationalAdelicGL2RealFiniteEquiv (adelicFullAwayEmbedding v a) = (a.1, a.2.val) := by
  change rationalAdelicGL2RealFiniteEquiv (adelicLocalFullAwayEquiv v (1, a)) = _
  rw [adelicLocalFullAwayEquiv_coordinates, finiteAdelicLocalGL2_one, one_mul]

/-- The genuine full factorization inserts exactly the original one-place matrix and the actual full complementary matrix. -/
theorem adelicLocalFullAwayEquiv_factor (v : HeightOneSpectrum ℤ)
    (g : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)) (a : AdelicFullAwayGroup v) :
    adelicLocalFullAwayEquiv v (g, a) =
      rationalAdelicFiniteGL2Embedding (finiteAdelicLocalGL2 v g) * adelicFullAwayEmbedding v a := by
  apply rationalAdelicGL2RealFiniteEquiv.injective
  rw [adelicLocalFullAwayEquiv_coordinates, map_mul,
    rationalAdelicFiniteGL2Embedding_coordinates, adelicFullAwayEmbedding_coordinates]
  simp only [Prod.mk_mul_mk, one_mul]

/-- The original local-place insertion commutes with every genuine full complementary group element. -/
theorem adelicLocal_fullAway_commute (v : HeightOneSpectrum ℤ)
    (g : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)) (a : AdelicFullAwayGroup v) :
    Commute (rationalAdelicFiniteGL2Embedding (finiteAdelicLocalGL2 v g)) (adelicFullAwayEmbedding v a) := by
  apply rationalAdelicGL2RealFiniteEquiv.injective
  simp only [map_mul, rationalAdelicFiniteGL2Embedding_coordinates,
    adelicFullAwayEmbedding_coordinates, Prod.mk_mul_mk, one_mul, mul_one]
  exact Prod.ext rfl (finiteAdelicLocalGL2_commute_of_place_one v a.2.val a.2.property g).eq.symm

/-- The genuine original local/full-complement group factorization is continuous for the inherited local and restricted-product topologies. -/
theorem adelicLocalFullAwayEquiv_continuous (v : HeightOneSpectrum ℤ) :
    Continuous (adelicLocalFullAwayEquiv v) := by
  change Continuous (fun a : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ) × AdelicFullAwayGroup v =>
    rationalAdelicGL2RealFiniteEquiv.symm (a.2.1, finiteAdelicLocalGL2 v a.1 * a.2.2.val))
  exact rationalAdelicGL2RealFiniteEquiv_symm_continuous.comp
    ((continuous_fst.comp continuous_snd).prodMk
      (((finiteAdelicLocalGL2_continuous v).comp continuous_fst).mul
        (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))))

end
end Dubon2026
