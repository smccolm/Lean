import Dubon2026.AdelicLocalFullAwayProduct

/-! # Exact membership in the genuine full complementary group at an original finite place -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

/-- Evaluation at the genuine finite place on the original full adelic general-linear group. -/
def adelicPlaceGL2Hom (v : HeightOneSpectrum ℤ) :
    RationalAdelicGL2 →* GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ) :=
  (GeneralLinearGroup.map (finiteAdelePlace v)).comp
    ((MonoidHom.snd (GeneralLinearGroup (Fin 2) ℝ)
      (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ))).comp
        rationalAdelicGL2RealFiniteEquiv.toMonoidHom)

/-- Genuine full-adelic place evaluation is exactly evaluation of its original finite coordinate. -/
theorem adelicPlaceGL2Hom_apply (v : HeightOneSpectrum ℤ) (a : RationalAdelicGL2) :
    adelicPlaceGL2Hom v a = GeneralLinearGroup.map (finiteAdelePlace v)
      (rationalAdelicGL2RealFiniteEquiv a).2 := rfl

/-- Every genuine complementary element has identity at the removed original place. -/
theorem adelicPlaceGL2Hom_fullAway (v : HeightOneSpectrum ℤ) (a : AdelicFullAwayGroup v) :
    adelicPlaceGL2Hom v (adelicFullAwayEmbedding v a) = 1 := by
  rw [adelicPlaceGL2Hom_apply, adelicFullAwayEmbedding_coordinates]
  exact a.2.property

/-- Every original full adelic matrix with identity at one place is an actual element of the full real-plus-away complement. -/
theorem adelicFullAwayEmbedding_of_place_one (v : HeightOneSpectrum ℤ)
    (a : RationalAdelicGL2) (ha : adelicPlaceGL2Hom v a = 1) :
    ∃ b : AdelicFullAwayGroup v, adelicFullAwayEmbedding v b = a := by
  let b : AdelicFullAwayGroup v :=
    ((rationalAdelicGL2RealFiniteEquiv a).1, ⟨(rationalAdelicGL2RealFiniteEquiv a).2, ha⟩)
  refine ⟨b, ?_⟩
  apply rationalAdelicGL2RealFiniteEquiv.injective
  rw [adelicFullAwayEmbedding_coordinates]

/-- Original one-place insertion is literally unchanged by evaluating at the same genuine place. -/
theorem adelicPlaceGL2Hom_local_same (v : HeightOneSpectrum ℤ)
    (g : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)) :
    adelicPlaceGL2Hom v (rationalAdelicFiniteGL2Embedding (finiteAdelicLocalGL2 v g)) = g := by
  rw [adelicPlaceGL2Hom_apply, rationalAdelicFiniteGL2Embedding_coordinates]
  exact finiteAdelicLocalGL2_same v g

/-- Every distinct original place sees the identity in a genuine one-place insertion. -/
theorem adelicPlaceGL2Hom_local_ne (v w : HeightOneSpectrum ℤ) (h : v ≠ w)
    (g : GeneralLinearGroup (Fin 2) (w.adicCompletion ℚ)) :
    adelicPlaceGL2Hom v (rationalAdelicFiniteGL2Embedding (finiteAdelicLocalGL2 w g)) = 1 := by
  rw [adelicPlaceGL2Hom_apply, rationalAdelicFiniteGL2Embedding_coordinates]
  exact finiteAdelicLocalGL2_ne w v h g

end
end Dubon2026
