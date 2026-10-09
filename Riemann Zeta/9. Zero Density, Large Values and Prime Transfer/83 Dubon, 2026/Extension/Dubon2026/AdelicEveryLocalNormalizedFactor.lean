import Dubon2026.AdelicEveryLocalMixedCoefficient
import Dubon2026.AdelicNormalizedCoefficientFactor

/-! # Exact original normalized coefficient factorization at all genuine finite places -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

variable {N : ℕ} [NeZero N] {k : ℤ} (F : PrimitiveCuspForm N k) (hk : 0 < k)

include hk

/-- At every actual finite place, the original local and full complementary normalized cusp coefficients multiply exactly. -/
theorem adelicNormalizedCuspCoefficient_everyLocal_fullAway (v : HeightOneSpectrum ℤ)
    (g : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)) (a : AdelicFullAwayGroup v) :
    adelicNormalizedCuspCoefficient F.toCuspForm
      (rationalAdelicFiniteGL2Embedding (finiteAdelicLocalGL2 v g) * adelicFullAwayEmbedding v a) =
      adelicNormalizedCuspCoefficient F.toCuspForm (rationalAdelicFiniteGL2Embedding (finiteAdelicLocalGL2 v g)) *
        adelicNormalizedCuspCoefficient F.toCuspForm (adelicFullAwayEmbedding v a) :=
  (@representationNormalizedCoefficient_mul_iff RationalAdelicGL2 (AdelicCyclicHilbert F.toCuspForm)
    inferInstance inferInstance inferInstance (adelicCyclicHilbertRepresentation F.toCuspForm)
    (adelicCyclicHilbertGenerator F.toCuspForm)
    (adelicCyclicHilbertGenerator_ne_zero F.toCuspForm (primitiveCuspForm_ne_zero F)) _ _).mpr
    (adelicEveryLocal_fullAway_coefficient_factor F hk v g a)

/-- Every original complementary matrix with identity at an arbitrary genuine finite place factors against that place in the actual normalized cusp coefficient. -/
theorem adelicNormalizedCuspCoefficient_everyLocal_mul (v : HeightOneSpectrum ℤ)
    (g : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))
    (a : RationalAdelicGL2) (ha : adelicPlaceGL2Hom v a = 1) :
    adelicNormalizedCuspCoefficient F.toCuspForm (rationalAdelicFiniteGL2Embedding (finiteAdelicLocalGL2 v g) * a) =
      adelicNormalizedCuspCoefficient F.toCuspForm (rationalAdelicFiniteGL2Embedding (finiteAdelicLocalGL2 v g)) *
        adelicNormalizedCuspCoefficient F.toCuspForm a := by
  obtain ⟨b, rfl⟩ := adelicFullAwayEmbedding_of_place_one v a ha
  exact adelicNormalizedCuspCoefficient_everyLocal_fullAway F hk v g b

end
end Dubon2026
