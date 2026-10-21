import Dubon2026.SourceMixedPrimitiveVanishing
import Dubon2026.SourceWeightTwoPrimitiveCusps

/-! DUB-17/18 -> residual Galois association -> parabolic Hecke realization
-> period-pair injectivity. This consumer uses the original weight-two
cusp forms themselves and constructs their normalized primitives and
all-cusp limits from the existing Eichler series. The remaining mixed
invariance premise will be derived from the actual period-pair kernel.
-/
namespace Dubon2026
noncomputable section
open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups

/-- Mixed invariance of the constructed primitives forces the original
weight-two cusp form to vanish; holomorphy, derivative normalization and
every original cusp limit are derived from the actual forms. -/
theorem sourceWeightTwo_mixedPrimitive_injective
    (N : ℕ) [NeZero N]
    (f g : CuspForm ((Gamma0 N).map (mapGL ℝ)) 2)
    (hinv : ∀ γ : Gamma0 N, ∀ z : ℍ,
      sourceWeightTwoPrimitive ((Gamma0 N).map (mapGL ℝ)).strictWidthInfty f (γ.val • z) -
        sourceWeightTwoPrimitive ((Gamma0 N).map (mapGL ℝ)).strictWidthInfty g
          (J • (γ.val • z)) =
      sourceWeightTwoPrimitive ((Gamma0 N).map (mapGL ℝ)).strictWidthInfty f z -
        sourceWeightTwoPrimitive ((Gamma0 N).map (mapGL ℝ)).strictWidthInfty g (J • z)) :
    f = 0 := by
  apply DFunLike.ext
  intro z
  change f z = 0
  exact sourceMixedPrimitive_derivative_zero
    (sourceWeightTwoPrimitive_hasDerivAt f
      ((Gamma0 N).map (mapGL ℝ)).strictWidthInfty_pos
      ((Gamma0 N).map (mapGL ℝ)).strictWidthInfty_mem_strictPeriods)
    (sourceWeightTwoPrimitive_hasDerivAt g
      ((Gamma0 N).map (mapGL ℝ)).strictWidthInfty_pos
      ((Gamma0 N).map (mapGL ℝ)).strictWidthInfty_mem_strictPeriods)
    (sourceWeightTwoPrimitive_exists_cusp_limit f
      ((Gamma0 N).map (mapGL ℝ)).strictWidthInfty_pos
      ((Gamma0 N).map (mapGL ℝ)).strictWidthInfty_mem_strictPeriods)
    (sourceWeightTwoPrimitive_exists_cusp_limit g
      ((Gamma0 N).map (mapGL ℝ)).strictWidthInfty_pos
      ((Gamma0 N).map (mapGL ℝ)).strictWidthInfty_mem_strictPeriods) hinv z

end
end Dubon2026
