import Mathlib.RingTheory.MvPowerSeries.PiTopology
import Mathlib.Topology.DenseEmbedding

/-! Uniqueness of the actual finite-quotient parameter comparison.
Polynomial density supplies the required equality of continuous
power-series maps without a new division or presentation argument. -/

namespace Dubon2026
open scoped MvPowerSeries.WithPiTopology

/-- Continuous algebra maps out of the common parameter ring are
equal when their values on the original variables agree. -/
theorem continuousPowerSeriesAlgHom_ext
    {O η A : Type*} [CommRing O] [TopologicalSpace O]
    [CommRing A] [Algebra O A] [TopologicalSpace A] [T2Space A]
    (f g : MvPowerSeries η O →ₐ[O] A)
    (hf : Continuous f) (hg : Continuous g)
    (hX : ∀ i, f (MvPowerSeries.X i) = g (MvPowerSeries.X i)) : f = g := by
  apply DFunLike.ext'
  apply MvPowerSeries.WithPiTopology.denseRange_toMvPowerSeries.equalizer hf hg
  funext p
  have h : f.comp (MvPolynomial.coeToMvPowerSeries.algHom O) =
      g.comp (MvPolynomial.coeToMvPowerSeries.algHom O) := by
    apply MvPolynomial.algHom_ext
    intro i
    simpa using hX i
  exact congrArg (fun e => e p) h

end Dubon2026
