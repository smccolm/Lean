import Dubon2026.AdelicNormalizedHecke
import Dubon2026.AdelicRealCyclicClosure
import Dubon2026.ContinuousCyclicScalar

/-! # Actual normalized finite Hecke eigenvalues on the entire original real cyclic component -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

/-- The genuine finite Hecke trace commutes with every original real group operator. -/
theorem adelicHilbertHeckeTrace_real_commute {N p : ℕ} [NeZero N] [NeZero p] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (hpN : p.Coprime N)
    (g : SL(2, ℝ)) (v : AdelicCyclicHilbert f) :
    adelicHilbertHeckeTrace f p hpN
      (adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding g) v) =
    adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding g)
      (adelicHilbertHeckeTrace f p hpN v) := by
  exact (finiteAdelicHeckeTrace_intertwiner
    ((adelicCyclicHilbertRepresentation f).comp rationalAdelicFiniteGL2Embedding) N p hpN
    (adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding g))
    (fun a w => adelicCyclicHilbert_real_finite_commute f g a w) v).symm

/-- The unitary normalization retains genuine commutation with every original real group element. -/
theorem adelicNormalizedHecke_real_commute {N p : ℕ} [NeZero N] [NeZero p] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (hpN : p.Coprime N)
    (g : SL(2, ℝ)) (v : AdelicCyclicHilbert f) :
    adelicNormalizedHecke f p hpN
      (adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding g) v) =
    adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding g)
      (adelicNormalizedHecke f p hpN v) := by
  simp only [adelicNormalizedHecke, ContinuousLinearMap.smul_apply,
    adelicBoundedHeckeTrace_apply, map_smul, adelicHilbertHeckeTrace_real_commute]

/-- Every vector of the genuine original real cyclic Hilbert component has the exact original primitive Fourier eigenvalue for the actual normalized finite-adelic Hecke operator. -/
theorem adelicNormalizedHecke_real_component {N p : ℕ} [NeZero N] [NeZero p]
    [Fact p.Prime] {k : ℤ} (f : PrimitiveCuspForm N k) (hpN : p.Coprime N)
    (v : AdelicCyclicHilbert f.toCuspForm) (hv : v ∈ adelicRealCyclicClosedSpan f.toCuspForm) :
    adelicNormalizedHecke f.toCuspForm p hpN v = normalizedCuspCoefficients f.toCuspForm p • v := by
  apply @continuousLinearMap_scalar_on_closedSpan (AdelicCyclicHilbert f.toCuspForm) SL(2, ℝ)
    inferInstance inferInstance (adelicNormalizedHecke f.toCuspForm p hpN)
    (normalizedCuspCoefficients f.toCuspForm p)
    (fun g => adelicCyclicHilbertRepresentation f.toCuspForm (adelicRealSL2Embedding g)
      (adelicCyclicHilbertGenerator f.toCuspForm))
  · intro g
    rw [adelicNormalizedHecke_real_commute, adelicNormalizedHecke_primitive_generator, map_smul]
  · exact hv

end
end Dubon2026
