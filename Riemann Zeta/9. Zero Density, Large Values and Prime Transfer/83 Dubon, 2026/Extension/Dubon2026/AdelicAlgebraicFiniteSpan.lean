import Dubon2026.AdelicLevelFiniteSpan

/-! # The faithful algebraic preimage of the original finite-adelic Hilbert span -/

namespace Dubon2026

noncomputable section
open Matrix Matrix.SpecialLinearGroup IsDedekindDomain UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- The finite-adelic orbit span in the original space of actual adelic functions. -/
def adelicAlgebraicFiniteSpan :
    Submodule ℂ (adelicLiftCyclicRepresentation N k f).toSubmodule :=
  Submodule.span ℂ (Set.range (fun a : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ) =>
    (adelicLiftCyclicRepresentation N k f).toRepresentation
      (rationalAdelicFiniteGL2Embedding a) (adelicCyclicGenerator N f)))

/-- The original faithful embedding identifies the actual algebraic finite-place span with its Hilbert-space version. -/
theorem adelicAlgebraicFiniteSpan_map :
    (adelicAlgebraicFiniteSpan f).map (adelicCyclicHilbertEmbedding f) = adelicFiniteCyclicSpan f := by
  unfold adelicAlgebraicFiniteSpan adelicFiniteCyclicSpan
  rw [Submodule.map_span, ← Set.range_comp]
  apply congrArg (fun h => Submodule.span ℂ (Set.range h))
  funext a
  exact (adelicCyclicHilbertEmbedding_intertwines f (rationalAdelicFiniteGL2Embedding a)
    (adelicCyclicGenerator N f)).symm

/-- Every actual finite-adelic Hilbert combination comes from an actual finite combination of original adelic functions. -/
theorem adelicFiniteCyclicSpan_preimage (v : AdelicCyclicHilbert f) (hv : v ∈ adelicFiniteCyclicSpan f) :
    ∃ w ∈ adelicAlgebraicFiniteSpan f, adelicCyclicHilbertEmbedding f w = v := by
  rw [← adelicAlgebraicFiniteSpan_map f] at hv
  exact hv

end
end Dubon2026
