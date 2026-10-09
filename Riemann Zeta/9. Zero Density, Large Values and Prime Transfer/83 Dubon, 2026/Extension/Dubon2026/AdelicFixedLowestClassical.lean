import Dubon2026.AdelicFixedCoreFiniteDimension
import Dubon2026.AdelicFixedLowestDensity

/-! # Full original lowest-weight fixed-level Hilbert vectors are genuine classical cusp lifts -/

namespace Dubon2026

noncomputable section
open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- Finite dimensionality makes the genuine fixed-level finite-adelic core closed in the original Hilbert norm. -/
theorem adelicFixedFiniteSpan_isClosed :
    IsClosed ((adelicFiniteCyclicSpan f ⊓ adelicLevelFixedSpace f : Submodule ℂ (AdelicCyclicHilbert f)) :
      Set (AdelicCyclicHilbert f)) :=
  Submodule.closed_of_finiteDimensional _

/-- The entire original lowest-weight fixed-level Hilbert space equals its actual algebraic finite-adelic core. -/
theorem adelicFixedLowest_eq_algebraic (hf : f ≠ 0) (hk : 0 < k) :
    adelicRotationWeightSpace f ⊓ adelicLevelFixedSpace f =
      adelicFiniteCyclicSpan f ⊓ adelicLevelFixedSpace f := by
  rw [← adelicFixedLowest_algebraic_density f hf hk]
  exact (adelicFixedFiniteSpan_isClosed f).submodule_topologicalClosure_eq

/-- The full lowest-weight fixed-level subspace of the original adelic Hilbert completion is genuinely finite dimensional. -/
theorem adelicFixedLowest_finiteDimensional (hf : f ≠ 0) (hk : 0 < k) :
    FiniteDimensional ℂ ↥(adelicRotationWeightSpace f ⊓ adelicLevelFixedSpace f :
      Submodule ℂ (AdelicCyclicHilbert f)) := by
  rw [adelicFixedLowest_eq_algebraic f hf hk]
  infer_instance

/-- Every original lowest-weight fixed-level Hilbert vector is the faithful image of an actual adelic function equal everywhere to a unique genuine original-level classical cusp lift. -/
theorem adelicFixedLowest_classical_reconstruction (hf : f ≠ 0) (hk : 0 < k)
    (v : AdelicCyclicHilbert f) (hv : v ∈ adelicRotationWeightSpace f)
    (hlevel : v ∈ adelicLevelFixedSpace f) :
    ∃ w ∈ adelicAlgebraicFiniteSpan f, adelicCyclicHilbertEmbedding f w = v ∧
      ∃! F : CuspForm ((Gamma0 N).map (mapGL ℝ)) k,
        w.val = canonicalAdelicGL2CuspLift N k F := by
  have hc : v ∈ adelicRotationWeightSpace f ⊓ adelicLevelFixedSpace f := ⟨hv, hlevel⟩
  rw [adelicFixedLowest_eq_algebraic f hf hk] at hc
  obtain ⟨w, hw, he⟩ := adelicFiniteCyclicSpan_preimage f v hc.1
  have hl : adelicCyclicHilbertEmbedding f w ∈ adelicLevelFixedSpace f := he ▸ hlevel
  exact ⟨w, hw, he, adelicAlgebraicFiniteSpan_classical_full f w hw hl⟩

end
end Dubon2026
