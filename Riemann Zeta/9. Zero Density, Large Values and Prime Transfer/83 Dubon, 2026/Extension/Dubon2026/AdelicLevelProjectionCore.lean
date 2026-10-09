import Dubon2026.AdelicLevelProjection
import Dubon2026.CompactInvariantProjection

/-! # The actual finite-level projector preserves the genuine original algebraic cusp core -/

namespace Dubon2026

noncomputable section
open Matrix Matrix.SpecialLinearGroup IsDedekindDomain UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- For every actual original algebraic cusp vector, the genuine level projector stays in its own finite level-orbit span. -/
theorem adelicLevelProjection_core_orbit (v : (adelicLiftCyclicRepresentation N k f).toSubmodule) :
    adelicLevelProjection f (adelicCyclicHilbertEmbedding f v) ∈
      Submodule.span ℂ (Set.range (fun a : finiteAdeleGL2Gamma0 N =>
        adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding a.val)
          (adelicCyclicHilbertEmbedding f v))) := by
  have hproj : @Submodule.HasOrthogonalProjection ℂ (AdelicCyclicHilbert f)
      inferInstance inferInstance inferInstance (adelicLevelFixedSpace f) := inferInstance
  letI : CompactSpace (finiteAdeleGL2Gamma0 N) :=
    isCompact_iff_compactSpace.mp (finiteAdeleGL2Gamma0_isCompact N)
  obtain ⟨K, _, hKo, hK⟩ := adelicCyclicHilbert_finite_smooth_core f v
  let H : Subgroup (finiteAdeleGL2Gamma0 N) := K.comap (finiteAdeleGL2Gamma0 N).subtype
  have hH : IsOpen (H : Set (finiteAdeleGL2Gamma0 N)) := hKo.preimage continuous_subtype_val
  have hv : ∀ a ∈ H, adelicFiniteLevelRepresentation f a (adelicCyclicHilbertEmbedding f v) =
      adelicCyclicHilbertEmbedding f v := fun a ha => hK a.val ha
  exact @compactInvariantProjection_mem_orbitSpan (finiteAdeleGL2Gamma0 N) (AdelicCyclicHilbert f)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (adelicFiniteLevelRepresentation f)
    (fun a v w => adelicCyclicHilbertRepresentation_inner f (rationalAdelicFiniteGL2Embedding a.val) v w)
    hproj H hH (adelicCyclicHilbertEmbedding f v) hv

/-- The level projection of an actual original algebraic vector has a genuine original algebraic preimage. -/
theorem adelicLevelProjection_core (v : (adelicLiftCyclicRepresentation N k f).toSubmodule) :
    ∃ w : (adelicLiftCyclicRepresentation N k f).toSubmodule,
      adelicLevelProjection f (adelicCyclicHilbertEmbedding f v) = adelicCyclicHilbertEmbedding f w := by
  have hs : Submodule.span ℂ (Set.range (fun a : finiteAdeleGL2Gamma0 N =>
      adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding a.val)
        (adelicCyclicHilbertEmbedding f v))) ≤ (adelicCyclicHilbertEmbedding f).range := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    exact ⟨(adelicLiftCyclicRepresentation N k f).toRepresentation
      (rationalAdelicFiniteGL2Embedding a.val) v,
      (adelicCyclicHilbertEmbedding_intertwines f (rationalAdelicFiniteGL2Embedding a.val) v).symm⟩
  obtain ⟨w, hw⟩ := hs (adelicLevelProjection_core_orbit f v)
  exact ⟨w, hw.symm⟩

end
end Dubon2026
