import Dubon2026.AdelicSublevelFixedSpace
import Dubon2026.AdelicAlgebraicFiniteSpan

/-! # The actual sublevel projector preserves the original finite-adelic core -/

namespace Dubon2026

noncomputable section
open Matrix Matrix.SpecialLinearGroup IsDedekindDomain UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- The genuine orthogonal projector onto the original sublevel fixed space. -/
def adelicSublevelProjection (L : Subgroup (finiteAdeleGL2Gamma0 N)) :
    AdelicCyclicHilbert f →L[ℂ] AdelicCyclicHilbert f :=
  @Submodule.starProjection ℂ (AdelicCyclicHilbert f) inferInstance inferInstance inferInstance
    (adelicSublevelFixedSpace f L) inferInstance

/-- Compactness of a genuine open sublevel and original finite smoothness keep the actual fixed projector in each vector's finite sublevel orbit span. -/
theorem adelicSublevelProjection_core_orbit (L : Subgroup (finiteAdeleGL2Gamma0 N))
    (hL : IsOpen (L : Set (finiteAdeleGL2Gamma0 N)))
    (v : (adelicLiftCyclicRepresentation N k f).toSubmodule) :
    adelicSublevelProjection f L (adelicCyclicHilbertEmbedding f v) ∈
      Submodule.span ℂ (Set.range (fun a : L =>
        adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding a.val.val)
          (adelicCyclicHilbertEmbedding f v))) := by
  have hproj : @Submodule.HasOrthogonalProjection ℂ (AdelicCyclicHilbert f)
      inferInstance inferInstance inferInstance (adelicSublevelFixedSpace f L) := inferInstance
  letI : CompactSpace (finiteAdeleGL2Gamma0 N) :=
    isCompact_iff_compactSpace.mp (finiteAdeleGL2Gamma0_isCompact N)
  letI : CompactSpace L := isCompact_iff_compactSpace.mp (L.isClosed_of_isOpen hL).isCompact
  obtain ⟨K, _, hKo, hK⟩ := adelicCyclicHilbert_finite_smooth_core f v
  let H : Subgroup L := K.comap ((finiteAdeleGL2Gamma0 N).subtype.comp L.subtype)
  have hH : IsOpen (H : Set L) :=
    hKo.preimage (continuous_subtype_val.comp continuous_subtype_val)
  have hv : ∀ a ∈ H, adelicFiniteSublevelRepresentation f L a (adelicCyclicHilbertEmbedding f v) =
      adelicCyclicHilbertEmbedding f v := fun a ha => hK a.val.val ha
  exact @compactInvariantProjection_mem_orbitSpan L (AdelicCyclicHilbert f)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (adelicFiniteSublevelRepresentation f L)
    (fun a v w => adelicCyclicHilbertRepresentation_inner f (rationalAdelicFiniteGL2Embedding a.val.val) v w)
    hproj H hH (adelicCyclicHilbertEmbedding f v) hv

/-- The genuine sublevel projection preserves every original algebraic finite-adelic Hilbert combination. -/
theorem adelicSublevelProjection_finiteSpan (L : Subgroup (finiteAdeleGL2Gamma0 N))
    (hL : IsOpen (L : Set (finiteAdeleGL2Gamma0 N)))
    (v : AdelicCyclicHilbert f) (hv : v ∈ adelicFiniteCyclicSpan f) :
    adelicSublevelProjection f L v ∈ adelicFiniteCyclicSpan f := by
  obtain ⟨w, hw, he⟩ := adelicFiniteCyclicSpan_preimage f v hv
  have hs : Submodule.span ℂ (Set.range (fun a : L =>
      adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding a.val.val)
        (adelicCyclicHilbertEmbedding f w))) ≤ adelicFiniteCyclicSpan f := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    rw [he]
    exact adelicFiniteCyclicSpan_invariant f a.val.val v hv
  rw [← he]
  exact hs (adelicSublevelProjection_core_orbit f L hL w)

end
end Dubon2026
