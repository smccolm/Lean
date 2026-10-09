import Dubon2026.AdelicLocalCyclicCore
import Dubon2026.AdelicLocalFixedSpace
import Dubon2026.CompactInvariantProjection

/-! # Actual compact local fixed projection preserves the original algebraic orbit core -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- The genuine orthogonal projector onto the original local level-fixed Hilbert subspace. -/
def adelicLocalFixedProjection (v : HeightOneSpectrum ℤ) :
    AdelicCyclicHilbert f →L[ℂ] AdelicCyclicHilbert f :=
  @Submodule.starProjection ℂ (AdelicCyclicHilbert f) inferInstance inferInstance inferInstance
    (adelicLocalFixedSpace f v) inferInstance

/-- The original local fixed projector fixes the genuine cusp generator. -/
theorem adelicLocalFixedProjection_generator (v : HeightOneSpectrum ℤ) :
    adelicLocalFixedProjection f v (adelicCyclicHilbertGenerator f) = adelicCyclicHilbertGenerator f :=
  (@Submodule.starProjection_eq_self_iff ℂ (AdelicCyclicHilbert f)
    inferInstance inferInstance inferInstance (adelicLocalFixedSpace f v) inferInstance _).mpr
    (adelicCyclicHilbertGenerator_mem_localFixed f v)

/-- The actual local projection takes every original vector to the genuine level-fixed space. -/
theorem adelicLocalFixedProjection_mem (v : HeightOneSpectrum ℤ) (x : AdelicCyclicHilbert f) :
    adelicLocalFixedProjection f v x ∈ adelicLocalFixedSpace f v :=
  @Submodule.starProjection_apply_mem ℂ (AdelicCyclicHilbert f)
    inferInstance inferInstance inferInstance (adelicLocalFixedSpace f v) inferInstance x

/-- The actual local fixed projection preserves the original inner product with the cusp generator. -/
theorem adelicLocalFixedProjection_inner_generator (v : HeightOneSpectrum ℤ) (x : AdelicCyclicHilbert f) :
    inner ℂ (adelicLocalFixedProjection f v x) (adelicCyclicHilbertGenerator f) =
      inner ℂ x (adelicCyclicHilbertGenerator f) := by
  have he := @Submodule.inner_starProjection_left_eq_right ℂ (AdelicCyclicHilbert f)
    inferInstance inferInstance inferInstance (adelicLocalFixedSpace f v) inferInstance
    x (adelicCyclicHilbertGenerator f)
  change inner ℂ (adelicLocalFixedProjection f v x) (adelicCyclicHilbertGenerator f) =
    inner ℂ x (adelicLocalFixedProjection f v (adelicCyclicHilbertGenerator f)) at he
  simpa only [adelicLocalFixedProjection_generator] using he

/-- Projection of each genuine local algebraic core vector stays in its own finite original compact level-orbit span. -/
theorem adelicLocalFixedProjection_core_orbit (v : HeightOneSpectrum ℤ)
    (x : AdelicCyclicHilbert f) (hx : x ∈ adelicLocalCyclicCore f v) :
    adelicLocalFixedProjection f v x ∈ Submodule.span ℂ (Set.range
      (fun a : finitePlaceGL2Gamma0 N v => adelicCyclicLocalRepresentation f v a.val x)) := by
  have hproj : @Submodule.HasOrthogonalProjection ℂ (AdelicCyclicHilbert f)
      inferInstance inferInstance inferInstance (adelicLocalFixedSpace f v) := inferInstance
  letI : CompactSpace (finitePlaceGL2Gamma0 N v) :=
    isCompact_iff_compactSpace.mp (finitePlaceGL2Gamma0_isCompact N v)
  obtain ⟨K, hKo, hK⟩ := adelicLocalCyclicCore_smooth f v x hx
  let H := K.comap (finitePlaceGL2Gamma0 N v).subtype
  have hH : IsOpen (H : Set (finitePlaceGL2Gamma0 N v)) := hKo.preimage continuous_subtype_val
  exact @compactInvariantProjection_mem_orbitSpan (finitePlaceGL2Gamma0 N v) (AdelicCyclicHilbert f)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    ((adelicCyclicLocalRepresentation f v).comp (finitePlaceGL2Gamma0 N v).subtype)
    (fun g a b => adelicCyclicLocalRepresentation_inner f v g.val a b)
    hproj H hH x (fun g hg => hK g.val hg)

/-- Every actual algebraic invariant subspace of the original local core is preserved by the genuine compact local projection. -/
theorem adelicLocalFixedProjection_mem_invariantCore (v : HeightOneSpectrum ℤ)
    (W : Submodule ℂ (AdelicCyclicHilbert f)) (hW : W ≤ adelicLocalCyclicCore f v)
    (hinv : ∀ g x, x ∈ W → adelicCyclicLocalRepresentation f v g x ∈ W)
    (x : AdelicCyclicHilbert f) (hx : x ∈ W) : adelicLocalFixedProjection f v x ∈ W := by
  have hs : Submodule.span ℂ (Set.range
      (fun a : finitePlaceGL2Gamma0 N v => adelicCyclicLocalRepresentation f v a.val x)) ≤ W := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    exact hinv a.val x hx
  exact hs (adelicLocalFixedProjection_core_orbit f v x (hW hx))

end
end Dubon2026
