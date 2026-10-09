import Dubon2026.AdelicLevelProjectionCore

/-! # The genuine level projector preserves the original finite-adelic algebraic orbit span -/

namespace Dubon2026

noncomputable section
open Matrix Matrix.SpecialLinearGroup IsDedekindDomain UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- The original algebraic finite-adelic orbit span, before taking its already identified Hilbert closure. -/
def adelicFiniteCyclicSpan : Submodule ℂ (AdelicCyclicHilbert f) :=
  Submodule.span ℂ (Set.range (fun a : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ) =>
    adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding a)
      (adelicCyclicHilbertGenerator f)))

/-- Its genuine original Hilbert closure is precisely the already constructed finite-adelic cyclic closure. -/
theorem adelicFiniteCyclicSpan_closure :
    (adelicFiniteCyclicSpan f).topologicalClosure = adelicFiniteCyclicClosedSpan f := rfl

/-- The actual algebraic finite-adelic span is invariant under every original finite-place operator. -/
theorem adelicFiniteCyclicSpan_invariant
    (a : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) (v : AdelicCyclicHilbert f)
    (hv : v ∈ adelicFiniteCyclicSpan f) :
    adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding a) v ∈ adelicFiniteCyclicSpan f :=
  @representationOrbitSpan_invariant (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) ℂ (AdelicCyclicHilbert f)
    inferInstance inferInstance inferInstance inferInstance
    ((adelicCyclicHilbertRepresentation f).comp rationalAdelicFiniteGL2Embedding)
    (adelicCyclicHilbertGenerator f) a v hv

/-- The genuine level projection of each original finite-adelic generator translate is still a finite original adelic combination. -/
theorem adelicLevelProjection_finiteOrbit
    (a : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) :
    adelicLevelProjection f
      (adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding a) (adelicCyclicHilbertGenerator f)) ∈
        adelicFiniteCyclicSpan f := by
  let v := (adelicLiftCyclicRepresentation N k f).toRepresentation
    (rationalAdelicFiniteGL2Embedding a) (adelicCyclicGenerator N f)
  have he : adelicCyclicHilbertEmbedding f v =
      adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding a) (adelicCyclicHilbertGenerator f) :=
    (adelicCyclicHilbertEmbedding_intertwines f (rationalAdelicFiniteGL2Embedding a)
      (adelicCyclicGenerator N f)).symm
  have hv : adelicCyclicHilbertEmbedding f v ∈ adelicFiniteCyclicSpan f := by
    rw [he]
    exact Submodule.subset_span ⟨a, rfl⟩
  have hs : Submodule.span ℂ (Set.range (fun b : finiteAdeleGL2Gamma0 N =>
      adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding b.val)
        (adelicCyclicHilbertEmbedding f v))) ≤ adelicFiniteCyclicSpan f := by
    apply Submodule.span_le.mpr
    rintro _ ⟨b, rfl⟩
    exact adelicFiniteCyclicSpan_invariant f b.val _ hv
  rw [← he]
  exact hs (adelicLevelProjection_core_orbit f v)

/-- The actual finite-level projector preserves the entire original algebraic finite-adelic cyclic span. -/
theorem adelicLevelProjection_finiteSpan (v : AdelicCyclicHilbert f) (hv : v ∈ adelicFiniteCyclicSpan f) :
    adelicLevelProjection f v ∈ adelicFiniteCyclicSpan f := by
  change v ∈ Submodule.span ℂ (Set.range (fun a : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ) =>
    adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding a)
      (adelicCyclicHilbertGenerator f))) at hv
  have hs : Submodule.span ℂ (Set.range (fun a : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ) =>
      adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding a)
        (adelicCyclicHilbertGenerator f))) ≤
      (adelicFiniteCyclicSpan f).comap (adelicLevelProjection f).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    exact adelicLevelProjection_finiteOrbit f a
  exact hs hv

end
end Dubon2026
