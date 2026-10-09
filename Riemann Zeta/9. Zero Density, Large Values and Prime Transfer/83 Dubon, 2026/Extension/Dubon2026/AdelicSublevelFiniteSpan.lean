import Dubon2026.AdelicSublevelClassicalCusp
import Dubon2026.FixedCosetRepresentative

/-! # The actual finite-adelic algebraic core at genuine finite sublevels -/

namespace Dubon2026

noncomputable section
open Matrix Matrix.SpecialLinearGroup IsDedekindDomain UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- Every genuine finite-adelic translate preserves the literal original algebraic finite-adelic span. -/
theorem adelicAlgebraicFiniteSpan_invariant
    (a : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ))
    (v : (adelicLiftCyclicRepresentation N k f).toSubmodule)
    (hv : v ∈ adelicAlgebraicFiniteSpan f) :
    (adelicLiftCyclicRepresentation N k f).toRepresentation (rationalAdelicFiniteGL2Embedding a) v ∈
      adelicAlgebraicFiniteSpan f :=
  @representationOrbitSpan_invariant (GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) ℂ
    (adelicLiftCyclicRepresentation N k f).toSubmodule
    inferInstance inferInstance inferInstance inferInstance
    ((adelicLiftCyclicRepresentation N k f).toRepresentation.comp rationalAdelicFiniteGL2Embedding)
    (adelicCyclicGenerator N f) a v hv

/-- Original level matrices preserve the genuine fixed space of each normal sublevel. -/
theorem adelicSublevelFixedSpace_normal_invariant
    (L : Subgroup (finiteAdeleGL2Gamma0 N)) [L.Normal] (a : finiteAdeleGL2Gamma0 N)
    (v : AdelicCyclicHilbert f) (hv : v ∈ adelicSublevelFixedSpace f L) :
    adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding a.val) v ∈
      adelicSublevelFixedSpace f L :=
  Representation.le_comap_invariants (adelicFiniteLevelRepresentation f) L a hv

/-- The actual original algebraic finite-adelic vectors fixed by a prescribed genuine sublevel. -/
def adelicAlgebraicSublevelFiniteSpan (L : Subgroup (finiteAdeleGL2Gamma0 N)) :
    Submodule ℂ (adelicLiftCyclicRepresentation N k f).toSubmodule :=
  adelicAlgebraicFiniteSpan f ⊓ (adelicSublevelFixedSpace f L).comap (adelicCyclicHilbertEmbedding f)

/-- Every original finite-level translate of an actual normal-sublevel fixed finite vector remains in the same genuine core. -/
theorem adelicAlgebraicSublevelFiniteSpan_invariant
    (L : Subgroup (finiteAdeleGL2Gamma0 N)) [L.Normal] (a : finiteAdeleGL2Gamma0 N)
    (v : (adelicLiftCyclicRepresentation N k f).toSubmodule)
    (hv : v ∈ adelicAlgebraicSublevelFiniteSpan f L) :
    (adelicLiftCyclicRepresentation N k f).toRepresentation (rationalAdelicFiniteGL2Embedding a.val) v ∈
      adelicAlgebraicSublevelFiniteSpan f L := by
  refine ⟨adelicAlgebraicFiniteSpan_invariant f a.val v hv.1, ?_⟩
  change adelicCyclicHilbertEmbedding f
    ((adelicLiftCyclicRepresentation N k f).toRepresentation (rationalAdelicFiniteGL2Embedding a.val) v) ∈ adelicSublevelFixedSpace f L
  rw [← adelicCyclicHilbertEmbedding_intertwines]
  exact adelicSublevelFixedSpace_normal_invariant f L a _ hv.2

/-- Genuine coset representatives induce precisely the original finite-level translates on each actual sublevel-fixed algebraic vector. -/
theorem adelicAlgebraicSublevelFiniteSpan_coset_out
    (L : Subgroup (finiteAdeleGL2Gamma0 N))
    (v : adelicAlgebraicSublevelFiniteSpan f L) (a : finiteAdeleGL2Gamma0 N) :
    (adelicLiftCyclicRepresentation N k f).toRepresentation
      (rationalAdelicFiniteGL2Embedding (Quotient.out (QuotientGroup.mk a : (finiteAdeleGL2Gamma0 N) ⧸ L)).val) v.val =
    (adelicLiftCyclicRepresentation N k f).toRepresentation (rationalAdelicFiniteGL2Embedding a.val) v.val := by
  apply adelicCyclicHilbertEmbedding_injective f
  rw [← adelicCyclicHilbertEmbedding_intertwines, ← adelicCyclicHilbertEmbedding_intertwines]
  exact representation_fixed_coset_out (adelicFiniteLevelRepresentation f) L
    (adelicCyclicHilbertEmbedding f v.val)
    (fun l hl => (mem_adelicSublevelFixedSpace f L _).mp v.property.2 ⟨l, hl⟩) a

end
end Dubon2026
