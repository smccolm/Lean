import Dubon2026.FiniteAdelicSublevel
import Dubon2026.AdelicLevelProjection

/-! # Actual Hilbert vectors fixed by a genuine subgroup of the original finite level group -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- Restrict the original finite level action to its actual sublevel. -/
def adelicFiniteSublevelRepresentation (L : Subgroup (finiteAdeleGL2Gamma0 N)) :
    Representation ℂ L (AdelicCyclicHilbert f) :=
  (adelicFiniteLevelRepresentation f).comp L.subtype

/-- The original Hilbert subspace fixed by the genuine finite sublevel. -/
def adelicSublevelFixedSpace (L : Subgroup (finiteAdeleGL2Gamma0 N)) :
    Submodule ℂ (AdelicCyclicHilbert f) :=
  Representation.invariants (adelicFiniteSublevelRepresentation f L)

/-- Actual sublevel invariance is exactly the original Hilbert fixed-vector equation. -/
theorem mem_adelicSublevelFixedSpace (L : Subgroup (finiteAdeleGL2Gamma0 N)) (x : AdelicCyclicHilbert f) :
    x ∈ adelicSublevelFixedSpace f L ↔ ∀ a : L,
      adelicCyclicHilbertRepresentation f (rationalAdelicFiniteGL2Embedding a.val.val) x = x := Iff.rfl

/-- The original sublevel fixed space is closed in the genuine full Hilbert topology. -/
theorem adelicSublevelFixedSpace_isClosed (L : Subgroup (finiteAdeleGL2Gamma0 N)) :
    IsClosed (adelicSublevelFixedSpace f L : Set (AdelicCyclicHilbert f)) :=
  @representation_invariants_isClosed L (AdelicCyclicHilbert f)
    inferInstance inferInstance inferInstance (adelicFiniteSublevelRepresentation f L)
    (fun a => adelicCyclicHilbertOperator f (rationalAdelicFiniteGL2Embedding a.val.val)) (fun _ _ => rfl)

/-- The actual closed sublevel fixed space is complete. -/
instance adelicSublevelFixedSpace_complete (L : Subgroup (finiteAdeleGL2Gamma0 N)) :
    CompleteSpace (adelicSublevelFixedSpace f L) :=
  (adelicSublevelFixedSpace_isClosed f L).isComplete.completeSpace_coe

/-- Passing to a smaller genuine sublevel preserves every original fixed vector. -/
theorem adelicSublevelFixedSpace_antitone {L M : Subgroup (finiteAdeleGL2Gamma0 N)} (h : L ≤ M) :
    adelicSublevelFixedSpace f M ≤ adelicSublevelFixedSpace f L := by
  intro x hx
  apply (mem_adelicSublevelFixedSpace f L x).mpr
  intro a
  exact (mem_adelicSublevelFixedSpace f M x).mp hx ⟨a.val, h a.property⟩

/-- Faithfulness of the original Hilbert embedding turns genuine sublevel fixed vectors into literal right invariance of their original adelic functions. -/
theorem adelicCyclic_sublevel_pointwise (L : Subgroup (finiteAdeleGL2Gamma0 N))
    (x : (adelicLiftCyclicRepresentation N k f).toSubmodule)
    (hx : adelicCyclicHilbertEmbedding f x ∈ adelicSublevelFixedSpace f L)
    (a : L) (g : RationalAdelicGL2) :
    x.val (g * rationalAdelicFiniteGL2Embedding a.val.val) = x.val g := by
  have h := (mem_adelicSublevelFixedSpace f L _).mp hx a
  rw [adelicCyclicHilbertEmbedding_intertwines] at h
  have he := adelicCyclicHilbertEmbedding_injective f h
  exact congrFun (congrArg Subtype.val he) g

end
end Dubon2026
