import Dubon2026.AdelicLocalCoreIrreducible
import Dubon2026.IrreducibleRestriction

/-! # The actual irreducible smooth good-prime local representation on the original algebraic cusp orbit -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- Restriction of the original local action to its literal algebraic cyclic core. -/
def adelicLocalSmoothRepresentation (v : HeightOneSpectrum ℤ) :
    Representation ℂ (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)) (adelicLocalCyclicCore f v) :=
  Representation.subrepresentation (adelicCyclicLocalRepresentation f v) (adelicLocalCyclicCore f v)
    (fun g x hx => adelicLocalCyclicCore_invariant f v g x hx)

/-- The actual algebraic restriction acts by exactly the original local Hilbert action. -/
theorem adelicLocalSmoothRepresentation_apply (v : HeightOneSpectrum ℤ)
    (g : GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)) (x : adelicLocalCyclicCore f v) :
    (adelicLocalSmoothRepresentation f v g x).val = adelicCyclicLocalRepresentation f v g x.val := rfl

/-- Every vector of the actual local algebraic representation has a genuine open stabilizer. -/
theorem adelicLocalSmoothRepresentation_smooth (v : HeightOneSpectrum ℤ) (x : adelicLocalCyclicCore f v) :
    ∃ H : Subgroup (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)),
      IsOpen (H : Set (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))) ∧
        ∀ g ∈ H, adelicLocalSmoothRepresentation f v g x = x := by
  obtain ⟨H, hH, hx⟩ := adelicLocalCyclicCore_smooth f v x.val x.property
  exact ⟨H, hH, fun g hg => Subtype.ext (hx g hg)⟩

/-- The genuine local algebraic representation is nonzero for every original nonzero cusp form. -/
theorem adelicLocalCyclicCore_ne_bot (v : HeightOneSpectrum ℤ) (hf : f ≠ 0) :
    adelicLocalCyclicCore f v ≠ ⊥ := by
  intro he
  have hm := adelicLocalCyclicCore_generator_mem f v
  rw [he, Submodule.mem_bot] at hm
  exact adelicCyclicHilbertGenerator_ne_zero f hf hm

/-- The actual original primitive good-prime smooth representation is irreducible in Mathlib's genuine subrepresentation sense. -/
theorem adelicLocalSmoothRepresentation_irreducible {p : ℕ} [NeZero p] [Fact p.Prime]
    (F : PrimitiveCuspForm N k) (hpN : p.Coprime N) :
    (adelicLocalSmoothRepresentation F.toCuspForm (rationalPrimePlace p (Fact.out : p.Prime))).IsIrreducible :=
  @representation_restriction_irreducible
    (GeneralLinearGroup (Fin 2) ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ))
    (AdelicCyclicHilbert F.toCuspForm) inferInstance inferInstance inferInstance
    (adelicCyclicLocalRepresentation F.toCuspForm _) (adelicLocalCyclicCore F.toCuspForm _)
    (adelicLocalCyclicCore_invariant F.toCuspForm _)
    (adelicLocalCyclicCore_ne_bot F.toCuspForm _ (primitiveCuspForm_ne_zero F))
    (adelicLocalCyclicCore_irreducible F hpN)

end
end Dubon2026
