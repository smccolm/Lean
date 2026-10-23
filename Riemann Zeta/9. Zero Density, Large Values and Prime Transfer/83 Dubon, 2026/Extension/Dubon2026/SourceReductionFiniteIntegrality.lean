import Dubon2026.SourceReductionIntegralCoordinates

/-! DUB-17/18 -> original Frobenius/inertia -> good reduction -> genus
comparison -> preservation of pole bounds. Integral coordinate expansions
prove that the prolongation ring is finite over its intersection with the
rational coordinate field. Native finite-module integrality then replaces
the source's general valuation-refinement and uniqueness detour. The required
degree equality will be derived for the actual modular j coordinate. -/
namespace Dubon2026.SourceCurve.RegularProlongation
noncomputable section
open IsLocalRing
variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

theorem isIntegral_coordinate_intersection (R : RegularProlongation A F Fbar)
    (x : R.integers) (hx : Transcendental (ResidueField A) (R.residue x))
    (hfin : 0 < Module.finrank
      (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hdeg : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
      Module.finrank
        (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (f : R.integers) :
    IsIntegral ↥((IntermediateField.adjoin L ({(x : F)} : Set F)).toSubfield.toSubring ⊓
      R.integers.toSubring : Subring F) (f : F) := by
  classical
  haveI : FiniteDimensional
      (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar :=
    Module.finite_of_finrank_pos hfin
  haveI : FiniteDimensional (IntermediateField.adjoin L ({(x : F)} : Set F)) F :=
    Module.finite_of_finrank_pos (hdeg ▸ hfin)
  let yb := Module.finBasis
    (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar
  choose y hy using fun i => R.residue_surjective (yb i)
  have hyind : LinearIndependent
      (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar))
      (fun i => R.residue (y i)) := by
    have : (fun i => R.residue (y i)) = yb := funext hy
    rw [this]
    exact yb.linearIndependent
  let S : Subring F :=
    (IntermediateField.adjoin L ({(x : F)} : Set F)).toSubfield.toSubring ⊓ R.integers.toSubring
  let O : Subalgebra S F :=
    { R.integers.toSubring with algebraMap_mem' := fun c => c.2.2 }
  have hspan : O.toSubmodule = Submodule.span S (Set.range fun i => (y i : F)) := by
    apply le_antisymm
    · intro g hg
      obtain ⟨r, hr, hsum⟩ := exists_repr_mem_inf R x hx y hyind hdeg ⟨g, hg⟩
      change g = _ at hsum
      rw [hsum]
      refine Submodule.sum_mem _ fun i _ => ?_
      exact Submodule.smul_mem _ (⟨r i, (hr i).2, (hr i).1⟩ : S)
        (Submodule.subset_span ⟨i, rfl⟩)
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      exact (y i).2
  have hfg : O.toSubmodule.FG := by
    rw [hspan]
    exact Submodule.fg_span (Set.finite_range _)
  exact IsIntegral.of_mem_of_fg O hfg (f : F) f.2

end
end Dubon2026.SourceCurve.RegularProlongation
