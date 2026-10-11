import Dubon2026.ContinuousRepresentationCohomology
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90

/-! # Original continuous Hilbert 90 for finite-extension Galois unit coefficients -/

namespace Dubon2026
noncomputable section

variable {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  [TopologicalSpace Gal(L/K)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [IsTopologicalAddGroup (Rep.ofAlgebraAutOnUnits K L)]
  [@ContinuousSMul ℤ (Rep.ofAlgebraAutOnUnits K L)
    (Rep.ofAlgebraAutOnUnits K L).hV2.toSMul inferInstance inferInstance]
  (hA : Continuous (fun z : Gal(L/K) × Rep.ofAlgebraAutOnUnits K L =>
    (Rep.ofAlgebraAutOnUnits K L).ρ z.1 z.2))

/-- Pinned Hilbert 90 supplies an actual original coefficient witnessing each
original continuous one-cocycle as a continuous coboundary. No change of the
coefficient topology or assumption of trivial Galois action is made. -/
theorem continuousGaloisUnitCocycle_exists_coboundary
    (c : continuousRepresentationCocyclesOne (Rep.ofAlgebraAutOnUnits K L)) :
    ∃ v : Rep.ofAlgebraAutOnUnits K L,
      continuousRepresentationCoboundaryOne (Rep.ofAlgebraAutOnUnits K L) hA v = c := by
  have hz : groupCohomology.H1π (Rep.ofAlgebraAutOnUnits K L) c.val = 0 :=
    Subsingleton.elim _ _
  obtain ⟨v, hv⟩ := (groupCohomology.H1π_eq_zero_iff c.val).mp hz
  refine ⟨v, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact hv

/-- The same original continuous H1 vanishes for the actual finite-extension
automorphism action on units, by the actual Hilbert-90 coefficient witness. -/
theorem continuousGaloisUnitH1_eq_zero
    (x : ContinuousRepresentationH1 (Rep.ofAlgebraAutOnUnits K L) hA) : x = 0 := by
  induction x using Quotient.inductionOn' with
  | h c =>
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact continuousGaloisUnitCocycle_exists_coboundary hA c

end
end Dubon2026
