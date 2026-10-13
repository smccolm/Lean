import Dubon2026.CyclicCohomologyHerbrandMultiplicativity
import Mathlib.RepresentationTheory.Rep.Basic

/-! # The original stable-submodule quotient sequence

The literal subtype and quotient maps give the short exact sequence
needed to compare DUB-17's extended S-unit lattice with its constructed
finite-index permutation sublattice in the existing cohomology category.
-/

namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2
variable {R G : Type} [CommRing R] [Group G] (A : Rep R G) (W : Submodule R A)
  (hW : ∀ g, W ≤ W.comap (A.ρ g))

/-- The original stable-submodule inclusion and actual quotient projection. -/
def stableSubmoduleShortComplex : ShortComplex (Rep R G) where
  X₁ := A.subrepresentation W hW
  X₂ := A
  X₃ := A.quotient W hW
  f := A.subtype W hW
  g := A.mkQ W hW
  zero := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    exact (Submodule.Quotient.mk_eq_zero W).mpr x.property

/-- The actual original subtype and quotient sequence is short exact. -/
theorem stableSubmoduleShortComplex_shortExact :
    (stableSubmoduleShortComplex A W hW).ShortExact := by
  refine {
    exact := ?_
    mono_f := (Rep.mono_iff_injective _).mpr Subtype.val_injective
    epi_g := (Rep.epi_iff_surjective _).mpr W.mkQ_surjective }
  apply ((stableSubmoduleShortComplex A W hW).exact_map_iff_of_faithful
    (forget₂ (Rep R G) (ModuleCat R))).mp
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  exact W.range_subtype.trans W.ker_mkQ.symm

end
end Dubon2026
