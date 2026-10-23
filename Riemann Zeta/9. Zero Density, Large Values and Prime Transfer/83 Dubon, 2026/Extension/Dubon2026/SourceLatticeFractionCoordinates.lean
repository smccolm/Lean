import Mathlib.Algebra.Module.Lattice

/-! DUB-17/18 -> continuous residual association -> integral coordinates
of the constructed full lattice. Reuse native extension of a lattice
basis to the fraction field and identify the actual coordinate maps.
This identity will transfer continuity from the existing field action. -/
namespace Dubon2026
noncomputable section
variable {S E V I : Type*} [CommRing S] [Field E] [Algebra S E] [IsFractionRing S E]
variable [AddCommGroup V] [Module S V] [Module E V] [IsScalarTower S E V]
variable (L : Submodule S V) [Submodule.IsLattice E L] (b : Module.Basis I S L)

theorem latticeBasis_fraction_repr (x : L) (i : I) :
    (b.extendOfIsLattice E).repr (x : V) i = algebraMap S E (b.repr x i) := by
  classical
  have h : (((b.extendOfIsLattice E).coord i).restrictScalars S).comp L.subtype =
      (Algebra.linearMap S E).comp (b.coord i) := by
    apply b.ext
    intro j
    change (b.extendOfIsLattice E).repr ((b j : L) : V) i =
      algebraMap S E (b.repr (b j) i)
    rw [← Module.Basis.extendOfIsLattice_apply]
    simp only [Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs <;> simp
  exact LinearMap.congr_fun h x

end
end Dubon2026
