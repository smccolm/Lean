import Mathlib.Algebra.Module.Lattice

/-! DUB-17/18 -> residual primitive realization -> rank of the actual
integer lattice. Reuse the native lattice freeness and rank theorems.
The application uses the coefficient valuation ring and its fraction field. -/
namespace Dubon2026
noncomputable section
variable {S E V : Type*} [CommRing S] [IsDomain S] [IsPrincipalIdealRing S]
variable [Field E] [Algebra S E] [IsFractionRing S E]
variable [AddCommGroup V] [Module S V] [Module E V] [IsScalarTower S E V]

theorem fullIntegralLattice_free_finite_rank (L : Submodule S V) (hL : L.FG)
    (hspan : Submodule.span E (L : Set V) = ⊤) :
    Module.Free S L ∧ Module.Finite S L ∧ Module.finrank S L = Module.finrank E V := by
  letI : Submodule.IsLattice E L := ⟨hL, hspan⟩
  exact ⟨inferInstance, inferInstance,
    congrArg Cardinal.toNat (Submodule.IsLattice.rank' E L)⟩

end
end Dubon2026
