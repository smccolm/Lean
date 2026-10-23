import Dubon2026.SourceResidueAllLevelInduction

/-! DUB-17/18 -> original Frobenius/inertia -> actual modular-curve good
reduction -> residue degree. The joint induction gives the degree of the
literal internal j coordinate, the j_N minimal polynomial, and its expanded
primitive-slot factorization at every level away from the coefficient
characteristic. Genus preservation and good reduction are separate obligations. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial IntermediateField ConjugateSlots SourceLevelProjective
open scoped IntermediateField
variable {K : Type*} [Field K] [IsAlgClosed K]

theorem finrank_coeff_over_j_eq_psi (N : ℕ) [NeZero N] (hNK : (N : K) ≠ 0) :
    Module.finrank (IntermediateField.adjoin K
      ({jCoeff N K} : Set (modularFunctionFieldCoeff N K)))
        (modularFunctionFieldCoeff N K) = dedekindPsi N := by
  rw [coefficient_field_finrank_over_j_eq_relfinrank]
  exact (residue_full_generation_and_degree N hNK).2

theorem residue_j_minpoly_natDegree_eq_psi (N : ℕ) [NeZero N] (hNK : (N : K) ≠ 0) :
    (minpoly K⟮jqModC K⟯ (qExpand K N (jqModC K))).natDegree = dedekindPsi N := by
  obtain ⟨hgen, hdeg⟩ := residue_full_generation_and_degree N hNK
  rw [residue_minpoly_degree_eq_full_relfinrank_of_generation K N hgen]
  exact hdeg

theorem residueExpandedJMinpoly_eq_slotProduct (N : ℕ) [NeZero N] (hNK : (N : K) ≠ 0)
    (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) N) :
    residueExpandedJMinpoly K N N = slotProduct N ζ := by
  apply residueExpandedJMinpoly_eq_slotProduct_of_divisor_induction N ζ hζ
  intro d hd _
  exact residue_full_generation_and_degree d (ne_zero_of_dvd_ne_zero hNK hd.natCast)

end
end Dubon2026.SourceFunctionField
