import Dubon2026.SourceResidueCoprimeNonmembership

/-! DUB-17/18 -> original Frobenius/inertia -> good reduction -> exact
all-level residue degree -> coprime prime nonmembership. Adapt local SourceOriginalCoprimeInduction
to actual coefficient-field j series and divisor fields. Lower generation and
conjugate products are explicit induction inputs. Expansion-range preservation
forces each image of j_p to the distinguished branch; bounded polynomial
descent contradicts the already proved prime nonmembership in K(j).
The level and prime must remain nonzero in the coefficient field. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial IntermediateField SourceLevelProjective
open scoped IntermediateField
variable {K : Type*} [Field K] [IsAlgClosed K]

theorem prime_j_not_mem_residue_coprime_of_divisor_induction (M p : ℕ)
    [NeZero M] [Fact p.Prime] (hpM : ¬ p ∣ M) (hMK : (M : K) ≠ 0) (hpK : (p : K) ≠ 0)
    (hall : ∀ (d : ℕ), d ∣ M → ∀ [NeZero d],
      modularFunctionFieldCoeff d K = IntermediateField.adjoin K
        ({(jqModC K), qExpand K d (jqModC K)} : Set (LaurentSeries K)) ∧
      relfinrank K⟮(jqModC K)⟯ (modularFunctionFieldCoeff d K) = dedekindPsi d) :
    qExpand K p (jqModC K) ∉ modularFunctionFieldCoeff M K := by
  haveI : NeZero (M : K) := ⟨hMK⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K M
  have hu := hz.isUnit (NeZero.ne M)
  have hζ : IsPrimitiveRoot (hu.unit : K) M := by rw [hu.unit_spec]; exact hz
  have hproduct := residueExpandedJMinpoly_eq_slotProduct_of_divisor_induction M hu.unit hζ hall
  exact prime_j_not_mem_residue_coprime_of_conjugate_product M p hpM hpK hu.unit hζ
    (hall M dvd_rfl).1 hproduct

end
end Dubon2026.SourceFunctionField
