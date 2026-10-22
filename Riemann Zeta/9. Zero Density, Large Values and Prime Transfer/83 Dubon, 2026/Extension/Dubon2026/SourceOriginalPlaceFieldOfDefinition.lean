import Dubon2026.SourceOriginalFiniteFieldOfDefinition
import Dubon2026.SourceOriginalFinitePlaceOrbit

/-! DUB-17/18 -> continuous original modular torsion action -> finite
fields of definition of the actual original places. For each other place
in its finite arithmetic orbit, a function distinguishes the two literal
valuation rings. A finite compositum of the proved function fields of
definition excludes every such place. Thus its fixing subgroup fixes the
original place itself. This selects the finite-orbit argument from
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_JZero_isOpen_stabilizer, using original j-fiber finiteness
instead of a separate constant-field restriction theory.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve
local notation "Qbar" => AlgebraicClosure ℚ

theorem original_place_fieldOfDefinition (N : ℕ) [NeZero N]
    (v : Place Qbar (modularFunctionFieldOver N Qbar)) :
    ∃ E : IntermediateField ℚ Qbar, FiniteDimensional ℚ E ∧
      ∀ σ : Qbar ≃ₐ[ℚ] Qbar, σ ∈ E.fixingSubgroup → originalArithmeticPlace N σ v = v := by
  classical
  have key (w : Place Qbar (modularFunctionFieldOver N Qbar)) :
      ∃ E : IntermediateField ℚ Qbar, FiniteDimensional ℚ E ∧
        (w ≠ v → ∀ σ : Qbar ≃ₐ[ℚ] Qbar, σ ∈ E.fixingSubgroup → originalArithmeticPlace N σ v ≠ w) := by
    by_cases hw : w = v
    · subst w
      exact ⟨⊥, inferInstance, fun hn => (hn rfl).elim⟩
    · have hex : ∃ x : modularFunctionFieldOver N Qbar,
          ¬ (x ∈ v.toValuationSubring ↔ x ∈ w.toValuationSubring) := by
        by_contra h
        push Not at h
        exact hw (Place.ext (SetLike.ext h)).symm
      obtain ⟨x, hx⟩ := hex
      obtain ⟨E, hE, hfix⟩ := original_function_fieldOfDefinition N x
      refine ⟨E, hE, fun _ σ hσ heq => ?_⟩
      have hs : originalArithmeticRingAut N σ.symm x = x :=
        hfix σ.symm (E.fixingSubgroup.inv_mem hσ)
      have hm : x ∈ (originalArithmeticPlace N σ v).toValuationSubring ↔ x ∈ v.toValuationSubring := by
        change originalArithmeticRingAut N σ.symm x ∈ v.toValuationSubring ↔ x ∈ v.toValuationSubring
        rw [hs]
      rw [heq] at hm
      exact hx hm.symm
  choose E hE hsep using key
  letI : ∀ w, FiniteDimensional ℚ (E w) := hE
  let S := (original_place_galois_orbit_finite N v).toFinset
  refine ⟨⨆ w ∈ S, E w, IntermediateField.finiteDimensional_iSup_of_finset, fun σ hσ => ?_⟩
  by_contra hn
  have hm : originalArithmeticPlace N σ v ∈ S :=
    (original_place_galois_orbit_finite N v).mem_toFinset.mpr ⟨σ, rfl⟩
  have hle : E (originalArithmeticPlace N σ v) ≤ ⨆ w ∈ S, E w :=
    le_iSup₂_of_le _ hm le_rfl
  exact hsep (originalArithmeticPlace N σ v) hn σ (IntermediateField.fixingSubgroup_le hle hσ) rfl

end
end Dubon2026.SourceFunctionField
