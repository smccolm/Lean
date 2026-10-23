import Dubon2026.SourceResidueCoefficientAlgebra

/-! DUB-17/18 -> original Frobenius/inertia -> actual good/place reduction
-> coefficient specialization of the modular divisor field. Finite polynomial
relations are scaled so one coefficient is a unit and then reduced literally.
The all-level degree consumer will supply independence of powers of j_N,
so an integral Laurent member specializes into the residue modular field.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, coefficient specialization proof.
No specialization or independence premise is hidden in these constructions. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial

theorem exists_primitive_coefficient_scale {L : Type*} [Field L] (A : ValuationSubring L)
    (s : Finset (L)) (hs : ∃ x ∈ s, x ≠ 0) :
    ∃ a ∈ s, a ≠ 0 ∧ ∀ b ∈ s, a⁻¹ * b ∈ A := by
  classical
  set s' := s.filter (fun x => x ≠ 0) with hs'
  have hne : s'.Nonempty := by
    obtain ⟨x, hx, hx0⟩ := hs
    exact ⟨x, Finset.mem_filter.mpr ⟨hx, hx0⟩⟩
  obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image s' (fun x => A.valuation x) hne
  obtain ⟨has, ha0⟩ := Finset.mem_filter.mp ha
  refine ⟨a, has, ha0, fun b hb => ?_⟩
  by_cases hb0 : b = 0
  · simp [hb0]
  have hle : A.valuation b ≤ A.valuation a := hmax b (Finset.mem_filter.mpr ⟨hb, hb0⟩)
  rw [← A.valuation_le_one_iff, map_mul, map_inv₀]
  have hva : A.valuation a ≠ 0 := by
    intro h; exact ha0 ((Valuation.zero_iff _).mp h)
  calc (A.valuation a)⁻¹ * A.valuation b ≤ (A.valuation a)⁻¹ * A.valuation a :=
        mul_le_mul_right hle _
    _ = 1 := inv_mul_cancel₀ hva

end
end Dubon2026.SourceFunctionField
