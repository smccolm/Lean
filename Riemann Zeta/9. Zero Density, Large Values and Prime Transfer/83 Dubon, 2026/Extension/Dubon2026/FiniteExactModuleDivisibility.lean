import Dubon2026.FiniteExactModuleCardinality
import Mathlib.GroupTheory.Coset.Card

/-! # Actual three-term exact module cardinal divisibility -/

namespace Dubon2026
noncomputable section

/-- In a genuine three-term exact sequence with injective first map,
finite outer modules make the original middle module finite, and its actual
order divides the product of the two original outer orders. -/
theorem finite_exact_three_module_card_dvd
    {R A B C : Type} [CommRing R]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C] [Finite A] [Finite C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) (hf : Function.Injective f)
    (hfg : f.range = g.ker) :
    Finite B ∧ Nat.card B ∣ Nat.card A * Nat.card C := by
  refine ⟨finite_exact_module_middle f g hfg, ?_⟩
  have hA : Nat.card g.ker = Nat.card A := by
    rw [← hfg]
    exact Nat.card_congr (LinearEquiv.ofInjective f hf).symm.toEquiv
  rw [linearMap_card_eq_kernel_mul_range g, hA]
  exact Nat.mul_dvd_mul_left _ g.range.toAddSubgroup.card_addSubgroup_dvd_card

end
end Dubon2026
