import Dubon2026.AdelicQuadraticDirichletClassification
import Dubon2026.DirichletPrimitiveAdelicCharacter

/-! # Classification of every nontrivial quadratic original idele-class character by a primitive Dirichlet character -/

namespace Dubon2026

noncomputable section
open NumberField

/-- Every genuine nontrivial continuous quadratic rational idele-class character comes from a genuine nontrivial primitive quadratic Dirichlet character of positive conductor. -/
theorem adelicQuadraticCharacter_primitive_exists (ψ : (AdeleRing ℤ ℚ)ˣ →* ℂ)
    (hc : Continuous ψ) (hq : ∀ a, ψ a ^ 2 = 1)
    (hp : ∀ q : ℚˣ, ψ (Units.map (algebraMap ℚ (AdeleRing ℤ ℚ)).toMonoidHom q) = 1)
    (hne : ψ ≠ 1) :
    ∃ D : ℕ+, ∃ χ : DirichletCharacter ℂ D,
      χ.IsPrimitive ∧ χ ≠ 1 ∧ χ.IsQuadratic ∧ ψ = adelicDirichletCharacter χ := by
  obtain ⟨D, χ, hχq, he⟩ := adelicQuadraticCharacter_dirichlet_exists ψ hc hq hp
  letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hep : ψ = adelicDirichletCharacter χ.primitiveCharacter :=
    he.trans (adelicDirichletCharacter_primitive χ hχq).symm
  refine ⟨⟨χ.conductor, Nat.pos_of_ne_zero χ.conductor_ne_zero⟩, χ.primitiveCharacter,
    χ.primitiveCharacter_isPrimitive, ?_, dirichlet_primitiveCharacter_quadratic χ hχq, hep⟩
  intro hz
  apply hne
  rw [hz] at hep
  exact hep.trans (adelicDirichletCharacter_one χ.conductor)

end
end Dubon2026
