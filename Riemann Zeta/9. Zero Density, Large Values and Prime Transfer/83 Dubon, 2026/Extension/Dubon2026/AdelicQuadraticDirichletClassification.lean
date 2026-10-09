import Dubon2026.AdelicQuadraticCharacterRigidity
import Dubon2026.AdelicDirichletQuadratic
import Dubon2026.IntegralIdeleDirichletDescent

/-! # Classification of genuine continuous quadratic rational idele-class characters by actual Dirichlet characters -/

namespace Dubon2026

noncomputable section
open NumberField IsDedekindDomain

/-- Every actual continuous quadratic character of the original rational ideles, trivial on original principal rationals, is the constructed full idele character of a positive-modulus quadratic Dirichlet character. -/
theorem adelicQuadraticCharacter_dirichlet_exists (ψ : (AdeleRing ℤ ℚ)ˣ →* ℂ)
    (hc : Continuous ψ) (hq : ∀ a, ψ a ^ 2 = 1)
    (hp : ∀ q : ℚˣ, ψ (Units.map (algebraMap ℚ (AdeleRing ℤ ℚ)).toMonoidHom q) = 1) :
    ∃ D : ℕ+, ∃ χ : DirichletCharacter ℂ D, χ.IsQuadratic ∧ ψ = adelicDirichletCharacter χ := by
  let ψi : finiteAdeleIntegerSubringˣ →* ℂ := ψ.comp
    (rationalIdeleFiniteEmbedding.comp (Units.map finiteAdeleIntegerSubring.subtype.toMonoidHom))
  have hci : Continuous ψi := hc.comp (rationalIdeleFiniteEmbedding_continuous.comp
    (Continuous.units_map _ continuous_subtype_val))
  have hqi : ∀ u, ψi u ^ 2 = 1 := fun u => hq
    (rationalIdeleFiniteEmbedding (Units.map finiteAdeleIntegerSubring.subtype.toMonoidHom u))
  obtain ⟨D, hD, χ, hχ, hv⟩ := integralIdele_quadratic_dirichlet_exists ψi hci hqi
  letI : NeZero D := ⟨ne_of_gt hD⟩
  refine ⟨⟨D, hD⟩, χ, hχ, ?_⟩
  apply adelicQuadraticCharacter_eq_of_integral ψ (adelicDirichletCharacter χ) hq
    (adelicDirichletCharacter_quadratic χ hχ) hp (adelicDirichletCharacter_rational χ)
  intro u
  rw [adelicDirichletCharacter_integral, hv u]
  change ψi u = (ψi u)⁻¹
  rcases sq_eq_one_iff.mp (hqi u) with ho | hm
  · rw [ho, inv_one]
  · rw [hm, inv_neg, inv_one]

end
end Dubon2026
