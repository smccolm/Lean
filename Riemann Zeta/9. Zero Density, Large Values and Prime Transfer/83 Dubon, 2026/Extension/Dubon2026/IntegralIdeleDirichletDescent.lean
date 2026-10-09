import Dubon2026.QuadraticCharacterCongruence
import Mathlib.NumberTheory.DirichletCharacter.Basic

/-! # Genuine Dirichlet character descent of continuous quadratic integral-idele characters -/

namespace Dubon2026

noncomputable section

variable (D : ℕ) [NeZero D] (ψ : finiteAdeleIntegerSubringˣ →* ℂ)
    (hker : ∀ u : finiteAdeleIntegerSubringˣ, finiteAdeleResidue D u.val = 1 → ψ u = 1)

/-- The original integral-idele character descends along the proved surjective original residue-unit map. -/
def integralIdeleResidueCharacter : (ZMod D)ˣ →* ℂˣ :=
  (Units.map (finiteAdeleResidue D).toMonoidHom).liftOfSurjective (finiteAdeleResidue_units_surjective D)
    ⟨ψ.toHomUnits, by
      intro u hu
      apply Units.ext
      apply hker u
      exact congrArg Units.val hu⟩

/-- The descended unit character agrees exactly with the original character on every original integral finite idele. -/
theorem integralIdeleResidueCharacter_apply (u : finiteAdeleIntegerSubringˣ) :
    integralIdeleResidueCharacter D ψ hker (Units.map (finiteAdeleResidue D).toMonoidHom u) =
      ψ.toHomUnits u := by
  unfold integralIdeleResidueCharacter
  exact MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _

/-- The actual Dirichlet character associated to the descended original residue-unit character. -/
def integralIdeleDirichletCharacter : DirichletCharacter ℂ D :=
  MulChar.ofUnitHom (integralIdeleResidueCharacter D ψ hker)

/-- Its literal original residue values are the original integral-idele character values. -/
theorem integralIdeleDirichletCharacter_apply (u : finiteAdeleIntegerSubringˣ) :
    integralIdeleDirichletCharacter D ψ hker (finiteAdeleResidue D u.val) = ψ u := by
  have h := congrArg Units.val (integralIdeleResidueCharacter_apply D ψ hker u)
  rw [← MulChar.ofUnitHom_coe] at h
  exact h

/-- Genuine quadratic values of the original integral-idele character give a genuine quadratic Dirichlet character. -/
theorem integralIdeleDirichletCharacter_quadratic (hq : ∀ u, ψ u ^ 2 = 1) :
    (integralIdeleDirichletCharacter D ψ hker).IsQuadratic := by
  intro x
  by_cases hx : IsUnit x
  · obtain ⟨u, hu⟩ := finiteAdeleResidue_units_surjective D hx.unit
    have hr : finiteAdeleResidue D u.val = x :=
      (congrArg Units.val hu).trans hx.unit_spec
    rw [← hr, integralIdeleDirichletCharacter_apply]
    exact Or.inr (sq_eq_one_iff.mp (hq u))
  · exact Or.inl ((integralIdeleDirichletCharacter D ψ hker).map_nonunit hx)

/-- Every actual continuous quadratic integral-idele character factors through a positive ordinary Dirichlet modulus, with its quadratic property proved. -/
theorem integralIdele_quadratic_dirichlet_exists
    (φ : finiteAdeleIntegerSubringˣ →* ℂ) (hc : Continuous φ) (hq : ∀ u, φ u ^ 2 = 1) :
    ∃ D : ℕ, ∃ hD : 0 < D, ∃ χ : DirichletCharacter ℂ D,
      χ.IsQuadratic ∧ ∀ u : finiteAdeleIntegerSubringˣ,
        χ (@finiteAdeleResidue D ⟨ne_of_gt hD⟩ u.val) = φ u := by
  obtain ⟨D, hD, hker⟩ := integralIdele_quadratic_congruence hc hq
  letI : NeZero D := ⟨ne_of_gt hD⟩
  exact ⟨D, hD, integralIdeleDirichletCharacter D φ hker,
    integralIdeleDirichletCharacter_quadratic D φ hker hq,
    integralIdeleDirichletCharacter_apply D φ hker⟩

end
end Dubon2026
