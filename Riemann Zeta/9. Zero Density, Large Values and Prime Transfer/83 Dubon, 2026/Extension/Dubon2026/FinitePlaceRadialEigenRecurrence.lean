import Dubon2026.FinitePlaceHeckeRadialTrace

/-! # The exact spherical radial recurrence derived from the genuine local Hecke eigenvector -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

/-- An actual eigenvector of the original intrinsic Hecke trace gives its exact boundary equation and radial recurrence. -/
theorem finitePlaceHecke_radial_eigen_recurrence {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] (N p : ℕ) [NeZero N] [NeZero p] [Fact p.Prime]
    (hpN : p.Coprime N)
    (ρ : Representation ℂ
      (GeneralLinearGroup (Fin 2) ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ)) V)
    (hρ : ∀ g x y, inner ℂ (ρ g x) (ρ g y) = inner ℂ x y)
    (hscalar : ∀ u z, ρ (GeneralLinearGroup.scalar (Fin 2) u) z = z)
    (x y : V)
    (hx : ∀ g : finitePlaceGL2Gamma0 N (rationalPrimePlace p (Fact.out : p.Prime)), ρ g.val x = x)
    (hy : ∀ g : finitePlaceGL2Gamma0 N (rationalPrimePlace p (Fact.out : p.Prime)), ρ g.val y = y)
    (μ : ℂ)
    (heigen : @finitePlaceHeckeTrace V inferInstance inferInstance N p
      inferInstance inferInstance inferInstance hpN ρ y = μ • y) :
    let φ := @finitePlaceRadialCoefficient V inferInstance inferInstance p
      inferInstance inferInstance ρ x y
    μ * φ 0 = ((p : ℂ) + 1) * φ 1 ∧
      ∀ n, μ * φ (n + 1) = φ n + (p : ℂ) * φ (n + 2) := by
  dsimp only
  constructor
  · have he := @finitePlaceHeckeTrace_radial_zero V inferInstance inferInstance N p
      inferInstance inferInstance inferInstance hpN ρ hρ hscalar x y hx hy
    rw [heigen, inner_smul_right] at he
    simpa only [finitePlaceRadialCoefficient, pow_zero, map_one, Module.End.one_apply] using he
  · intro n
    have he := @finitePlaceHeckeTrace_radial_successor V inferInstance inferInstance N p
      inferInstance inferInstance inferInstance hpN ρ hρ hscalar x y hx hy n
    rw [heigen, map_smul, inner_smul_right] at he
    exact he

end
end Dubon2026
