import Dubon2026.FiniteIdelePrimeAway

/-! # The exact original Dirichlet character value at a genuine prime uniformizer -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain

/-- The actual prime-removed integral idele has the inverse original Dirichlet prime value. -/
theorem finiteIdeleDirichletCharacter_primeAway {D : ℕ} [NeZero D]
    (χ : DirichletCharacter ℂ D) (p : ℕ) [NeZero p] (hp : p.Prime) (hpD : p.Coprime D) :
    finiteIdeleDirichletCharacter χ (finiteIdelePrimeAway p hp) = (χ (p : ZMod D))⁻¹ := by
  have he : Units.map finiteAdeleIntegerSubring.subtype.toMonoidHom
      (finiteIdelePrimeAwayIntegerUnit p hp) = finiteIdelePrimeAway p hp := Units.ext rfl
  rw [← he, finiteIdeleDirichletCharacter_integral, finiteIdelePrimeAway_residue D p hp hpD]

/-- The genuine local prime insertion has exactly the original Dirichlet prime value away from the modulus. -/
theorem finiteIdeleDirichletCharacter_uniformizer {D : ℕ} [NeZero D]
    (χ : DirichletCharacter ℂ D) (p : ℕ) [NeZero p] (hp : p.Prime) (hpD : p.Coprime D) :
    finiteIdeleDirichletCharacter χ
      (finiteAdeleLocalUnit (rationalPrimePlace p hp) (finitePlacePrimeUnit p _)) = χ (p : ZMod D) := by
  have hpos : (0 : ℚ) < p := by exact_mod_cast hp.pos
  have h := finiteIdeleDirichletCharacter_primeAway χ p hp hpD
  rw [finiteIdelePrimeAway, map_mul, map_inv,
    finiteIdeleDirichletCharacter_positive_rational χ (p : ℚ) hpos, one_mul] at h
  exact inv_injective h

end
end Dubon2026
