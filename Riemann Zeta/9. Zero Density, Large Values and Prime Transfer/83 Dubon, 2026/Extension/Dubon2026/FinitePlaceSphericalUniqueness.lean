import Dubon2026.FinitePlaceSphericalFormula

/-! # Genuine unitary spherical coefficients are determined by their original Hecke eigenvalue -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (ρ : Representation ℂ (GeneralLinearGroup (Fin 2)
      ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ)) V)
    (σ : Representation ℂ (GeneralLinearGroup (Fin 2)
      ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ)) W)
    (hρ : ∀ g x y, inner ℂ (ρ g x) (ρ g y) = inner ℂ x y)
    (hσ : ∀ g x y, inner ℂ (σ g x) (σ g y) = inner ℂ x y)
    (hcρ : ∀ u z, ρ (GeneralLinearGroup.scalar (Fin 2) u) z = z)
    (hcσ : ∀ u z, σ (GeneralLinearGroup.scalar (Fin 2) u) z = z)
    (v : V) (w : W) (hv : inner ℂ v v = 1) (hw : inner ℂ w w = 1)
    (hvK : ∀ g : finitePlaceGL2Gamma0 1 (rationalPrimePlace p (Fact.out : p.Prime)), ρ g.val v = v)
    (hwK : ∀ g : finitePlaceGL2Gamma0 1 (rationalPrimePlace p (Fact.out : p.Prime)), σ g.val w = w)
    (z : ℂ)
    (hzv : @finitePlaceHeckeTrace V inferInstance inferInstance 1 p inferInstance inferInstance
      inferInstance (Nat.coprime_one_right p) ρ v = ((Real.sqrt p : ℂ) * z) • v)
    (hzw : @finitePlaceHeckeTrace W inferInstance inferInstance 1 p inferInstance inferInstance
      inferInstance (Nat.coprime_one_right p) σ w = ((Real.sqrt p : ℂ) * z) • w)

include hρ hσ hcρ hcσ hv hw hvK hwK hzv hzw

/-- Actual local Cartan decomposition and the original intrinsic Hecke equations determine the full unit spherical function uniquely. -/
theorem finitePlace_unit_spherical_coefficient_unique
    (g : GeneralLinearGroup (Fin 2) ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ)) :
    inner ℂ v (ρ g v) = inner ℂ w (σ g w) := by
  obtain ⟨u, n, l, r, hg⟩ := finitePlaceGL2_cartan p (Fact.out : p.Prime) g
  rw [hg]
  exact (finitePlace_unit_spherical_cartan_formula p ρ hρ hcρ v hv hvK z hzv u n l r).trans
    (finitePlace_unit_spherical_cartan_formula p σ hσ hcσ w hw hwK z hzw u n l r).symm

/-- Equality of the actual full spherical functions forces equality of the original full local orbit Gram matrices. -/
theorem finitePlace_unit_spherical_orbit_gram
    (g h : GeneralLinearGroup (Fin 2) ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ)) :
    inner ℂ (ρ g v) (ρ h v) = inner ℂ (σ g w) (σ h w) := by
  rw [representation_inner_inverse ρ hρ g, representation_inner_inverse σ hσ g,
    ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
  exact finitePlace_unit_spherical_coefficient_unique p ρ σ hρ hσ hcρ hcσ v w hv hw hvK hwK z hzv hzw _

end
end Dubon2026
