import Dubon2026.FinitePlaceFunctionalHecke
import Dubon2026.FinitePlaceSphericalFormula

/-! # The exact original spherical function from an invariant functional and Hecke equation -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (ρ : Representation ℂ (GeneralLinearGroup (Fin 2)
      ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ)) V)
    (ℓ : V →ₗ[ℂ] ℂ) (y : V)
    (hℓ : ∀ k : finitePlaceGL2Gamma0 1 (rationalPrimePlace p (Fact.out : p.Prime)),
      ∀ x : V, ℓ (ρ k.val x) = ℓ x)
    (hy : ∀ k : finitePlaceGL2Gamma0 1 (rationalPrimePlace p (Fact.out : p.Prime)), ρ k.val y = y)
    (hc : ∀ u x, ρ (GeneralLinearGroup.scalar (Fin 2) u) x = x)
    (hn : ℓ y = 1) (z : ℂ)
    (heigen : finitePlaceHeckeTrace 1 p (Nat.coprime_one_right p) ρ y =
      ((Real.sqrt p : ℂ) * z) • y)

include hℓ hy hc hn heigen

/-- The actual radial values of the normalized invariant functional are exactly the original spherical Chebyshev coefficients. -/
theorem finitePlaceFunctional_spherical_radial (n : ℕ) :
    finitePlaceFunctionalRadial p ρ ℓ y n = sphericalChebyshevCoefficient p (Real.sqrt p) z n := by
  obtain ⟨hb, hr⟩ := finitePlaceFunctionalHecke_eigen_recurrence p ρ ℓ y hℓ hy hc _ heigen
  have hs0 : (Real.sqrt p : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (show (0 : ℝ) < p by exact_mod_cast (Fact.out : p.Prime).pos)).ne'
  have hs : (Real.sqrt p : ℂ) ^ 2 = p := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg p : (0 : ℝ) ≤ p)
  have he := radial_recurrence_chebyshev_formula p (Real.sqrt p) z hs0 hs _ hb hr n
  simpa only [finitePlaceFunctionalRadial, pow_zero, map_one, Module.End.one_apply, hn, one_mul] using he

/-- The genuine compact-invariant functional has the exact original spherical formula on every actual central-integral Cartan factorization. -/
theorem finitePlaceFunctional_spherical_cartan
    (u : ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ)ˣ) (n : ℕ)
    (l r : finitePlaceGL2Gamma0 1 (rationalPrimePlace p (Fact.out : p.Prime))) :
    ℓ (ρ (GeneralLinearGroup.scalar (Fin 2) u * l.val *
      (GeneralLinearGroup.map (finiteAdelePlace (rationalPrimePlace p (Fact.out : p.Prime)))
        (finiteAdelicHeckeDiagonal p)) ^ n * r.val) y) =
      sphericalChebyshevCoefficient p (Real.sqrt p) z n := by
  exact (sphericalFunctional_scalar_double_coset ρ _ ℓ hℓ y hy _ _ (hc u) l r).trans
    (finitePlaceFunctional_spherical_radial p ρ ℓ y hℓ hy hc hn z heigen n)

/-- An actual normalized spherical functional and a genuine unitary spherical coefficient with the same original Hecke value coincide on the entire original local group. -/
theorem finitePlaceFunctional_unitary_unique {W : Type*} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W]
    (σ : Representation ℂ (GeneralLinearGroup (Fin 2)
      ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ)) W)
    (hσ : ∀ g a b, inner ℂ (σ g a) (σ g b) = inner ℂ a b)
    (hσc : ∀ u a, σ (GeneralLinearGroup.scalar (Fin 2) u) a = a)
    (w : W) (hw : inner ℂ w w = 1)
    (hwK : ∀ k : finitePlaceGL2Gamma0 1 (rationalPrimePlace p (Fact.out : p.Prime)), σ k.val w = w)
    (hwT : finitePlaceHeckeTrace 1 p (Nat.coprime_one_right p) σ w =
      ((Real.sqrt p : ℂ) * z) • w)
    (g : GeneralLinearGroup (Fin 2) ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ)) :
    ℓ (ρ g y) = inner ℂ w (σ g w) := by
  obtain ⟨u, n, l, r, hg⟩ := finitePlaceGL2_cartan p (Fact.out : p.Prime) g
  rw [hg]
  exact (finitePlaceFunctional_spherical_cartan p ρ ℓ y hℓ hy hc hn z heigen u n l r).trans
    (finitePlace_unit_spherical_cartan_formula p σ hσ hσc w hw hwK z hwT u n l r).symm

end
end Dubon2026
