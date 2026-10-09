import Dubon2026.RepresentationSphericalFunctional
import Dubon2026.FinitePlaceHeckeRadialCosets
import Dubon2026.FinitePlaceHeckeTrace

/-! # The original radial coset coefficients for a genuine invariant linear functional -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (ρ : Representation ℂ (GeneralLinearGroup (Fin 2)
      ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ)) V)
    (ℓ : V →ₗ[ℂ] ℂ) (y : V)

/-- The literal original diagonal coefficient of the actual linear functional and vector. -/
def finitePlaceFunctionalRadial (n : ℕ) : ℂ :=
  ℓ (ρ ((GeneralLinearGroup.map (finiteAdelePlace (rationalPrimePlace p (Fact.out : p.Prime)))
    (finiteAdelicHeckeDiagonal p)) ^ n) y)

variable
    (hℓ : ∀ k : finitePlaceGL2Gamma0 1 (rationalPrimePlace p (Fact.out : p.Prime)),
      ∀ x : V, ℓ (ρ k.val x) = ℓ x)
    (hy : ∀ k : finitePlaceGL2Gamma0 1 (rationalPrimePlace p (Fact.out : p.Prime)), ρ k.val y = y)

include hℓ hy in
/-- Every original nonzero-residue or Bezout radial representative has exactly the succeeding radial coefficient for the genuine invariant functional. -/
theorem finitePlaceFunctionalRadial_forward (n : ℕ) (i : Option (ZMod p))
    (hi : i ≠ some 0) :
    ℓ (ρ (finitePlaceHeckeRadialMatrix 1 p (Nat.coprime_one_right p)
      (rationalPrimePlace p (Fact.out : p.Prime)) n i) y) =
      finitePlaceFunctionalRadial p ρ ℓ y (n + 1) := by
  have hcoset : ∃ l r : finitePlaceGL2Gamma0 1 (rationalPrimePlace p (Fact.out : p.Prime)),
      finitePlaceHeckeRadialMatrix 1 p (Nat.coprime_one_right p)
        (rationalPrimePlace p (Fact.out : p.Prime)) n i =
      l.val * (GeneralLinearGroup.map (finiteAdelePlace (rationalPrimePlace p (Fact.out : p.Prime)))
        (finiteAdelicHeckeDiagonal p)) ^ (n + 1) * r.val := by
    cases i with
    | none => exact finitePlaceHeckeRadial_none_forward 1 p (Nat.coprime_one_right p) n
    | some a => exact finitePlaceHeckeRadial_some_forward 1 p (Nat.coprime_one_right p) n a (by simpa using hi)
  obtain ⟨l, r, he⟩ := hcoset
  rw [he]
  exact sphericalFunctional_double_coset ρ _ ℓ hℓ y hy _ l r

/-- The actual zero-residue radial branch has the preceding coefficient when the genuine scalar action is trivial. -/
theorem finitePlaceFunctionalRadial_backward
    (hc : ∀ u x, ρ (GeneralLinearGroup.scalar (Fin 2) u) x = x) (n : ℕ) :
    ℓ (ρ (finitePlaceHeckeRadialMatrix 1 p (Nat.coprime_one_right p)
      (rationalPrimePlace p (Fact.out : p.Prime)) (n + 1) (some 0)) y) =
      finitePlaceFunctionalRadial p ρ ℓ y n := by
  rw [finitePlaceHeckeRadial_some_zero, map_mul, Module.End.mul_apply, hc]
  rfl

end
end Dubon2026
