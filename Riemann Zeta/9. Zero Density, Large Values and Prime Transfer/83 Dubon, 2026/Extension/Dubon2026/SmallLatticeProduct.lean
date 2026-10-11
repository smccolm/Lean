import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Tactic.Ring

/-! # A genuine small-product bound for an original full lattice -/

namespace Dubon2026

/-- If the original lattice contains `π^n S`, then products after scaling
by `π^(n+1)` gain an additional factor of `π` in that same lattice.
No equality between the lattice and its square is assumed. -/
theorem smallLattice_scaled_product
    {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    (A : Submodule R S) (π : R) (n : ℕ)
    (hA : ∀ z : S, π ^ n • z ∈ A) (x y : S) :
    ∃ z : S, z ∈ A ∧
      (π ^ (n + 1) • x) * (π ^ (n + 1) • y) = π ^ (n + 2) • z := by
  refine ⟨π ^ n • (x * y), hA (x * y), ?_⟩
  simp only [Algebra.smul_def, map_pow, map_mul, pow_add, pow_one, pow_two]
  ring

end Dubon2026
