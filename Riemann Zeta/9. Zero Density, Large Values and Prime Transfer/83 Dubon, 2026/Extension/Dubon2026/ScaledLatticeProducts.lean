import Mathlib.Algebra.Module.Submodule.Map
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Tactic.Ring

/-! # Actual products in original scalar images of full lattices -/

namespace Dubon2026
noncomputable section

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S]

/-- The actual scalar image of the original lattice inside the same ring. -/
def scalarLatticeImage (A : Submodule R S) (r : R) : Submodule R S :=
  A.map (r • LinearMap.id)

/-- Membership in the actual scalar image retains its original preimage. -/
theorem mem_scalarLatticeImage (A : Submodule R S) (r : R) (x : S) :
    x ∈ scalarLatticeImage A r ↔ ∃ a ∈ A, r • a = x := by
  simp only [scalarLatticeImage, Submodule.mem_map, LinearMap.smul_apply, LinearMap.id_apply]

/-- Original lower and upper lattice bounds force an extra uniformizer
factor in products in the original scaled lattice. The witness remains in
that same scalar image, not in an independently supplied comparison module. -/
theorem scalarLatticeImage_product_gain
    (A : Submodule R S) (B : Subring S) (π : R) (n : ℕ)
    (hupper : ∀ x ∈ A, x ∈ B) (hlower : ∀ x ∈ B, π ^ n • x ∈ A)
    {x y : S} (hx : x ∈ scalarLatticeImage A (π ^ (n + 1)))
    (hy : y ∈ scalarLatticeImage A (π ^ (n + 1))) :
    ∃ z ∈ scalarLatticeImage A (π ^ (n + 1)), x * y = π • z := by
  obtain ⟨a, ha, rfl⟩ := (mem_scalarLatticeImage A _ x).mp hx
  obtain ⟨b, hb, rfl⟩ := (mem_scalarLatticeImage A _ y).mp hy
  let t : S := π ^ n • (a * b)
  have ht : t ∈ A := hlower (a * b) (B.mul_mem (hupper a ha) (hupper b hb))
  refine ⟨π ^ (n + 1) • t, (mem_scalarLatticeImage A _ _).mpr ⟨t, ht, rfl⟩, ?_⟩
  dsimp [t]
  simp only [Algebra.smul_def, map_pow, map_mul, pow_add, pow_one]
  ring

/-- The same original scaled lattice is closed under multiplication as a
consequence of the stronger proved extra-factor identity. -/
theorem scalarLatticeImage_mul_mem
    (A : Submodule R S) (B : Subring S) (π : R) (n : ℕ)
    (hupper : ∀ x ∈ A, x ∈ B) (hlower : ∀ x ∈ B, π ^ n • x ∈ A)
    {x y : S} (hx : x ∈ scalarLatticeImage A (π ^ (n + 1)))
    (hy : y ∈ scalarLatticeImage A (π ^ (n + 1))) :
    x * y ∈ scalarLatticeImage A (π ^ (n + 1)) := by
  obtain ⟨z, hz, hxy⟩ := scalarLatticeImage_product_gain A B π n hupper hlower hx hy
  rw [hxy]
  exact (scalarLatticeImage A (π ^ (n + 1))).smul_mem π hz

end
end Dubon2026
