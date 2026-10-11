import Dubon2026.ScaledLatticeProducts

/-! # Actual scalar lattice filtration and its product gain at every level -/

namespace Dubon2026
noncomputable section

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S]

/-- Iterated original scalar images are the literal product-scalar image. -/
theorem scalarLatticeImage_scalar_image (A : Submodule R S) (r s : R) :
    scalarLatticeImage (scalarLatticeImage A r) s = scalarLatticeImage A (s * r) := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := (mem_scalarLatticeImage _ s x).mp hx
    obtain ⟨a, ha, rfl⟩ := (mem_scalarLatticeImage A r y).mp hy
    exact (mem_scalarLatticeImage A (s * r) _).mpr ⟨a, ha, mul_smul s r a⟩
  · intro hx
    obtain ⟨a, ha, rfl⟩ := (mem_scalarLatticeImage A (s * r) x).mp hx
    exact (mem_scalarLatticeImage _ s _).mpr
      ⟨r • a, (mem_scalarLatticeImage A r _).mpr ⟨a, ha, rfl⟩, (mul_smul s r a).symm⟩

/-- Every scalar image of the original submodule remains in that submodule. -/
theorem scalarLatticeImage_le (A : Submodule R S) (r : R) : scalarLatticeImage A r ≤ A := by
  intro x hx
  obtain ⟨a, ha, rfl⟩ := (mem_scalarLatticeImage A r x).mp hx
  exact A.smul_mem r ha

/-- Original lattice inclusion is preserved by the same original scalar image. -/
theorem scalarLatticeImage_mono (A B : Submodule R S) (h : A ≤ B) (r : R) :
    scalarLatticeImage A r ≤ scalarLatticeImage B r := by
  intro x hx
  obtain ⟨a, ha, rfl⟩ := (mem_scalarLatticeImage A r x).mp hx
  exact (mem_scalarLatticeImage B r _).mpr ⟨a, h ha, rfl⟩

/-- The actual power filtration descends by one original scalar multiplication. -/
theorem scalarLatticeImage_pow_succ (A : Submodule R S) (π : R) (j : ℕ) :
    scalarLatticeImage A (π ^ (j + 1)) =
      scalarLatticeImage (scalarLatticeImage A (π ^ j)) π := by
  rw [scalarLatticeImage_scalar_image, pow_succ']

/-- The genuine scalar-power lattice filtration is nested. -/
theorem scalarLatticeImage_pow_succ_le (A : Submodule R S) (π : R) (j : ℕ) :
    scalarLatticeImage A (π ^ (j + 1)) ≤ scalarLatticeImage A (π ^ j) := by
  rw [scalarLatticeImage_pow_succ]
  exact scalarLatticeImage_le _ π

/-- An original one-factor product gain persists at every actual scalar
level. The displayed witness remains in the original lattice. -/
theorem scalarLatticeImage_level_product_gain (A : Submodule R S) (π : R)
    (hmul : ∀ a ∈ A, ∀ b ∈ A, a * b ∈ scalarLatticeImage A π)
    (j : ℕ) {x y : S}
    (hx : x ∈ scalarLatticeImage A (π ^ j))
    (hy : y ∈ scalarLatticeImage A (π ^ j)) :
    x * y ∈ scalarLatticeImage (scalarLatticeImage A (π ^ j)) π := by
  obtain ⟨a, ha, rfl⟩ := (mem_scalarLatticeImage A _ x).mp hx
  obtain ⟨b, hb, rfl⟩ := (mem_scalarLatticeImage A _ y).mp hy
  obtain ⟨c, hc, he⟩ := (mem_scalarLatticeImage A π (a * b)).mp (hmul a ha b hb)
  refine (mem_scalarLatticeImage _ π _).mpr
    ⟨π ^ j • (π ^ j • c),
      (mem_scalarLatticeImage A _ _).mpr ⟨π ^ j • c, A.smul_mem _ hc, rfl⟩, ?_⟩
  have hprod : (π ^ j • a) * (π ^ j • b) =
      π ^ j • (π ^ j • (a * b)) := by
    simp only [Algebra.smul_def]
    ring
  rw [hprod, ← he]
  simp only [Algebra.smul_def]
  ring

end
end Dubon2026
