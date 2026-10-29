import Dubon2026.SourceTateEndomorphisms

/-! DUB-17/18 -> original Gamma1 Tate Frobenius identity. The actual
Tate functor carries a twisted quadratic identity on every prime-power
torsion subgroup to the compatible-sequence module. The original Picard
consumer supplies all coordinate identities from its norm proof. -/
namespace Dubon2026.TateModule
noncomputable section
variable (ell : ℕ) [Fact ell.Prime] {J : Type*} [AddCommGroup J]

theorem tateMap_diamond_quadratic (H F D : AddMonoid.End J) (p : ℕ)
    (h : ∀ (n : ℕ) (x : J), ell ^ n • x = 0 → H (F x) = F (F (D x)) + p • x) :
    tateMap ell H * tateMap ell F =
      tateMap ell F * tateMap ell F * tateMap ell D + p • 1 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext n
  change H (F ((x : ℕ → J) n)) = F (F (D ((x : ℕ → J) n))) + p • (x : ℕ → J) n
  apply h n ((x : ℕ → J) n)
  rw [← Nat.cast_smul_eq_nsmul ℤ]
  exact torsion x n

end
end Dubon2026.TateModule
