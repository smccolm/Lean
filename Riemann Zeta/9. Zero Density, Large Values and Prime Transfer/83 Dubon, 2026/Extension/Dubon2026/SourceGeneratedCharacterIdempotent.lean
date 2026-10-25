import Mathlib.Algebra.Algebra.Subalgebra.Lattice

/-! DUB-17/18 -> primitive Tate rank-two image. The prescribed scalar
identity for the generating prime Hecke operators extends to their actual
coefficient algebra by native adjoin induction. -/
namespace Dubon2026
noncomputable section

theorem character_scalar_action_of_generators
    {K T E A I : Type*} [CommSemiring K] [Semiring T] [CommSemiring E] [Semiring A]
    [Algebra K T] [Algebra K E] [Algebra K A] [Algebra E A] [IsScalarTower K E A]
    (χ : I → T) (hχ : Algebra.adjoin K (Set.range χ) = ⊤)
    (φ : T →ₐ[K] A) (κ : T →ₐ[K] E) (e : A)
    (he : ∀ i, φ (χ i) * e = κ (χ i) • e) :
    ∀ t : T, φ t * e = κ t • e := by
  intro t
  have ht : t ∈ Algebra.adjoin K (Set.range χ) := hχ.ge (by trivial)
  induction ht using Algebra.adjoin_induction with
  | mem t ht =>
    obtain ⟨i, rfl⟩ := ht
    exact he i
  | algebraMap r =>
    rw [φ.commutes, κ.commutes, algebraMap_smul, Algebra.smul_def]
  | add a b _ _ ha hb =>
    rw [map_add, map_add, add_mul, ha, hb, add_smul]
  | mul a b _ _ ha hb =>
    rw [map_mul, map_mul, mul_assoc, hb, mul_smul_comm, ha, smul_smul,
      mul_comm (κ b) (κ a)]

end
end Dubon2026
