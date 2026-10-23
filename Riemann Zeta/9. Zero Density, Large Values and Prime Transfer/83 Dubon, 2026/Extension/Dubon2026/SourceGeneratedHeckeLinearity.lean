import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Algebra.Module.LinearMap.Defs

/-! DUB-17/18 -> original rank-two Galois realization -> linearity over
the constructed Hecke algebra. Once the actual Galois action commutes
with every prime scalar, native adjoin induction extends this to the
whole coefficient algebra. The input is prime commutation, not the
desired algebra-linear Galois representation. -/
namespace Dubon2026
noncomputable section

theorem map_smul_of_generating_hecke {K T V I : Type*}
    [CommSemiring K] [Semiring T] [Algebra K T]
    [AddCommMonoid V] [Module T V] [Module K V] [IsScalarTower K T V]
    (χ : I → T) (hχ : Algebra.adjoin K (Set.range χ) = ⊤)
    (u : Module.End K V) (hu : ∀ i x, u (χ i • x) = χ i • u x) :
    ∀ (t : T) (x : V), u (t • x) = t • u x := by
  intro t
  have ht : t ∈ Algebra.adjoin K (Set.range χ) := hχ.ge (by trivial)
  induction ht using Algebra.adjoin_induction with
  | mem t ht =>
      obtain ⟨i, rfl⟩ := ht
      exact hu i
  | algebraMap r =>
      intro x
      simpa only [algebraMap_smul] using u.map_smul r x
  | add a b _ _ ha hb =>
      intro x
      rw [add_smul, map_add, ha, hb, add_smul]
  | mul a b _ _ ha hb =>
      intro x
      rw [mul_smul, ha, hb, mul_smul]

end
end Dubon2026
