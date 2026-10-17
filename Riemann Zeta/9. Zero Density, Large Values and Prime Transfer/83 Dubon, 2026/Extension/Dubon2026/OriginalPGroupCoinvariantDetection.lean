import Dubon2026.OriginalPGroupFixedVector
import Mathlib.RepresentationTheory.Coinvariants
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Detection by actual coinvariants in characteristic p

A nonzero functional on an original vector gives a nonzero fixed dual
vector for a finite p-group. It annihilates every original coinvariant
relation, so zero coinvariants force the coefficient to be zero. This
is the detection step for the mod-p induced-module criterion required
by DUB-17's actual integral projectivity proof.
The argument adapts the inspected Anthropic FLT induced-module solution
at revision 6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026
noncomputable section

/-- An original characteristic-p representation of a finite p-group is zero if every vector is a coinvariant relation. -/
theorem originalPGroup_zero_of_coinvariant_relations
    {k : Type*} [Field k] {p : ℕ} [Fact p.Prime] [CharP k p]
    {G : Type*} [Group G] [Finite G] (hG : IsPGroup p G)
    {W : Type*} [AddCommGroup W] [Module k W] (σ : Representation k G W)
    (h : ∀ w : W, w ∈ Representation.Coinvariants.ker σ) (w : W) : w = 0 := by
  classical
  by_contra hw
  have hd : ¬ ∀ φ : Module.Dual k W, φ w = 0 :=
    fun H => hw ((Module.forall_dual_apply_eq_zero_iff k w).mp H)
  push Not at hd
  obtain ⟨φ, hφ⟩ := hd
  have hφ0 : φ ≠ 0 := fun H => hφ (by rw [H]; rfl)
  obtain ⟨ψ, hψ0, hψ⟩ := originalPGroup_exists_nonzero_fixed_vector hG σ.dual hφ0
  have hker : ∀ x ∈ Representation.Coinvariants.ker σ, ψ x = 0 := by
    intro x hx
    refine Submodule.span_induction ?_ (map_zero ψ)
      (fun a b _ _ ha hb => by rw [map_add, ha, hb, add_zero])
      (fun c a _ ha => by rw [map_smul, ha, smul_zero]) hx
    rintro _ ⟨⟨g, y⟩, rfl⟩
    have he := hψ g⁻¹
    rw [Representation.dual_apply, inv_inv] at he
    have hy := congrArg (fun f : Module.Dual k W => f y) he
    simp only [Module.Dual.transpose_apply, LinearMap.comp_apply] at hy
    change ψ (σ g y - y) = 0
    rw [map_sub, hy, sub_self]
  apply hψ0
  apply LinearMap.ext
  intro x
  exact hker x (h x)

end
end Dubon2026
