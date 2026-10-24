import Dubon2026.SourceEllipticCharThreeStabilizerCoordinates
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-! Counting the actual scaling and translation coordinates bounds the
characteristic-three exceptional stabilizer by twelve. This is the exact
bound needed to identify its inertia image in the DUB-17/18 wild census. -/
namespace Dubon2026.SourceEllipticExceptional
open WeierstrassCurve Polynomial
noncomputable section
variable {K : Type*} [Field K] [CharP K 3]

omit [CharP K 3] in
theorem cube_eq_self_iff_three_values (x : K) :
    x ^ 3 = x ↔ x = 0 ∨ x = 1 ∨ x = -1 := by
  constructor
  · intro h
    have hz : x * (x - 1) * (x + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp hz with hz | hz
    · rcases mul_eq_zero.mp hz with hz | hz
      · exact Or.inl hz
      · exact Or.inr (Or.inl (sub_eq_zero.mp hz))
    · exact Or.inr (Or.inr (eq_neg_of_add_eq_zero_left hz))
  · rintro (rfl | rfl | rfl) <;> ring

theorem char_three_stabilizer_card_le_twelve :
    Finite (MulAction.stabilizer (VariableChange K) (EA (-1 : K))) ∧
      Nat.card (MulAction.stabilizer (VariableChange K) (EA (-1 : K))) ≤ 12 := by
  classical
  let U := (nthRoots 4 (1 : K)).toFinset
  let T : Finset K := {0, 1, -1}
  let f : MulAction.stabilizer (VariableChange K) (EA (-1 : K)) → U × T := fun C =>
    ⟨⟨C.val.u, by
      rw [Multiset.mem_toFinset, mem_nthRoots (by norm_num : 0 < (4 : ℕ))]
      exact (char_three_stabilizer_coordinates (MulAction.mem_stabilizer_iff.mp C.property)).2.2.1⟩,
      ⟨C.val.r, by
        have hr := (char_three_stabilizer_coordinates (MulAction.mem_stabilizer_iff.mp C.property)).2.2.2
        simpa only [T, Finset.mem_insert, Finset.mem_singleton] using
          (cube_eq_self_iff_three_values C.val.r).mp hr⟩⟩
  have hf : Function.Injective f := by
    intro C D h
    have hu : (C.val.u : K) = D.val.u := congrArg (fun x : U × T => x.1.val) h
    have hr : C.val.r = D.val.r := congrArg (fun x : U × T => x.2.val) h
    have hc := char_three_stabilizer_coordinates (MulAction.mem_stabilizer_iff.mp C.property)
    have hd := char_three_stabilizer_coordinates (MulAction.mem_stabilizer_iff.mp D.property)
    exact Subtype.ext (VariableChange.ext (Units.ext hu) hr (hc.1.trans hd.1.symm)
      (hc.2.1.trans hd.2.1.symm))
  letI : Finite (MulAction.stabilizer (VariableChange K) (EA (-1 : K))) :=
    Finite.of_injective f hf
  refine ⟨inferInstance, (Nat.card_le_card_of_injective f hf).trans ?_⟩
  rw [Nat.card_prod, Nat.card_eq_finsetCard, Nat.card_eq_finsetCard]
  have hU : U.card ≤ 4 := (Multiset.toFinset_card_le _).trans (card_nthRoots 4 1)
  have hT : T.card ≤ 3 := by
    exact (Finset.card_insert_le _ _).trans (by
      have h := Finset.card_insert_le (1 : K) {-1}
      simp only [Finset.card_singleton] at h
      omega)
  exact (Nat.mul_le_mul hU hT).trans (by norm_num)

end
end Dubon2026.SourceEllipticExceptional
