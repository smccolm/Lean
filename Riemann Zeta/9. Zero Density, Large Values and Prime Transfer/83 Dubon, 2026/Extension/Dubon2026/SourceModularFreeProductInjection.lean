import Dubon2026.SourceModularPingPongSets

/-! DUB-17/18 -> original Gamma1 Picard/H1 -> Abel-Jacobi -> unitary
multiplier correction -> integral parabolic-character lifting -> the actual
PSL2(Z) free-product presentation. Adapted from
anthropics/fermats-last-theorem, Apache-2.0, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularGroup_exists_mulEquiv_freeProduct_quotient_center.
Native Mathlib ping-pong, modular generators and scalar center are reused.
This module discharges only its named presentation dependency. -/
namespace Dubon2026.SourceModularFreeProduct
open Matrix MatrixGroups ModularGroup
open scoped Pointwise
open scoped IrrationalPt
open Subgroup

/-- The two cyclic factors of orders two and three. -/
abbrev G23 (i : Fin 2) : Type := Multiplicative (ZMod (i.val + 2))

/-- Both cyclic factors have order greater than one. -/
scoped instance factOneLt (i : Fin 2) : Fact (1 < i.val + 2) := ⟨by omega⟩

/-- The two generator permutations of the irrational Mobius action. -/
noncomputable def gen : Fin 2 → Equiv.Perm IrrationalPt := ![permS, permU]

@[scoped simp] theorem gen_zero : gen 0 = permS := rfl
@[scoped simp] theorem gen_one : gen 1 = permU := rfl

theorem gen_pow_eq_one (i : Fin 2) : gen i ^ (i.val + 2) = 1 := by
  fin_cases i
  · exact permS_sq
  · exact permU_pow_three

/-- The cyclic factor homomorphism determined by the corresponding generator permutation. -/
noncomputable def incl (i : Fin 2) : G23 i →* Equiv.Perm IrrationalPt where
  toFun x := gen i ^ (Multiplicative.toAdd x).val
  map_one' := by rw [toAdd_one, ZMod.val_zero, pow_zero]
  map_mul' x y := by
    rw [toAdd_mul, ZMod.val_add, ← pow_eq_pow_mod _ (gen_pow_eq_one i), pow_add]

theorem incl_ofAdd_one (i : Fin 2) : incl i (Multiplicative.ofAdd 1) = gen i := by
  show gen i ^ (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod (i.val + 2)))).val = gen i
  rw [toAdd_ofAdd, ZMod.val_one, pow_one]

theorem incl_zero_eq (h : G23 0) (hne : h ≠ 1) : incl 0 h = permS := by
  have hh : h = Multiplicative.ofAdd 1 := by
    revert hne; revert h; decide
  subst hh
  rw [incl_ofAdd_one, gen_zero]

theorem incl_one_eq (h : G23 1) (hne : h ≠ 1) :
    incl 1 h = permU ∨ incl 1 h = permU * permU := by
  have hh : h = Multiplicative.ofAdd 1 ∨
      h = Multiplicative.ofAdd 1 * Multiplicative.ofAdd 1 := by
    revert hne; revert h; decide
  rcases hh with rfl | rfl
  · left; rw [incl_ofAdd_one, gen_one]
  · right; rw [map_mul, incl_ofAdd_one, gen_one]

/-- The positive and negative irrational ping-pong domains. -/
def pingPongSet : Fin 2 → Set IrrationalPt := ![Pos, Neg]

@[scoped simp] theorem pingPongSet_zero : pingPongSet 0 = Pos := rfl
@[scoped simp] theorem pingPongSet_one : pingPongSet 1 = Neg := rfl

theorem pingPong : Pairwise fun i j => ∀ h : G23 i, h ≠ 1 →
    incl i h • pingPongSet j ⊆ pingPongSet i := by
  intro i j hij h hne
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · rintro _ ⟨y, hy, rfl⟩
    show incl 0 h • y ∈ Pos
    rw [incl_zero_eq h hne]
    exact S_smul_neg_mem_pos hy
  · rintro _ ⟨y, hy, rfl⟩
    show incl 1 h • y ∈ Neg
    rcases incl_one_eq h hne with h1 | h2
    · rw [h1]
      exact ST_smul_pos_mem_neg hy
    · rw [h2, permU, ← map_mul]
      exact ST_sq_smul_pos_mem_neg hy
  · exact absurd rfl hij

theorem three_le_card_factor_one : 3 ≤ Cardinal.mk (G23 1) := by
  have hc : Fintype.card (G23 1) = 3 := by decide
  rw [Cardinal.mk_fintype, hc]
  norm_num

theorem lift_injective : Function.Injective (Monoid.CoprodI.lift incl) := by
  apply Monoid.CoprodI.lift_injective_of_ping_pong incl
    (Or.inr ⟨1, three_le_card_factor_one⟩) pingPongSet
  · intro i
    fin_cases i
    · exact pos_nonempty
    · exact neg_nonempty
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact disjoint_pos_neg
    · exact disjoint_pos_neg.symm
    · exact absurd rfl hij
  · exact pingPong

theorem range_lift_eq : (Monoid.CoprodI.lift incl).range = toPerm.range := by
  apply le_antisymm
  · rw [Monoid.CoprodI.range_eq_iSup]
    apply iSup_le
    intro i
    rintro _ ⟨x, rfl⟩
    show gen i ^ (Multiplicative.toAdd x).val ∈ toPerm.range
    refine Subgroup.pow_mem _ ?_ _
    fin_cases i
    · exact ⟨S, rfl⟩
    · exact ⟨S * T, rfl⟩
  · rw [MonoidHom.range_eq_map, ← SpecialLinearGroup.SL2Z_generators, MonoidHom.map_closure,
      Subgroup.closure_le]
    rintro _ ⟨x, hx, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    have hS : toPerm S ∈ (Monoid.CoprodI.lift incl).range := by
      refine ⟨Monoid.CoprodI.of (i := 0) (Multiplicative.ofAdd 1), ?_⟩
      rw [Monoid.CoprodI.lift_of, incl_ofAdd_one, gen_zero, permS]
    have hST : toPerm (S * T) ∈ (Monoid.CoprodI.lift incl).range := by
      refine ⟨Monoid.CoprodI.of (i := 1) (Multiplicative.ofAdd 1), ?_⟩
      rw [Monoid.CoprodI.lift_of, incl_ofAdd_one, gen_one, permU]
    rcases hx with rfl | rfl
    · exact hS
    · have : toPerm T = (toPerm S)⁻¹ * toPerm (S * T) := by
        rw [← map_inv, ← map_mul, inv_mul_cancel_left]
      rw [this]
      exact mul_mem (inv_mem hS) hST

end Dubon2026.SourceModularFreeProduct
