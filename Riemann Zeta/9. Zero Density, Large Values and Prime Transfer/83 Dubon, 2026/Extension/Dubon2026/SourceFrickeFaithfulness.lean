import Dubon2026.SourceFrickeSeparation

/-! DUB-17/18 -> original all-weight arithmetic association -> finite Gamma1
characters -> Picard/H1 and diamond comparison -> cusp differential
realization -> rational Fourier structure -> faithful Fricke generators.
The actual row action and proved Fricke separation identify its stabilizer
with the principal congruence subgroup up to sign.
The finite row-action argument adapts anthropics/fermats-last-theorem,
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache License 2.0. -/
namespace Dubon2026.SourceFricke
noncomputable section
open UpperHalfPlane Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm

theorem mem_Gamma_or_neg_mem_of_vecMulSL {N : ℕ} [NeZero N] (γ : SL(2, ℤ))
    (h : ∀ a : Fin 2 → ZMod N, a ≠ 0 → vecMulSL N a γ = a ∨ vecMulSL N a γ = -a) :
    γ ∈ CongruenceSubgroup.Gamma N ∨ -γ ∈ CongruenceSubgroup.Gamma N := by
  rcases Nat.lt_or_ge 1 N with hN | hN
  · haveI : Fact (1 < N) := ⟨hN⟩
    have h10 : (1 : ZMod N) ≠ 0 := one_ne_zero
    have r1 := h ![1, 0] (fun e ↦ h10 (by simpa using congrFun e 0))
    have r2 := h ![0, 1] (fun e ↦ h10 (by simpa using congrFun e 1))
    have r3 := h ![1, 1] (fun e ↦ h10 (by simpa using congrFun e 0))
    simp only [funext_iff, Fin.forall_fin_two, vecMulSL_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, one_mul, zero_mul, add_zero, zero_add,
      Pi.neg_apply, neg_zero] at r1 r2 r3
    have e01 : ((γ 0 1 : ℤ) : ZMod N) = 0 := by rcases r1 with ⟨_, e⟩ | ⟨_, e⟩ <;> exact e
    have e10 : ((γ 1 0 : ℤ) : ZMod N) = 0 := by rcases r2 with ⟨e, _⟩ | ⟨e, _⟩ <;> exact e
    have e0011 : ((γ 0 0 : ℤ) : ZMod N) = ((γ 1 1 : ℤ) : ZMod N) := by
      rcases r3 with ⟨c1, c2⟩ | ⟨c1, c2⟩ <;>
        (rw [e10, add_zero] at c1; rw [e01, zero_add] at c2; rw [c1, c2])
    rw [CongruenceSubgroup.Gamma_mem, CongruenceSubgroup.Gamma_mem]
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg, neg_eq_zero]
    rcases r1 with ⟨a1, _⟩ | ⟨a1, _⟩
    · left; exact ⟨a1, e01, e10, by rw [← e0011]; exact a1⟩
    · right; exact ⟨by rw [a1, neg_neg], e01, e10, by rw [← e0011, a1, neg_neg]⟩
  · have : N = 1 := by have := NeZero.ne N; omega
    subst this
    left
    simp [CongruenceSubgroup.Gamma_one_top]

theorem frickeF_faithful {N : ℕ} [NeZero N] (γ : SL(2, ℤ))
    (h : ∀ i : FrickeIdx N, ∀ τ : ℍ, frickeF N i.1 (γ • τ) = frickeF N i.1 τ) :
    γ ∈ CongruenceSubgroup.Gamma N ∨ -γ ∈ CongruenceSubgroup.Gamma N := by
  refine mem_Gamma_or_neg_mem_of_vecMulSL γ fun a ha ↦ ?_
  have hfun : frickeF N a = frickeF N (vecMulSL N a γ) := by
    funext τ; rw [← frickeF_slash, h ⟨a, ha⟩ τ]
  rcases frickeF_eq_imp ⟨a, ha⟩ ⟨vecMulSL N a γ, vecMulSL_ne_zero ha γ⟩ hfun with e | e
  · exact Or.inl e
  · exact Or.inr e


end
end Dubon2026.SourceFricke
