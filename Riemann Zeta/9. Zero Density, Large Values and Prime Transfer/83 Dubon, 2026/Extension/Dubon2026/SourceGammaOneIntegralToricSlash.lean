import Dubon2026.SourceGammaOneIntegralToricWeightFour

/-! DUB-17/18 -> original Gamma1 genus preservation -> finite elliptic
fibers -> integral toric coordinates. Derive the exact Gamma0 diamond
permutation of the constructed integral forms by finite-sum reindexing.
Native SlashAction.sum_slash replaces a separate finite-sum induction.
Adapted from Anthropic FLT ToricFourier, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2. -/
namespace Dubon2026.SourceFunctionField.GammaOne.ToricFourier
noncomputable section
open UpperHalfPlane CongruenceSubgroup SourceFricke ModularForm
open scoped MatrixGroups ModularForm Manifold
variable (M : ℕ) [NeZero M]

omit [NeZero M] in
theorem det_mod {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) :
    ((γ 1 1 : ℤ) : ZMod M) * ((γ 0 0 : ℤ) : ZMod M) = 1 := by
  have hdet := Matrix.SpecialLinearGroup.det_coe γ
  rw [Matrix.det_fin_two] at hdet
  have h := congrArg (fun z : ℤ => (z : ZMod M)) hdet
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_one] at h
  have hc : ((γ 1 0 : ℤ) : ZMod M) = 0 := Gamma0_mem.mp hγ
  rw [hc, mul_zero, sub_zero, mul_comm] at h
  exact h

theorem sum_reindex {V : Type*} [AddCommMonoid V] [Module ℂ V] (G : ZMod M → V) (c : ZMod M)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) :
    ∑ t ∈ nz M, (ψ (isPrimitiveRoot_zetaN (NeZero.ne M)) (-(t * c))) • G (t * ((γ 1 1 : ℤ) : ZMod M)) =
      ∑ t ∈ nz M, (ψ (isPrimitiveRoot_zetaN (NeZero.ne M)) (-(t * (c * ((γ 0 0 : ℤ) : ZMod M))))) • G t := by
  set δ : ZMod M := ((γ 1 1 : ℤ) : ZMod M) with hδ
  set a : ZMod M := ((γ 0 0 : ℤ) : ZMod M) with ha
  have hda : δ * a = 1 := det_mod M hγ
  refine Finset.sum_nbij' (fun t => t * δ) (fun t => t * a) ?_ ?_ ?_ ?_ ?_
  · intro t ht
    simp only [nz, Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
    intro h
    apply ht
    have : t * δ * a = 0 := by rw [h, zero_mul]
    rwa [mul_assoc, hda, mul_one] at this
  · intro t ht
    simp only [nz, Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
    intro h
    apply ht
    have : t * a * δ = 0 := by rw [h, zero_mul]
    rwa [mul_assoc, mul_comm a δ, hda, mul_one] at this
  · intro t _
    dsimp only
    rw [mul_assoc, hda, mul_one]
  · intro t _
    dsimp only
    rw [mul_assoc, mul_comm a δ, hda, mul_one]
  · intro t _
    congr 2
    linear_combination (t * c) * hda

theorem B_slash (c : ZMod M) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) :
    (⇑(B M c) : ℍ → ℂ) ∣[(2 : ℤ)] γ = ⇑(B M (c * ((γ 0 0 : ℤ) : ZMod M))) := by
  rw [coe_B, coe_B, ModularForm.SL_smul_slash, SlashAction.sum_slash]
  congr 1
  have h : ∀ t ∈ nz M, ((ψ (isPrimitiveRoot_zetaN (NeZero.ne M)) (-(t * c))) • (⇑(W M t) : ℍ → ℂ)) ∣[(2 : ℤ)] γ =
      (ψ (isPrimitiveRoot_zetaN (NeZero.ne M)) (-(t * c))) • (⇑(W M (t * ((γ 1 1 : ℤ) : ZMod M))) : ℍ → ℂ) := by
    intro t _
    rw [ModularForm.SL_smul_slash, W_slash M t γ hγ]
  rw [Finset.sum_congr rfl h]
  exact sum_reindex M (fun t => (⇑(W M t) : ℍ → ℂ)) c hγ

theorem D_slash (c : ZMod M) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) :
    (⇑(D M c) : ℍ → ℂ) ∣[(4 : ℤ)] γ = ⇑(D M (c * ((γ 0 0 : ℤ) : ZMod M))) := by
  rw [coe_D, coe_D, ModularForm.SL_smul_slash, SlashAction.sum_slash]
  congr 1
  have h : ∀ t ∈ nz M, ((ψ (isPrimitiveRoot_zetaN (NeZero.ne M)) (-(t * c))) • (⇑(Fform M t) : ℍ → ℂ)) ∣[(4 : ℤ)] γ =
      (ψ (isPrimitiveRoot_zetaN (NeZero.ne M)) (-(t * c))) • (⇑(Fform M (t * ((γ 1 1 : ℤ) : ZMod M))) : ℍ → ℂ) := by
    intro t _
    rw [ModularForm.SL_smul_slash, Fform_slash M t γ hγ]
  rw [Finset.sum_congr rfl h]
  exact sum_reindex M (fun t => (⇑(Fform M t) : ℍ → ℂ)) c hγ
end
end Dubon2026.SourceFunctionField.GammaOne.ToricFourier
