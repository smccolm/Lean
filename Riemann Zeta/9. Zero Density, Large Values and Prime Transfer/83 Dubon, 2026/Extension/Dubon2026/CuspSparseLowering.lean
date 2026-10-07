import Dubon2026.CuspLowerFunction

/-! # Genuine Gamma0 level lowering from sparse Fourier support -/

namespace Dubon2026

open Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane
open scoped MatrixGroups ModularForm

noncomputable section

/-- Period one of an actual analytic function gives slash invariance under every integral translation. -/
theorem slash_T_zpow_of_period (k : ℤ) (F : ℍ → ℂ)
    (hF : ∀ τ : ℍ, F ((1 : ℝ) +ᵥ τ) = F τ) (j : ℤ) :
    F ∣[k] mapGL ℝ (ModularGroup.T ^ j) = F := by
  funext τ
  have hp : Function.Periodic (fun x : ℝ => F (x +ᵥ τ)) 1 := by
    intro x
    change F ((x + 1) +ᵥ τ) = F (x +ᵥ τ)
    rw [add_comm x 1, add_vadd]
    exact hF (x +ᵥ τ)
  have he : F ((j : ℝ) +ᵥ τ) = F τ := by simpa using hp.int_mul_eq j
  change ((F ∣[k] (ModularGroup.T ^ j)) τ) = F τ
  rw [ModularForm.SL_slash_apply, modular_T_zpow_smul, ModularGroup.denom_apply]
  simpa [ModularGroup.coe_T_zpow, -map_zpow] using he

/-- The literal inverse dilation of a sparse Gamma0 form is invariant at the divided level. -/
theorem levelLowerFun_sparse_slash {N d : ℕ} [NeZero N] [NeZero d]
    (hd : d ∣ N) (k : ℤ) (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (hf : ∀ n, ¬d ∣ n → cuspCoefficients f n = 0)
    (δ : SL(2, ℤ)) (hδ : δ ∈ Gamma0 (N / d)) :
    levelLowerFun d k f ∣[k] mapGL ℝ δ = levelLowerFun d k f := by
  have hp : ∀ τ : ℍ, levelLowerFun d k f ((1 : ℝ) +ᵥ τ) = levelLowerFun d k f τ := by
    intro τ
    simp only [levelLowerFun_apply]
    exact cusp_sparse_rescaling_period d f hf τ
  obtain ⟨i, j, γ, hγ, he, _⟩ := exists_T_levelRaiseConj_T_factor d N hd δ hδ
  have hdγ : (d : ℤ) ∣ γ.val 1 0 :=
    (Int.natCast_dvd_natCast.mpr hd).trans
      ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hγ))
  have hc : levelLowerFun d k f ∣[k] mapGL ℝ
      (levelRaiseConjOfDvd d γ hdγ) = levelLowerFun d k f := by
    apply levelRaiseFun_injective d k
    rw [levelRaiseFun_slash_conjugate, levelRaiseFun_levelLowerFun]
    exact f.slash_action_eq' _ ⟨γ, hγ, rfl⟩
  rw [he, map_mul, map_mul, SlashAction.slash_mul, SlashAction.slash_mul,
    slash_T_zpow_of_period k _ hp i, hc, slash_T_zpow_of_period k _ hp j]

/-- The genuine lower-level cusp form f(z/d), constructed from its actual sparse q-expansion. -/
def cuspSparseLower {N d : ℕ} [NeZero N] [NeZero d] (hd : d ∣ N) (k : ℤ)
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (hf : ∀ n, ¬d ∣ n → cuspCoefficients f n = 0) :
    CuspForm ((Gamma0 (N / d)).map (mapGL ℝ)) k := by
  letI : NeZero (N / d) := ⟨(Nat.div_pos
    (Nat.le_of_dvd (Nat.pos_of_neZero N) hd) (Nat.pos_of_neZero d)).ne'⟩
  exact {
    toFun := levelLowerFun d k f
    slash_action_eq' := by
      rintro γ ⟨δ, hδ, rfl⟩
      exact levelLowerFun_sparse_slash hd k f hf δ hδ
    holo' := levelLowerFun_holomorphic d k f f.holo'
    zero_at_cusps' hc := levelLowerFun_zero_at_cusps d f hc
  }

/-- Evaluation of the constructed cusp form is the actual divided argument. -/
theorem cuspSparseLower_apply {N d : ℕ} [NeZero N] [NeZero d] (hd : d ∣ N) (k : ℤ)
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (hf : ∀ n, ¬d ∣ n → cuspCoefficients f n = 0) (τ : ℍ) :
    cuspSparseLower hd k f hf τ = f (heckeUpperPoint d 0 τ) :=
  levelLowerFun_apply d k f τ

/-- The actual lower-level cusp form recovers f under the genuine level-raising map. -/
theorem cuspSparseLower_levelRaise {N d : ℕ} [NeZero N] [NeZero d] (hd : d ∣ N) (k : ℤ)
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (hf : ∀ n, ¬d ∣ n → cuspCoefficients f n = 0) :
    levelRaiseFun d k (cuspSparseLower hd k f hf) = f :=
  levelRaiseFun_levelLowerFun d k f

end
end Dubon2026
