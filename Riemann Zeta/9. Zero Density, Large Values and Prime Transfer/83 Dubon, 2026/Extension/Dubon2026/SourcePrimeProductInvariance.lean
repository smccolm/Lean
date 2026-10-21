import Dubon2026.HeckePrimeOrbits

/-! DUB-17/18 -> finite original function-field extension -> monic relations.
The analytic conjugate polynomial must be SL2Z invariant. Reuse the original
proved Hecke matrices, integral Gamma0 transitions and finite residue permutation.
The only new finite-product argument replaces the existing additive sum argument.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane Polynomial
open HeckePrimeReindex
open scoped MatrixGroups

private theorem invariant_factor {F : ℍ → ℂ}
    (hF : ∀ (γ : SL(2, ℤ)) (τ : ℍ), F (γ • τ) = F τ)
    {A B : GL (Fin 2) ℝ} {σ : SL(2, ℤ)}
    (h : ∃ δ : SL(2, ℤ), δ ∈ Gamma0 1 ∧ A * mapGL ℝ σ = mapGL ℝ δ * B) (τ : ℍ) :
    F (A • σ • τ) = F (B • τ) := by
  obtain ⟨δ, -, he⟩ := h
  change F (A • (mapGL ℝ σ) • τ) = _
  rw [← mul_smul, he, mul_smul]
  exact hF δ (B • τ)

private theorem prod_ite_swap_eq {p : ℕ} {M : Type*} [CommMonoid M]
    (g : Fin p → M) (a : M) (φ : Fin p → Fin p) (hφ : Function.Bijective φ)
    (b : Fin p) (P : Fin p → Prop) [DecidablePred P] (hP : ∀ i, P i ↔ i = b) :
    (∏ x, if P x then a else g (φ x)) * g (φ b) = (∏ x, g x) * a := by
  classical
  have hbij : ∏ x, g (φ x) = ∏ x, g x :=
    (Equiv.ofBijective φ hφ).prod_comp g
  rw [← hbij, ← Finset.mul_prod_erase _ _ (Finset.mem_univ b),
    ← Finset.mul_prod_erase _ (fun x => g (φ x)) (Finset.mem_univ b)]
  rw [if_pos ((hP b).mpr rfl)]
  have he : ∏ x ∈ Finset.univ.erase b, (if P x then a else g (φ x)) =
      ∏ x ∈ Finset.univ.erase b, g (φ x) := by
    apply Finset.prod_congr rfl
    intro x hx
    rw [if_neg (fun h => (Finset.mem_erase.mp hx).1 ((hP x).mp h))]
  rw [he]
  ac_rfl

/-- The literal analytic prime conjugate product is invariant under the original modular group. -/
theorem prime_conjugate_product_invariant (p : ℕ) [NeZero p] (hp : p.Prime)
    (F : ℍ → ℂ) (hF : ∀ (γ : SL(2, ℤ)) (τ : ℍ), F (γ • τ) = F τ)
    (σ : SL(2, ℤ)) (τ : ℍ) :
    (X - C (F (heckeTriangularMatrix p 1 0 • σ • τ))) *
        ∏ b : Fin p, (X - C (F (heckeTriangularMatrix 1 p b.val • σ • τ))) =
      (X - C (F (heckeTriangularMatrix p 1 0 • τ))) *
        ∏ b : Fin p, (X - C (F (heckeTriangularMatrix 1 p b.val • τ))) := by
  classical
  have hσ : σ ∈ Gamma0 1 := Gamma0_mem.mpr (Subsingleton.elim _ _)
  by_cases hC : (p : ℤ) ∣ σ.val 1 0
  · rw [invariant_factor hF (heckePrime_lower_div_factor (Nat.coprime_one_right p) σ hσ hC)]
    congr 1
    refine Finset.prod_equiv
      (Equiv.ofBijective _ (Finite.injective_iff_bijective.mp
        (moebiusFin_injective p hp σ.val σ.prop)))
      (fun _ => ⟨fun _ => Finset.mem_univ _, fun _ => Finset.mem_univ _⟩) ?_
    intro b _
    rw [invariant_factor hF (heckePrime_upper_factor hp σ hσ b
      (not_dvd_topLeft_add_of_dvd_botLeft p hp σ.val
        (sl2z_fin_two_det_eq_one σ) hC b.val))]
    rfl
  · haveI : Fact p.Prime := ⟨hp⟩
    let b₀ : Fin p := ⟨(-(σ.val 0 0 : ZMod p) * (σ.val 1 0 : ZMod p)⁻¹).val,
      ZMod.val_lt _⟩
    have hb₀ : (p : ℤ) ∣ σ.val 0 0 + b₀.val * σ.val 1 0 :=
      dvd_topLeft_add_canonicalIndex p hp σ.val
        (fun h => hC ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h))
    have hupper (b : Fin p) :
        X - C (F (heckeTriangularMatrix 1 p b.val • σ • τ)) =
          if (p : ℤ) ∣ σ.val 0 0 + b.val * σ.val 1 0 then
            X - C (F (heckeTriangularMatrix p 1 0 • τ)) else
            X - C (F (heckeTriangularMatrix 1 p (moebiusFin p hp σ.val b).val • τ)) := by
      split_ifs with h
      · rw [invariant_factor hF (heckePrime_upper_pole_factor σ hσ b h)]
      · rw [invariant_factor hF (heckePrime_upper_factor hp σ hσ b h)]
    have hlower : F (heckeTriangularMatrix p 1 0 • σ • τ) =
        F (heckeTriangularMatrix 1 p (moebiusFin p hp σ.val b₀).val • τ) := by
      have hm : (moebiusFin p hp σ.val b₀).val =
          ((σ.val 1 1 : ZMod p) * (σ.val 1 0 : ZMod p)⁻¹).val := by
        simp only [moebiusFin, (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hb₀, if_true]
      rw [hm]
      exact invariant_factor hF (heckePrime_lower_factor hp σ hσ hC) τ
    simp_rw [hupper]
    rw [hlower, mul_comm (X - C _), mul_comm (X - C _)]
    exact prod_ite_swap_eq
      (fun b : Fin p => X - C (F (heckeTriangularMatrix 1 p b.val • τ)))
      (X - C (F (heckeTriangularMatrix p 1 0 • τ)))
      (moebiusFin p hp σ.val)
      (Finite.injective_iff_bijective.mp (moebiusFin_injective p hp σ.val σ.prop)) b₀ _
      (dvd_topLeft_add_iff_eq_canonicalIndex p hp σ.val σ.prop b₀ hb₀)

end
end Dubon2026.SourceFunctionField
