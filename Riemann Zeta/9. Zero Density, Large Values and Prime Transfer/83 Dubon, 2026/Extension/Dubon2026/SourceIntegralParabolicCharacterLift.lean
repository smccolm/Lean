import Dubon2026.SourceIntegralCharacterModularBridge

/-! DUB-17/18 -> original all-weight association -> Gamma1 Picard/H1
-> Abel-Jacobi -> unitary multiplier logarithms -> integral parabolic-character
lifting. Adapted from the Apache-2.0 scope-796 primary at revision
6e837e75355538c7f80bab5b956861e86c4eacc2. Reuse the repository
SourceParabolic.classification and the audited actual projective free-product
equivalence. The theorem uses literal squared-trace-four vanishing, all finite
indices and all natural moduli, including zero. It assumes no lifting theorem. -/
namespace Dubon2026.SourceIntegralCharacterLift
noncomputable section
open Subgroup
open scoped MatrixGroups
open Matrix.SpecialLinearGroup ModularGroup

/-- Every finite-index integral modular subgroup admits an integral parabolic lift
of a finite-valued parabolic character that vanishes on finite-order elements. -/
theorem exists_int_lift (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (n : ℕ)
    (φ : Additive Γ →+ ZMod n)
    (hpar : ∀ γ : Γ, γ.val.val.trace ^ 2 = 4 → φ (Additive.ofMul γ) = 0)
    (hφ : ∀ γ : Γ, IsOfFinOrder γ → φ (Additive.ofMul γ) = 0) :
    ∃ x : Additive Γ →+ ℤ,
      (∀ γ : Γ, γ.val.val.trace ^ 2 = 4 → x (Additive.ofMul γ) = 0) ∧
      (Int.castAddHom (ZMod n)).comp x = φ := by
  classical
  let e := SourceModularFreeProduct.mulEquiv
  have he0 := SourceModularFreeProduct.mulEquiv_of_zero
  have he1 := SourceModularFreeProduct.mulEquiv_of_one

  let ρ : SL(2, ℤ) →* G23 := e.symm.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))
  have hρ : ∀ z, ρ z = e.symm (QuotientGroup.mk z) := fun z => rfl
  have hker : ∀ z, ρ z = 1 ↔ z ∈ Subgroup.center SL(2, ℤ) := by
    intro z
    rw [hρ, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  have hsurj : Function.Surjective ρ :=
    e.symm.surjective.comp (QuotientGroup.mk'_surjective _)
  have hT : ρ T = tP := by
    rw [hρ, MulEquiv.symm_apply_eq, tP, SourceCuspCorrection.τ, SourceCuspCorrection.sA, SourceCuspCorrection.uA, map_mul, he0, he1, ← QuotientGroup.mk_mul, QuotientGroup.eq,
      ← mul_assoc S, S_mul_S, neg_one_mul, mul_neg, inv_mul_cancel]
    exact neg_one_mem_center

  let H : Subgroup G23 := Γ.map ρ
  haveI : H.FiniteIndex := ⟨fun h0 =>
    Subgroup.FiniteIndex.index_ne_zero (H := Γ) (Nat.eq_zero_of_zero_dvd (h0 ▸ Γ.index_map_dvd hsurj))⟩
  let ρΓ : Γ →* H := ρ.subgroupMap Γ
  have hρΓ : ∀ γ : Γ, ((ρΓ γ : H) : G23) = ρ γ := fun γ => rfl
  let ρΓa : Additive Γ →+ Additive H := MonoidHom.toAdditive ρΓ
  have hρΓa : ∀ γ : Γ, ρΓa (Additive.ofMul γ) = Additive.ofMul (ρΓ γ) := fun γ => rfl
  have hρΓa_surj : Function.Surjective ρΓa := ρ.subgroupMap_surjective Γ

  have hkerle : ρΓa.ker ≤ φ.ker := by
    refine Additive.ofMul.surjective.forall.mpr ?_
    intro γ hγ
    rw [AddMonoidHom.mem_ker] at hγ ⊢
    apply hφ γ
    have h1 : ρ γ = 1 := by
      rw [← hρΓ]
      have : ρΓ γ = 1 := hγ
      rw [this]; rfl
    have h2 : IsOfFinOrder (γ : SL(2, ℤ)) :=
      isOfFinOrder_of_rho ρ hker (by rw [h1]; exact IsOfFinOrder.one)
    exact Submonoid.isOfFinOrder_coe.mp h2
  let ψ : Additive H →+ ZMod n := ρΓa.liftOfSurjective hρΓa_surj ⟨φ, hkerle⟩
  have hψ : ∀ γ : Γ, ψ (Additive.ofMul (ρΓ γ)) = φ (Additive.ofMul γ) := by
    intro γ
    rw [← hρΓa]
    exact AddMonoidHom.liftOfRightInverse_comp_apply ρΓa _ _ ⟨φ, hkerle⟩
      (Additive.ofMul γ)
  have hψ' : ∀ (P : G23) (hP : P ∈ H), ∃ γ : Γ, ρ γ = P ∧
      ψ (Additive.ofMul ⟨P, hP⟩) = φ (Additive.ofMul γ) := by
    intro P hP
    obtain ⟨γ, hγ, hγP⟩ := Subgroup.mem_map.mp hP
    refine ⟨⟨γ, hγ⟩, hγP, ?_⟩
    have : (⟨P, hP⟩ : H) = ρΓ ⟨γ, hγ⟩ := Subtype.ext hγP.symm
    rw [this]
    exact hψ ⟨γ, hγ⟩

  have hψfac : ∀ (i : Fin 2) (x : M23 i) (g : G23) (h : g * Monoid.CoprodI.of x * g⁻¹ ∈ H),
      ψ (Additive.ofMul ⟨g * Monoid.CoprodI.of x * g⁻¹, h⟩) = 0 := by
    intro i x g h
    obtain ⟨γ, hγ, hval⟩ := hψ' _ h
    rw [hval]
    apply hφ γ
    exact Submonoid.isOfFinOrder_coe.mp (isOfFinOrder_of_rho_eq_conj_of ρ hker x g hγ)

  have hψpar : ∀ (g : G23) (k : ℤ) (h : g * tP ^ k * g⁻¹ ∈ H),
      ψ (Additive.ofMul ⟨g * tP ^ k * g⁻¹, h⟩) = 0 := by
    intro g k h
    obtain ⟨γ, hγ, hval⟩ := hψ' _ h
    rw [hval]
    exact hpar γ (trace_sq_of_rho_eq_conj_tP_zpow ρ hker hT hsurj hγ)

  obtain ⟨χ, hχ, -⟩ := exists_char_comp_eq_of_forall_conj_of H (Int.castAddHom (ZMod n))
    ZMod.intCast_surjective ψ hψfac

  have hdvd : ∀ (g : G23) (k : ℤ) (h : g * tP ^ k * g⁻¹ ∈ H),
      (n : ℤ) ∣ χ (Additive.ofMul ⟨_, h⟩) := by
    intro g k h
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).mp
    have := DFunLike.congr_fun hχ (Additive.ofMul ⟨_, h⟩)
    rw [AddMonoidHom.comp_apply, hψpar g k h] at this
    exact this

  obtain ⟨φ', hφ'⟩ := exists_sub_smul_apply_conj_zpow_eq_zero H χ n hdvd

  let x : Additive Γ →+ ℤ := (χ - (n : ℤ) • φ').comp ρΓa
  have hxpar : ∀ γ : Γ, γ.val.val.trace ^ 2 = 4 → x (Additive.ofMul γ) = 0 := by
    intro γ hγ
    obtain ⟨g, k, hgk⟩ := exists_rho_eq_conj_tP_zpow ρ hker hT hγ
    show (χ - (n : ℤ) • φ') (ρΓa (Additive.ofMul γ)) = 0
    have hmem : g * tP ^ k * g⁻¹ ∈ H := by rw [← hgk]; exact (ρΓ γ).2
    rw [hρΓa]
    have : ρΓ γ = ⟨g * tP ^ k * g⁻¹, hmem⟩ := Subtype.ext hgk
    rw [this]
    exact hφ' g k hmem
  refine ⟨x, hxpar, ?_⟩
  refine AddMonoidHom.ext (Additive.ofMul.surjective.forall.mpr ?_)
  intro γ
  show (Int.castAddHom (ZMod n)) ((χ - (n : ℤ) • φ') (ρΓa (Additive.ofMul γ)))
    = φ (Additive.ofMul γ)
  rw [← hψ γ, hρΓa, AddMonoidHom.sub_apply, map_sub, AddMonoidHom.zsmul_apply, map_zsmul]
  have h1 : (Int.castAddHom (ZMod n)) (χ (Additive.ofMul (ρΓ γ))) = ψ (Additive.ofMul (ρΓ γ)) :=
    DFunLike.congr_fun hχ _
  rw [h1, sub_eq_self, natCast_zsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul]

end
end Dubon2026.SourceIntegralCharacterLift
