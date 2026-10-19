/-
Copyright 2026 Anthropic, PBC.
Released under Apache 2.0; see ../../Dependencies/AnthropicFLTReuse/LICENSE.
Adapted from anthropics/fermats-last-theorem commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_Ideal_exists_monoidHom_inertia_residueFieldUnits_ker_iff_of_uniformizer.lean.
Modified for Dubon: extract the required dependency closure, use the native namespace,
remove external elaboration macros and linter overrides, and retain default proof limits.
This supplies the finite tame local condition for arithmetic patching -> higher symmetric
power continuation -> Dubon Theorem 2.6 (DUB-17) and Corollary 8.2 (DUB-18).
-/

import Dubon2026.TameInertiaCharacter

namespace Dubon2026.TameKernel

universe u v

section FrobeniusRelation
variable {B : Type u} [CommRing B] {G : Type v} [Group G] [MulSemiringAction G B]
variable (𝔓 : Ideal B)

theorem smul_sub_mul_mem_sq_of_uniformizer {ϖ : B} (hϖP : ϖ ∈ 𝔓)
    (hgen : ∀ x ∈ 𝔓, ∃ y : B, x - ϖ * y ∈ 𝔓 ^ 2) {σ : G} (hσ : σ ∈ 𝔓.inertia G) {t : B}
    (ht : σ • ϖ - ϖ * t ∈ 𝔓 ^ 2) {x : B} (hx : x ∈ 𝔓) : σ • x - t * x ∈ 𝔓 ^ 2 := by
  obtain ⟨y, hy⟩ := hgen x hx
  set p₂ := x - ϖ * y with hp
  have hx' : x = ϖ * y + p₂ := by rw [hp]; ring
  have e : σ • x - t * x = (σ • ϖ - ϖ * t) * (σ • y) + t * ϖ * (σ • y - y) + (σ • p₂ - t * p₂) := by
    conv_lhs => rw [hx']
    rw [smul_add, smul_mul']; ring
  rw [e]
  refine (𝔓 ^ 2).add_mem ((𝔓 ^ 2).add_mem (Ideal.mul_mem_right _ _ ht) ?_) ?_
  · rw [pow_two]; exact Ideal.mul_mem_mul (Ideal.mul_mem_left _ _ hϖP) (hσ y)
  · exact (𝔓 ^ 2).sub_mem (smul_mem_sq_of_mem_inertia 𝔓 hσ hy) (Ideal.mul_mem_left _ _ hy)

theorem smul_mem_sq_of_forall_smul_mem {φ : G} (hφP : ∀ x ∈ 𝔓, φ • x ∈ 𝔓) {z : B} (hz : z ∈ 𝔓 ^ 2) :
    φ • z ∈ 𝔓 ^ 2 := by
  let f : B →+* B := MulSemiringAction.toRingHom G B φ
  have hmap : 𝔓.map f ≤ 𝔓 := by
    rw [Ideal.map_le_iff_le_comap]; intro x hx; exact hφP x hx
  have h2 : (𝔓 ^ 2).map f ≤ 𝔓 ^ 2 := by rw [Ideal.map_pow]; exact Ideal.pow_right_mono hmap 2
  exact h2 (Ideal.mem_map_of_mem f hz)

theorem conj_smul_sub_mul_pow_mem_sq {ϖ : B} (hϖP : ϖ ∈ 𝔓)
    (hgen : ∀ x ∈ 𝔓, ∃ y : B, x - ϖ * y ∈ 𝔓 ^ 2) {σ : G} (hσ : σ ∈ 𝔓.inertia G) {t : B}
    (ht : σ • ϖ - ϖ * t ∈ 𝔓 ^ 2) {q : ℕ} {φ : G} (hφ : ∀ x : B, φ • x - x ^ q ∈ 𝔓)
    (hφP : ∀ x ∈ 𝔓, φ • x ∈ 𝔓) (hφP' : ∀ x ∈ 𝔓, φ⁻¹ • x ∈ 𝔓) :
    (φ * σ * φ⁻¹) • ϖ - ϖ * t ^ q ∈ 𝔓 ^ 2 := by
  set ϖ₁ := φ⁻¹ • ϖ with hϖ₁
  have hϖ₁P : ϖ₁ ∈ 𝔓 := hφP' ϖ hϖP
  have h1 : σ • ϖ₁ - t * ϖ₁ ∈ 𝔓 ^ 2 := smul_sub_mul_mem_sq_of_uniformizer 𝔓 hϖP hgen hσ ht hϖ₁P
  have h2 : φ • (σ • ϖ₁ - t * ϖ₁) ∈ 𝔓 ^ 2 := smul_mem_sq_of_forall_smul_mem 𝔓 hφP h1
  have e1 : (φ * σ * φ⁻¹) • ϖ = φ • (σ • ϖ₁) := by rw [hϖ₁, mul_smul, mul_smul]
  have e2 : φ • (σ • ϖ₁ - t * ϖ₁) = (φ * σ * φ⁻¹) • ϖ - (φ • t) * ϖ := by
    rw [smul_sub, smul_mul', e1, hϖ₁, smul_inv_smul]
  rw [e2] at h2

  have h3 : (φ • t) * ϖ - ϖ * t ^ q ∈ 𝔓 ^ 2 := by
    have : (φ • t) * ϖ - ϖ * t ^ q = (φ • t - t ^ q) * ϖ := by ring
    rw [this, pow_two]; exact Ideal.mul_mem_mul (hφ t) hϖP
  have : (φ * σ * φ⁻¹) • ϖ - ϖ * t ^ q = ((φ * σ * φ⁻¹) • ϖ - (φ • t) * ϖ) + ((φ • t) * ϖ - ϖ * t ^ q) := by ring
  rw [this]; exact (𝔓 ^ 2).add_mem h2 h3

theorem exists_tameChar [𝔓.IsMaximal] [Finite (B ⧸ 𝔓)] {ϖ : B} (hϖP : ϖ ∈ 𝔓)
    (hgen : ∀ x ∈ 𝔓, ∃ y : B, x - ϖ * y ∈ 𝔓 ^ 2) (hreg : ∀ c : B, c * ϖ ∈ 𝔓 ^ 2 → c ∈ 𝔓) :
    ∃ θ : 𝔓.inertia G →* (B ⧸ 𝔓)ˣ,
      (∀ (σ : 𝔓.inertia G) (t : B), ((θ σ : (B ⧸ 𝔓)ˣ) : B ⧸ 𝔓) = Ideal.Quotient.mk 𝔓 t ↔
        (σ : G) • ϖ - ϖ * t ∈ 𝔓 ^ 2) ∧
      (∀ σ : 𝔓.inertia G, θ σ = 1 ↔ ∀ x : B, (σ : G) • x - x ∈ 𝔓 ^ 2) ∧ IsCyclic θ.range := by
  refine ⟨tameChar 𝔓 hϖP hgen hreg, fun σ t => ?_, fun σ => tameChar_eq_one_iff_forall 𝔓 hϖP hgen hreg σ,
    isCyclic_range_tameChar 𝔓 hϖP hgen hreg⟩
  rw [tameChar_apply, Ideal.Quotient.eq]
  constructor
  · intro h
    have hs := tameCoeff_spec 𝔓 hϖP hgen σ.2
    have : (σ : G) • ϖ - ϖ * t = ((σ : G) • ϖ - ϖ * tameCoeff 𝔓 hϖP hgen σ.2) + ϖ * (tameCoeff 𝔓 hϖP hgen σ.2 - t) := by
      ring
    rw [this]
    refine (𝔓 ^ 2).add_mem hs ?_
    rw [pow_two]; exact Ideal.mul_mem_mul hϖP h
  · intro h
    exact tameCoeff_unique 𝔓 hreg (tameCoeff_spec 𝔓 hϖP hgen σ.2) h

end FrobeniusRelation


end Dubon2026.TameKernel
