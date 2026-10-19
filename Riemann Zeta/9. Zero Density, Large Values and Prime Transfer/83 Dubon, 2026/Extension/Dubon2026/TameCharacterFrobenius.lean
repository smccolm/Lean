import Dubon2026.TameFrobeniusRelation

/-! The finite tame character intertwines actual Frobenius conjugation with the
residue-cardinality power. This is the relation required by ramified auxiliary
deformations in the arithmetic patching chain for Dubon Theorem 2.6. -/

namespace Dubon2026.TameKernel

variable {B G : Type*} [CommRing B] [Group G] [MulSemiringAction G B]
  (P : Ideal B)

theorem inertia_conjugate_mem (φ σ : G) (hσ : σ ∈ P.inertia G)
    (hφP : ∀ x ∈ P, φ • x ∈ P) : φ * σ * φ⁻¹ ∈ P.inertia G := by
  intro x
  have h := hφP _ (hσ (φ⁻¹ • x))
  change (φ * σ * φ⁻¹) • x - x ∈ P
  rw [mul_smul, mul_smul]
  simpa only [smul_sub, smul_inv_smul] using h

theorem tame_character_frobenius {ϖ : B} (hϖP : ϖ ∈ P)
    (hgen : ∀ x ∈ P, ∃ y : B, x - ϖ * y ∈ P ^ 2)
    (θ : P.inertia G →* (B ⧸ P)ˣ)
    (hθ : ∀ (σ : P.inertia G) (t : B),
      (θ σ : B ⧸ P) = Ideal.Quotient.mk P t ↔ (σ : G) • ϖ - ϖ * t ∈ P ^ 2)
    (q : ℕ) (φ : G) (hφ : ∀ x : B, φ • x - x ^ q ∈ P)
    (hφP : ∀ x ∈ P, φ • x ∈ P) (hφP' : ∀ x ∈ P, φ⁻¹ • x ∈ P)
    (σ : P.inertia G) :
    θ ⟨φ * (σ : G) * φ⁻¹, inertia_conjugate_mem P φ σ σ.property hφP⟩ = θ σ ^ q := by
  obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (θ σ : B ⧸ P)
  have hcoeff := (hθ σ t).mp ht.symm
  have hconj := conj_smul_sub_mul_pow_mem_sq P hϖP hgen σ.property hcoeff hφ hφP hφP'
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, ← ht, ← map_pow]
  exact (hθ _ _).mpr hconj

end Dubon2026.TameKernel
