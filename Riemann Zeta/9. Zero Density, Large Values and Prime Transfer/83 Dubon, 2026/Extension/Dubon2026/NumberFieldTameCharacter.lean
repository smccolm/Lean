import Dubon2026.NumberFieldTameWild
import Dubon2026.DedekindTameUniformizer
import Dubon2026.TameCharacterFrobenius

/-! The original number-field prime supplies the uniformizer and finite residue field.
The actual tame character has residue-characteristic-power kernel. This removes the
uniformizer and wild-order inputs on the DUB-17 auxiliary local deformation chain. -/

namespace Dubon2026

open IsDedekindDomain
open scoped NumberField

variable {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F))

theorem numberField_wild_order_prime_power (p : ℕ) (hp : p.Prime)
    (hpw : (p : 𝓞 F) ∈ w.asIdeal) (σ : Gal(F/ℚ))
    (hσ : σ ∈ w.asIdeal.inertia Gal(F/ℚ))
    (hσ₂ : ∀ x : 𝓞 F, σ • x - x ∈ w.asIdeal ^ 2) :
    ∃ a : ℕ, orderOf σ = p ^ a := by
  have hvp : w.valuation F (p : F) < 1 := by
    rw [← map_natCast (algebraMap (𝓞 F) F) p, HeightOneSpectrum.valuation_of_algebraMap]
    exact (w.intValuation_lt_one_iff_mem _).mpr hpw
  exact Wild.IsWild.orderOf_eq_pow _
    (heightOne_isWild_of_forall_smul_sub_mem_sq w hσ hσ₂) hp hvp (orderOf_pos σ)

theorem numberField_exists_tame_character (p : ℕ) (hp : p.Prime)
    (hpw : (p : 𝓞 F) ∈ w.asIdeal) :
    ∃ θ : w.asIdeal.inertia Gal(F/ℚ) →* (𝓞 F ⧸ w.asIdeal)ˣ,
      (∀ σ, θ σ = 1 ↔ ∀ x : 𝓞 F, (σ : Gal(F/ℚ)) • x - x ∈ w.asIdeal ^ 2) ∧
      IsCyclic θ.range ∧ IsPGroup p θ.ker ∧
      ∀ (φ : Gal(F/ℚ)), (∀ x : 𝓞 F, φ • x - x ^ p ∈ w.asIdeal) →
        ∀ (hφP : ∀ x ∈ w.asIdeal, φ • x ∈ w.asIdeal),
        (∀ x ∈ w.asIdeal, φ⁻¹ • x ∈ w.asIdeal) → ∀ (σ : w.asIdeal.inertia Gal(F/ℚ)),
        θ ⟨φ * (σ : Gal(F/ℚ)) * φ⁻¹,
          TameKernel.inertia_conjugate_mem w.asIdeal φ σ σ.property hφP⟩ = θ σ ^ p := by
  obtain ⟨ϖ, hϖ, hgen, hreg⟩ := heightOne_exists_tame_uniformizer w
  obtain ⟨θ, hchar, hker, hcyc⟩ := TameKernel.exists_tameChar
    (G := Gal(F/ℚ)) w.asIdeal hϖ hgen hreg
  refine ⟨θ, hker, hcyc, ?_, ?_⟩
  · intro σ
    have hσ₂ := (hker σ.val).mp σ.property
    obtain ⟨a, ha⟩ := numberField_wild_order_prime_power w p hp hpw
      σ.val.val σ.val.property hσ₂
    refine ⟨a, Subtype.ext (Subtype.ext ?_)⟩
    change σ.val.val ^ (p ^ a) = 1
    rw [← ha]
    exact pow_orderOf_eq_one _
  · intro φ hφ hφP hφP' σ
    exact TameKernel.tame_character_frobenius w.asIdeal hϖ hgen θ hchar p φ hφ hφP hφP' σ

end Dubon2026
