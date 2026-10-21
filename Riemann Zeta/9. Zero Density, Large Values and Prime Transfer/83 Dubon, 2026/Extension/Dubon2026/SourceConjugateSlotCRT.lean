import Dubon2026.SourceConjugateSlotCount

/-! DUB-17/18 -> numerical modular genus -> general composite j-map
degree -> explicit minimal-polynomial conjugates. These counts identify
the primitive triangular conjugate list with the already proved level
factor dedekindPsi. The list is needed to prove the degree and divisor
generation by induction; no polynomial or geometric degree is assumed.
Selected from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ModularCurve_minpoly_jqNModC_map_eq_prod_slots.lean.
-/
namespace Dubon2026.SourceFunctionField.ConjugateSlots
noncomputable section
open SourceLevelProjective

theorem slotAt_mul (M M' d₁ d₂ : ℕ) (hM : M ≠ 0) (hM' : M' ≠ 0)
    (hco : Nat.Coprime M M') (hd₁ : d₁ ∣ M) (hd₂ : d₂ ∣ M') :
    slotAt (M * M') (d₁ * d₂) = slotAt M d₁ * slotAt M' d₂ := by
  have hd₁0 : 0 < d₁ :=
    Nat.pos_of_ne_zero (by rintro rfl; exact hM (Nat.eq_zero_of_zero_dvd hd₁))
  have hd₂0 : 0 < d₂ :=
    Nat.pos_of_ne_zero (by rintro rfl; exact hM' (Nat.eq_zero_of_zero_dvd hd₂))
  have hcod : Nat.Coprime d₁ d₂ :=
    Nat.Coprime.coprime_dvd_left hd₁ (Nat.Coprime.coprime_dvd_right hd₂ hco)
  have hxM : M / d₁ ∣ M := ⟨d₁, (Nat.div_mul_cancel hd₁).symm⟩
  have hyM' : M' / d₂ ∣ M' := ⟨d₂, (Nat.div_mul_cancel hd₂).symm⟩
  have hxy : (M * M') / (d₁ * d₂) = (M / d₁) * (M' / d₂) :=
    (Nat.div_mul_div_comm hd₁ hd₂).symm
  have hyd₁ : Nat.Coprime (M' / d₂) d₁ :=
    Nat.Coprime.coprime_dvd_left hyM' (Nat.Coprime.coprime_dvd_right hd₁ hco.symm)
  have hxd₂ : Nat.Coprime (M / d₁) d₂ :=
    Nat.Coprime.coprime_dvd_left hxM (Nat.Coprime.coprime_dvd_right hd₂ hco)
  have hgEq : Nat.gcd ((M * M') / (d₁ * d₂)) (d₁ * d₂) =
      Nat.gcd (M / d₁) d₁ * Nat.gcd (M' / d₂) d₂ := by
    rw [hxy, hcod.gcd_mul, hyd₁.gcd_mul_right_cancel, hxd₂.gcd_mul_left_cancel]
  have hg₁g : Nat.gcd (M / d₁) d₁ ∣ Nat.gcd ((M * M') / (d₁ * d₂)) (d₁ * d₂) := by
    rw [hgEq]
    exact dvd_mul_right _ _
  have hg₂g : Nat.gcd (M' / d₂) d₂ ∣ Nat.gcd ((M * M') / (d₁ * d₂)) (d₁ * d₂) := by
    rw [hgEq]
    exact dvd_mul_left _ _
  have hgg : Nat.gcd ((M * M') / (d₁ * d₂)) (d₁ * d₂) ∣
      Nat.gcd (M / d₁) d₁ * Nat.gcd (M' / d₂) d₂ := dvd_of_eq hgEq
  have hfwd : ∀ b : ℕ, Nat.gcd (Nat.gcd ((M * M') / (d₁ * d₂)) b) (d₁ * d₂) = 1 →
      Nat.gcd (Nat.gcd (M / d₁) (b % d₁)) d₁ = 1 ∧
        Nat.gcd (Nat.gcd (M' / d₂) (b % d₂)) d₂ = 1 := by
    intro b hb
    rw [slotCond_iff] at hb
    constructor
    · rw [slotCond_iff, slotCond_mod_iff]
      exact Nat.Coprime.coprime_dvd_left hg₁g hb
    · rw [slotCond_iff, slotCond_mod_iff]
      exact Nat.Coprime.coprime_dvd_left hg₂g hb
  have hbwd : ∀ b₁ b₂ k : ℕ, Nat.gcd (Nat.gcd (M / d₁) b₁) d₁ = 1 →
      Nat.gcd (Nat.gcd (M' / d₂) b₂) d₂ = 1 → k ≡ b₁ [MOD d₁] → k ≡ b₂ [MOD d₂] →
      Nat.gcd (Nat.gcd ((M * M') / (d₁ * d₂)) k) (d₁ * d₂) = 1 := by
    intro b₁ b₂ k h₁ h₂ hk₁ hk₂
    rw [slotCond_iff] at h₁ h₂ ⊢
    have hc₁ : Nat.Coprime (Nat.gcd (M / d₁) d₁) k := by
      unfold Nat.Coprime
      rw [gcd_eq_of_modEq (hk₁.of_dvd (Nat.gcd_dvd_right (M / d₁) d₁))]
      exact h₁
    have hc₂ : Nat.Coprime (Nat.gcd (M' / d₂) d₂) k := by
      unfold Nat.Coprime
      rw [gcd_eq_of_modEq (hk₂.of_dvd (Nat.gcd_dvd_right (M' / d₂) d₂))]
      exact h₂
    exact Nat.Coprime.coprime_dvd_left hgg (Nat.coprime_mul_iff_left.mpr ⟨hc₁, hc₂⟩)
  unfold slotAt
  rw [← Finset.card_product]
  refine Finset.card_bij' (fun b _ => (b % d₁, b % d₂))
    (fun q _ => (Nat.chineseRemainder hcod q.1 q.2 : ℕ)) ?_ ?_ ?_ ?_
  · intro b hb
    obtain ⟨hbr, hbc⟩ := Finset.mem_filter.mp hb
    obtain ⟨h₁, h₂⟩ := hfwd b hbc
    exact Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt b hd₁0), h₁⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt b hd₂0), h₂⟩⟩
  · intro q hq
    obtain ⟨hq₁, hq₂⟩ := Finset.mem_product.mp hq
    have hcrt := (Nat.chineseRemainder hcod q.1 q.2).prop
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
      (Nat.chineseRemainder_lt_mul hcod q.1 q.2 hd₁0.ne' hd₂0.ne'), ?_⟩
    exact hbwd q.1 q.2 _ (Finset.mem_filter.mp hq₁).2 (Finset.mem_filter.mp hq₂).2
      hcrt.1 hcrt.2
  · intro b hb
    have hb' : b < d₁ * d₂ := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
    have hcrt := (Nat.chineseRemainder hcod (b % d₁) (b % d₂)).prop
    have h₁ : (Nat.chineseRemainder hcod (b % d₁) (b % d₂) : ℕ) ≡ b [MOD d₁] :=
      hcrt.1.trans (Nat.mod_modEq b d₁)
    have h₂ : (Nat.chineseRemainder hcod (b % d₁) (b % d₂) : ℕ) ≡ b [MOD d₂] :=
      hcrt.2.trans (Nat.mod_modEq b d₂)
    exact ((Nat.modEq_and_modEq_iff_modEq_mul hcod).mp ⟨h₁, h₂⟩).eq_of_lt_of_lt
      (Nat.chineseRemainder_lt_mul hcod _ _ hd₁0.ne' hd₂0.ne') hb'
  · intro q hq
    obtain ⟨hq₁, hq₂⟩ := Finset.mem_product.mp hq
    have hb₁ : q.1 < d₁ := Finset.mem_range.mp (Finset.mem_filter.mp hq₁).1
    have hb₂ : q.2 < d₂ := Finset.mem_range.mp (Finset.mem_filter.mp hq₂).1
    have hcrt := (Nat.chineseRemainder hcod q.1 q.2).prop
    have h₁ : (Nat.chineseRemainder hcod q.1 q.2 : ℕ) % d₁ = q.1 := by
      have h' : (Nat.chineseRemainder hcod q.1 q.2 : ℕ) % d₁ = q.1 % d₁ := hcrt.1
      rw [h', Nat.mod_eq_of_lt hb₁]
    have h₂ : (Nat.chineseRemainder hcod q.1 q.2 : ℕ) % d₂ = q.2 := by
      have h' : (Nat.chineseRemainder hcod q.1 q.2 : ℕ) % d₂ = q.2 % d₂ := hcrt.2
      rw [h', Nat.mod_eq_of_lt hb₂]
    exact Prod.ext h₁ h₂


end
end Dubon2026.SourceFunctionField.ConjugateSlots
