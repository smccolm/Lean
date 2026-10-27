import Dubon2026.SourceFrickeCyclotomicCoefficients

/-! DUB-17/18 -> original all-weight association -> finite Gamma1
character realization -> Picard/H1 and diamond comparison -> differential
realization -> rational Fourier structure -> cyclotomic conjugation.
The actual finite Fourier coefficient model is transported by the given
cyclotomic embedding. No preservation of analytic modularity is assumed.
Adapted from anthropics/fermats-last-theorem at
6e837e75355538c7f80bab5b956861e86c4eacc2 (Apache License 2.0). -/
namespace Dubon2026.SourceFricke
noncomputable section
open Complex Real PeriodPair
open UpperHalfPlane hiding I
open scoped UpperHalfPlane Manifold MatrixGroups ModularForm

lemma ringHom_wpMonCoeffK {N : ℕ} (hN : N ≠ 0) (φ : kN N →+* ℂ) {s : ℕ}
    (hφ : φ (zetaK N) = zetaN N ^ s) (a₁ a₂ : ℕ) (i : WpIdx) :
    φ (wpMonCoeffK N a₁ a₂ i) = wpMonCoeff N a₁ (s * a₂ % N) i := by
  have hζN := zetaN_pow_N hN

  have hpow : ∀ k : ℕ, φ ⟨zetaN N ^ k, zetaN_pow_mem_kN N k⟩ = (zetaN N ^ s) ^ k := fun k ↦ by
    rw [← hφ, ← map_pow]; rfl
  have hinvpow : ∀ k : ℕ, φ ⟨(zetaN N)⁻¹ ^ k, zetaN_inv_pow_mem_kN N k⟩ = ((zetaN N ^ s)⁻¹) ^ k :=
    fun k ↦ by
    rw [← hφ, ← map_inv₀, ← map_pow]; rfl
  have hnatK : ∀ m : ℕ, (⟨(m : ℂ), natCast_mem_kN N m⟩ : kN N) = (m : kN N) := fun m ↦
    Subtype.ext (by simp)
  have hnat : ∀ m : ℕ, φ ⟨(m : ℂ), natCast_mem_kN N m⟩ = m := fun m ↦ by
    rw [hnatK, map_natCast]
  have htw : φ ⟨1 / 12, one_div_twelve_mem_kN N⟩ = 1 / 12 := by
    have h12 : (⟨1 / 12, one_div_twelve_mem_kN N⟩ : kN N) *
        ⟨((12 : ℕ) : ℂ), natCast_mem_kN N 12⟩ = 1 :=
      Subtype.ext (by show (1 / 12 : ℂ) * ((12 : ℕ) : ℂ) = 1; norm_num)
    have := congrArg φ h12
    rw [map_mul, map_one, hnat] at this
    rw [eq_one_div_of_mul_eq_one_left this]
    norm_num
  have hexp1 : (zetaN N ^ s) ^ a₂ = zetaN N ^ (s * a₂ % N) := by
    rw [← pow_mul, pow_eq_pow_mod (s * a₂) hζN]

  have hexp : ∀ m : ℕ, (zetaN N ^ s) ^ (a₂ * m) = zetaN N ^ (s * a₂ % N * m) := fun m ↦ by
    rw [← pow_mul, ← mul_assoc, pow_mul_eq_pow_mod_mul hζN]
  have hexpinv : ∀ m : ℕ, ((zetaN N ^ s)⁻¹) ^ (a₂ * m) = (zetaN N)⁻¹ ^ (s * a₂ % N * m) :=
    fun m ↦ by
    have hζN' : (zetaN N)⁻¹ ^ N = 1 := by rw [inv_pow, hζN, inv_one]
    rw [← inv_pow, ← pow_mul, ← mul_assoc, pow_mul_eq_pow_mod_mul hζN']
  rcases i with u | m | ⟨p, i⟩
  ·
    have e : wpMonCoeffK N a₁ a₂ (Sum.inl u) = ⟨1 / 12, one_div_twelve_mem_kN N⟩ +
        (if a₁ = 0 then ⟨zetaN N ^ a₂, zetaN_pow_mem_kN N a₂⟩ /
          (1 - ⟨zetaN N ^ a₂, zetaN_pow_mem_kN N a₂⟩) ^ 2 else 0) := by
      apply Subtype.ext
      simp only [wpMonCoeffK, wpMonCoeff]
      split_ifs <;> simp
    rw [e, map_add, htw]
    simp only [wpMonCoeff]
    split_ifs with h
    · rw [map_div₀, map_pow, map_sub, map_one, hpow, hexp1]
    · rw [map_zero]
  · have e : wpMonCoeffK N a₁ a₂ (Sum.inr (Sum.inl m)) =
        (if a₁ = 0 then 0 else ⟨((m : ℕ) : ℂ), natCast_mem_kN N m⟩ *
          ⟨zetaN N ^ (a₂ * m), zetaN_pow_mem_kN N _⟩) := by
      apply Subtype.ext
      simp only [wpMonCoeffK, wpMonCoeff]
      split_ifs <;> simp
    rw [e]
    simp only [wpMonCoeff]
    split_ifs with h
    · rw [map_zero]
    · rw [map_mul, hnat, hpow, hexp]
  · fin_cases i
    · have e : wpMonCoeffK N a₁ a₂ (Sum.inr (Sum.inr (p, 0))) =
          ⟨((p.2 : ℕ) : ℂ), natCast_mem_kN N _⟩ * ⟨zetaN N ^ (a₂ * p.2), zetaN_pow_mem_kN N _⟩ :=
        Subtype.ext (by simp [wpMonCoeffK, wpMonCoeff])
      simp only [Fin.zero_eta, Fin.isValue]
      rw [e, map_mul, hnat, hpow, hexp]
      simp [wpMonCoeff]
    · have e : wpMonCoeffK N a₁ a₂ (Sum.inr (Sum.inr (p, 1))) =
          ⟨((p.2 : ℕ) : ℂ), natCast_mem_kN N _⟩ *
            ⟨(zetaN N)⁻¹ ^ (a₂ * p.2), zetaN_inv_pow_mem_kN N _⟩ :=
        Subtype.ext (by simp [wpMonCoeffK, wpMonCoeff])
      simp only [Fin.mk_one, Fin.isValue]
      rw [e, map_mul, hnat, hinvpow, hexpinv]
      simp [wpMonCoeff]
    · have e : wpMonCoeffK N a₁ a₂ (Sum.inr (Sum.inr (p, 2))) =
          -⟨((2 : ℕ) : ℂ), natCast_mem_kN N 2⟩ * ⟨((p.2 : ℕ) : ℂ), natCast_mem_kN N _⟩ :=
        Subtype.ext (by
          show wpMonCoeff N a₁ a₂ (Sum.inr (Sum.inr (p, 2))) = -((2 : ℕ) : ℂ) * ((p.2 : ℕ) : ℂ)
          simp [wpMonCoeff])
      simp only [Fin.reduceFinMk, Fin.isValue]
      rw [e, map_mul, map_neg, hnat, hnat]
      simp [wpMonCoeff]

theorem ringHom_wpQCoeffK {N a₁ : ℕ} (ha₁ : a₁ < N) (φ : kN N →+* ℂ) {s : ℕ}
    (hφ : φ (zetaK N) = zetaN N ^ s) (a₂ n : ℕ) :
    φ (wpQCoeffK ha₁ a₂ n) = wpQCoeff N a₁ (s * a₂ % N) n := by
  have hN : N ≠ 0 := by omega
  have hfin := (finite_wpMonExp_fiber ha₁ n).to_subtype
  haveI := Fintype.ofFinite (wpMonExp N a₁ ⁻¹' {n})
  have e : wpQCoeffK ha₁ a₂ n = ∑ i : (wpMonExp N a₁ ⁻¹' {n}), wpMonCoeffK N a₁ a₂ i := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum, coe_wpQCoeffK, wpQCoeff, tsum_fintype]
    rfl
  rw [e, map_sum, wpQCoeff, tsum_fintype]
  exact Finset.sum_congr rfl fun i _ ↦ ringHom_wpMonCoeffK hN φ hφ a₁ a₂ i


end
end Dubon2026.SourceFricke
