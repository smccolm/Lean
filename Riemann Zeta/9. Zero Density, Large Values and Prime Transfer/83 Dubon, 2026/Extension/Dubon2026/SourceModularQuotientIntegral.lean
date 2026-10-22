import Dubon2026.SourceModularNormPolynomial
import Dubon2026.SourceLevelOneJPolynomial

/-! DUB-17/18 -> finite analytic-place exhaustion -> bounded original
functions integral over C[j] -> monic orbit relation for g/Delta^m.
Native modular-form norms and finite interpolation make each orbit
polynomial coefficient an actual level-one modular form. The proved
level-one polynomial reduction then places the coefficients in C[j].
This is the required integrality input; holomorphic removable singularities
and clearing cusp poles remain separate obligations. No place-exhaustion
or modular-curve genus premise is introduced.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularForm_isIntegral_adjoin_qExpansion_div_discriminant_pow_of_isArithmetic.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane ModularNormPolynomial SlashInvariantForm
open scoped MatrixGroups

theorem isIntegral_modular_quotient {𝒢 : Subgroup (GL (Fin 2) ℝ)} [𝒢.IsArithmetic] [𝒢.HasDetOne] (h1 : (1 : ℝ) ∈ 𝒢.strictPeriods) (m : ℕ) {k : ℤ} (hk : k = 12 * m) (g : ModularForm 𝒢 k) : IsIntegral (Algebra.adjoin ℂ ({(((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ 3 / ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ))} : Set (LaurentSeries ℂ))) (((qExpansion 1 (g : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) / ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ m) := by
  classical
  subst hk

  set Δmf : ModularForm 𝒮ℒ 12 := (CuspForm.discriminant : ModularForm 𝒮ℒ 12) with hΔmfdef
  have hΔcoe : ⇑Δmf = (ModularForm.discriminant : ℍ → ℂ) := rfl
  set Dsl : ModularForm 𝒮ℒ (12 * (m : ℤ)) :=
    ModularForm.mcast (by ring) (Δmf.pow m) with hDSLdef
  have hDSLq : qExpansion 1 (Dsl : ℍ → ℂ)
      = (qExpansion 1 (ModularForm.discriminant : ℍ → ℂ)) ^ m := by
    rw [hDSLdef, ModularForm.qExpansion_mcast,
      ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL, hΔcoe]
  set g' : ModularForm (𝒢 ⊓ 𝒮ℒ) (12 * (m : ℤ)) := restrict inf_le_left g with hg'def
  set D' : ModularForm (𝒢 ⊓ 𝒮ℒ) (12 * (m : ℤ)) := restrict inf_le_right Dsl with hD'def
  have hg'q : qExpansion 1 (g' : ℍ → ℂ) = qExpansion 1 (g : ℍ → ℂ) := by
    rw [hg'def, coe_restrict]
  have hD'q : qExpansion 1 (D' : ℍ → ℂ)
      = (qExpansion 1 (ModularForm.discriminant : ℍ → ℂ)) ^ m := by
    rw [hD'def, coe_restrict]
    exact hDSLq
  have hΔ0 : qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) ≠ 0 := fun h0 => by
    simpa [h0] using ModularForm.discriminant_qExpansion_coeff_one
  have hΔL : ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ≠ 0 := by
    rw [Ne, ← PowerSeries.coe_zero]
    exact fun h0 => hΔ0 (HahnSeries.ofPowerSeries_injective h0)
  have hΔmL : ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ m ≠ 0 := pow_ne_zero m hΔL
  letI : Fintype (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ) := Fintype.ofFinite _
  have h1' : (1 : ℝ) ∈ (𝒢 ⊓ 𝒮ℒ).strictPeriods := one_mem_strictPeriods_inf h1
  have h1'' : (1 : ℝ) ∈ ((𝒢 ⊓ 𝒮ℒ) ⊓ 𝒮ℒ).strictPeriods := one_mem_strictPeriods_inf h1'

  have hq0 : ∑ r : Fin (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ) + 1),
      qExpansion 1 (Aform g' D' (r : ℕ) : ℍ → ℂ)
        * (qExpansion 1 (g' : ℍ → ℂ)) ^ (r : ℕ)
        * (qExpansion 1 (D' : ℍ → ℂ)) ^ (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ) - (r : ℕ)) = 0 := by
    rw [← qExpansion_Sform h1'' g' D', Sform_eq_zero g' D', ModularForm.coe_zero, qExpansion_zero]
  have hq0L : ∑ r : Fin (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ) + 1),
      ((qExpansion 1 (Aform g' D' (r : ℕ) : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)
        * ((qExpansion 1 (g' : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ (r : ℕ)
        * ((qExpansion 1 (D' : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)
            ^ (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ) - (r : ℕ)) = 0 := by
    have h2 := congrArg (HahnSeries.ofPowerSeries ℤ ℂ) hq0
    rw [map_zero, map_sum] at h2
    rw [← h2]
    exact Finset.sum_congr rfl fun r _ => by rw [map_mul, map_mul, map_pow, map_pow]

  have hVP : ∀ r : ℕ, ∃ Pco : Polynomial ℂ,
      ((qExpansion 1 (Aform g' D' r : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)
        = Polynomial.aeval (((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ 3 / ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)) Pco * ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ (m * Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ)) := by
    intro r
    obtain ⟨Pco, -, hPc⟩ := exists_levelOne_j_polynomial
      (m * Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ))
      (ModularForm.mcast (by push_cast; ring) (Aform g' D' r))
    refine ⟨Pco, ?_⟩
    rw [← hPc, ModularForm.qExpansion_mcast]
  choose Pc hP using hVP

  set FL : LaurentSeries ℂ := ((qExpansion 1 (g : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) / ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ m with hFLdef
  have hgL : ((qExpansion 1 (g' : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)
      = ((qExpansion 1 (g : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) := by rw [hg'q]
  have hDqL : ((qExpansion 1 (D' : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)
      = ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ m := by
    rw [hD'q, PowerSeries.coe_pow]

  have hkey : (∑ r : Fin (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ) + 1),
      Polynomial.aeval (((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ 3 / ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)) (Pc (r : ℕ)) * FL ^ (r : ℕ))
      * (((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ (m * Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ))
          * ((qExpansion 1 (D' : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ))
      = ∑ r : Fin (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ) + 1),
        ((qExpansion 1 (Aform g' D' (r : ℕ) : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)
          * ((qExpansion 1 (g' : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ (r : ℕ)
          * ((qExpansion 1 (D' : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)
              ^ (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ) - (r : ℕ)) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hP (r : ℕ)]
    have hr : (r : ℕ) ≤ Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ) := Nat.lt_succ_iff.mp r.2
    have hexp : ((qExpansion 1 (g' : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ (r : ℕ)
        * ((qExpansion 1 (D' : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)
            ^ (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ) - (r : ℕ))
        = FL ^ (r : ℕ)
          * ((qExpansion 1 (D' : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ) := by
      rw [hgL, hDqL, pow_sub₀ _ hΔmL hr, hFLdef, div_pow]
      field_simp
    linear_combination (-(Polynomial.aeval (((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ 3 / ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)) (Pc (r : ℕ))
      * ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ (m * Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ)))) * hexp
  have hDne : ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ (m * Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ))
      * ((qExpansion 1 (D' : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ) ≠ 0 := by
    rw [hDqL]
    exact mul_ne_zero (pow_ne_zero _ hΔL) (pow_ne_zero _ hΔmL)
  have hsum0 : ∑ r : Fin (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ) + 1),
      Polynomial.aeval (((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ 3 / ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)) (Pc (r : ℕ)) * FL ^ (r : ℕ) = 0 := by
    have h3 := hkey.trans hq0L
    rcases mul_eq_zero.mp h3 with h' | h'
    · exact h'
    · exact absurd h' hDne
  have hsum0r : ∑ r ∈ Finset.range (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ) + 1),
      Polynomial.aeval (((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ 3 / ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)) (Pc r) * FL ^ r = 0 := by
    rw [← Fin.sum_univ_eq_sum_range
      (fun rr => Polynomial.aeval (((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ 3 / ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)) (Pc rr) * FL ^ rr) (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ) + 1)]
    exact hsum0
  have hsum1 : (∑ r ∈ Finset.range (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ)),
      Polynomial.aeval (((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ 3 / ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)) (Pc r) * FL ^ r)
      + Polynomial.aeval (((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ 3 / ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)) (Pc (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ))) * FL ^ (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ)) = 0 := by
    rw [← Finset.sum_range_succ
      (fun r => Polynomial.aeval (((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ 3 / ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)) (Pc r) * FL ^ r) (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ))]
    exact hsum0r

  have hcard : (Finset.univ : Finset (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ)).card = Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ) := by
    rw [Finset.card_univ, Nat.card_eq_fintype_card]
  have hAn : Aform g' D' (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ))
      = ((-1 : ℂ) ^ (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ))) • ModularForm.norm 𝒮ℒ D' := by
    ext τ
    rw [Aform_apply, ModularForm.IsGLPos.smul_apply, norm_apply_eq, smul_eq_mul]
    unfold Pp
    conv_lhs => rw [← hcard]
    rw [coeff_card_prod_linear, Finset.prod_neg, hcard]
  have hqfD : ∀ (q : 𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ) (τ : ℍ), quotientFunc D' q τ = Dsl τ := by
    intro q τ
    induction q using Quotient.inductionOn with
    | h r =>
      rw [quotientFunc_mk, hD'def, coe_restrict, slash_action_eqn Dsl _ (inv_mem r.2)]
  have hnormD : ModularForm.norm 𝒮ℒ D' = ModularForm.mcast (by ring)
      (Dsl.pow (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ))) := by
    ext τ
    calc ModularForm.norm 𝒮ℒ D' τ
        = ∏ q : 𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ, quotientFunc D' q τ := norm_apply_eq D' τ
      _ = ∏ _q : 𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ, Dsl τ := Finset.prod_congr rfl fun q _ => hqfD q τ
      _ = (Dsl τ) ^ (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ)) := by rw [Finset.prod_const, hcard]
      _ = (ModularForm.mcast (by ring) (Dsl.pow (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ))) : ModularForm 𝒮ℒ (12 * (m : ℤ) * (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ) : ℤ))) τ := by
          simp only [ModularForm.coe_mcast, ModularForm.coe_pow, Pi.pow_apply]
  have hqAnL : ((qExpansion 1 (Aform g' D' (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ)) : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)
      = (-1 : LaurentSeries ℂ) ^ (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ)) * ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ (m * Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ)) := by
    have hps : qExpansion 1 (Aform g' D' (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ)) : ℍ → ℂ)
        = PowerSeries.C ((-1 : ℂ) ^ (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ)))
          * (qExpansion 1 (ModularForm.discriminant : ℍ → ℂ)) ^ (m * Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ)) := by
      rw [hAn, ModularForm.IsGLPos.coe_smul,
        ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL, hnormD,
        ModularForm.qExpansion_mcast,
        ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL, hDSLq, ← pow_mul,
        PowerSeries.smul_eq_C_mul]
    rw [hps, PowerSeries.coe_mul, PowerSeries.coe_pow, PowerSeries.coe_C, map_pow, map_neg,
      map_one]
  have hPn : Polynomial.aeval (((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ 3 / ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)) (Pc (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ))) = (-1 : LaurentSeries ℂ) ^ (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ)) := by
    have h4 := (hP (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ))).symm.trans hqAnL
    exact mul_right_cancel₀ (pow_ne_zero _ hΔL) h4
  rw [hPn] at hsum1

  have hmem : ∀ r : ℕ, ((-1 : LaurentSeries ℂ) ^ (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ)) * Polynomial.aeval (((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ 3 / ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)) (Pc r))
      ∈ Algebra.adjoin ℂ ({(((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ 3 / ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ))} : Set (LaurentSeries ℂ)) := fun r =>
    Subalgebra.mul_mem _ (pow_mem (neg_mem (one_mem _)) _)
      (Polynomial.aeval_mem_adjoin_singleton ℂ _)
  refine ⟨Polynomial.X ^ (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ)) + ∑ r ∈ Finset.range (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ)),
    Polynomial.C (⟨_, hmem r⟩ : Algebra.adjoin ℂ ({(((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ 3 / ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ))} : Set (LaurentSeries ℂ)))
      * Polynomial.X ^ r, ?_, ?_⟩
  ·
    refine Polynomial.monic_X_pow_add ?_
    refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
    rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
    intro r hr
    exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le r _)
      (by exact_mod_cast Finset.mem_range.mp hr)
  ·
    rw [← Polynomial.aeval_def, map_add, map_pow, Polynomial.aeval_X, map_sum]
    have hterm : ∀ r ∈ Finset.range (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ)),
        Polynomial.aeval FL
          (Polynomial.C (⟨_, hmem r⟩ : Algebra.adjoin ℂ ({(((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ 3 / ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ))} : Set (LaurentSeries ℂ)))
            * Polynomial.X ^ r)
          = ((-1 : LaurentSeries ℂ) ^ (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ)) * Polynomial.aeval (((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ 3 / ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)) (Pc r)) * FL ^ r := by
      intro r _
      rw [map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X]
      rfl
    rw [Finset.sum_congr rfl hterm]
    have hdist : ∑ r ∈ Finset.range (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ)),
        ((-1 : LaurentSeries ℂ) ^ (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ)) * Polynomial.aeval (((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ 3 / ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)) (Pc r)) * FL ^ r
        = (-1 : LaurentSeries ℂ) ^ (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ))
          * ∑ r ∈ Finset.range (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ)), Polynomial.aeval (((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ 3 / ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)) (Pc r) * FL ^ r := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun r _ => by ring
    rw [hdist]
    have h11 : ((-1 : LaurentSeries ℂ) ^ (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ))) * ((-1 : LaurentSeries ℂ) ^ (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ))) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]
      norm_num
    linear_combination ((-1 : LaurentSeries ℂ) ^ (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ))) * hsum1 - (FL ^ (Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ))) * h11

end
end Dubon2026.SourceFunctionField
