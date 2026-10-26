import Dubon2026.SourceIntegralHomogeneousRelation
import Dubon2026.SourceModularNormPolynomial

/-! DUB-17/18 -> actual Gamma1 differential/cusp comparison -> inverse-j
integral bound. Apply the existing modular orbit polynomial to a cubed
form and E4 denominator. Its level-one coefficients are integral over
C[1/j] by SourceInverseJLevelOneIntegral; integral closure transitivity
then removes the remaining quotient-integrality premise. -/
namespace Dubon2026.SourceFunctionField.InverseJIntegral
noncomputable section
open UpperHalfPlane ModularNormPolynomial SlashInvariantForm
open scoped MatrixGroups ModularForm
local notation "qL" => fun F : ℍ → ℂ => (qExpansion 1 F : LaurentSeries ℂ)
local notation "δ" => qL ModularForm.discriminant
local notation "e₄" => qL (ModularForm.E₄ : ℍ → ℂ)

theorem isIntegral_modular_quotient_E4_cube
    {𝒢 : Subgroup (GL (Fin 2) ℝ)} [𝒢.IsArithmetic] [𝒢.HasDetOne]
    (h1 : (1 : ℝ) ∈ 𝒢.strictPeriods) (m : ℕ)
    (g : ModularForm 𝒢 (12 * (m : ℤ))) :
    IsIntegral (Algebra.adjoin ℂ ({δ / e₄ ^ 3} : Set (LaurentSeries ℂ)))
      (qL (g : ℍ → ℂ) / e₄ ^ (3 * m)) := by
  classical
  let Dsl : ModularForm 𝒮ℒ (12 * (m : ℤ)) :=
    (ModularForm.E₄.pow (3 * m)).mcast (by push_cast; ring)
  let g' : ModularForm (𝒢 ⊓ 𝒮ℒ) (12 * (m : ℤ)) := restrict inf_le_left g
  let D' : ModularForm (𝒢 ⊓ 𝒮ℒ) (12 * (m : ℤ)) := restrict inf_le_right Dsl
  have hDsl : qL (Dsl : ℍ → ℂ) = e₄ ^ (3 * m) := by
    dsimp only [Dsl]
    rw [ModularForm.qExpansion_mcast,
      ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL, PowerSeries.coe_pow]
  have hg : qL (g' : ℍ → ℂ) = qL (g : ℍ → ℂ) := rfl
  have hD : qL (D' : ℍ → ℂ) = e₄ ^ (3 * m) := hDsl
  letI : Fintype (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ) := Fintype.ofFinite _
  let d := Nat.card (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ)
  have hcard : (Finset.univ : Finset (𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ)).card = d := by
    dsimp only [d]
    rw [Finset.card_univ, Nat.card_eq_fintype_card]
  have hper := one_mem_strictPeriods_inf (one_mem_strictPeriods_inf h1)
  have hsum : ∑ r ∈ Finset.range (d + 1),
      qL (Aform g' D' r : ℍ → ℂ) * qL (g' : ℍ → ℂ) ^ r *
        qL (D' : ℍ → ℂ) ^ (d - r) = 0 := by
    have hq : ∑ r : Fin (d + 1),
        qExpansion 1 (Aform g' D' (r : ℕ) : ℍ → ℂ) *
          qExpansion 1 (g' : ℍ → ℂ) ^ (r : ℕ) *
          qExpansion 1 (D' : ℍ → ℂ) ^ (d - (r : ℕ)) = 0 := by
      rw [← qExpansion_Sform hper g' D', Sform_eq_zero g' D',
        ModularForm.coe_zero, qExpansion_zero]
    have hqL := congrArg (HahnSeries.ofPowerSeries ℤ ℂ) hq
    simp only [map_zero, map_sum, map_mul, map_pow] at hqL
    rw [← Fin.sum_univ_eq_sum_range]
    exact hqL
  have hlead : qL (Aform g' D' d : ℍ → ℂ) = (-qL (D' : ℍ → ℂ)) ^ d := by
    have hA : Aform g' D' d = ((-1 : ℂ) ^ d) •
        (Dsl.pow d).mcast (by ring) := by
      ext τ
      rw [Aform_apply, ModularForm.IsGLPos.smul_apply]
      simp only [ModularForm.coe_mcast, ModularForm.coe_pow, Pi.pow_apply, smul_eq_mul]
      unfold Pp
      rw [← hcard, coeff_card_prod_linear]
      have htrans : ∀ q : 𝒮ℒ ⧸ (𝒢 ⊓ 𝒮ℒ).subgroupOf 𝒮ℒ,
          quotientFunc D' q τ = Dsl τ := by
        intro q
        induction q using Quotient.inductionOn with
        | h r =>
          rw [quotientFunc_mk]
          change ((Dsl : ℍ → ℂ) ∣[12 * (m : ℤ)] (r : GL (Fin 2) ℝ)⁻¹) τ = Dsl τ
          rw [slash_action_eqn Dsl _ (inv_mem r.2)]
      simp_rw [htrans]
      rw [Finset.prod_const, hcard, neg_pow]
    dsimp only
    rw [hA, ModularForm.IsGLPos.coe_smul,
      ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL,
      ModularForm.qExpansion_mcast, ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL,
      PowerSeries.smul_eq_C_mul, PowerSeries.coe_mul, PowerSeries.coe_pow,
      PowerSeries.coe_C, map_pow, map_neg, map_one]
    change (-1 : LaurentSeries ℂ) ^ d * qL (Dsl : ℍ → ℂ) ^ d =
      (-qL (D' : ℍ → ℂ)) ^ d
    rw [neg_pow, hD, hDsl]
  have hI : IsIntegral (Algebra.adjoin ℂ ({δ / e₄ ^ 3} : Set (LaurentSeries ℂ)))
      (qL (g' : ℍ → ℂ) / qL (D' : ℍ → ℂ)) := by
    refine isIntegral_div_of_relation d (fun r => qL (Aform g' D' r : ℍ → ℂ))
      _ _ (by rw [hD]; exact pow_ne_zero _ eisenstein_four_expansion_ne_zero)
      hsum hlead ?_
    intro r _
    rw [hD, ← pow_mul]
    exact levelOne_isIntegral (3 * m * d) (Aform g' D' r) (by push_cast; ring)
  simpa only [hg, hD] using hI

theorem isIntegral_modular_quotient_E4
    {𝒢 : Subgroup (GL (Fin 2) ℝ)} [𝒢.IsArithmetic] [𝒢.HasDetOne]
    (h1 : (1 : ℝ) ∈ 𝒢.strictPeriods) (m : ℕ) {k : ℤ}
    (hk : k = 4 * (m : ℤ)) (g : ModularForm 𝒢 k) :
    IsIntegral (Algebra.adjoin ℂ ({δ / e₄ ^ 3} : Set (LaurentSeries ℂ)))
      (qL (g : ℍ → ℂ) / e₄ ^ m) := by
  refine IsIntegral.of_pow (by norm_num : 0 < 3) ?_
  have hw : (3 : ℤ) * k = 12 * (m : ℤ) := by rw [hk]; ring
  have hI := isIntegral_modular_quotient_E4_cube h1 m ((g.pow 3).mcast hw)
  dsimp only at hI
  rw [ModularForm.qExpansion_mcast, ModularForm.qExpansion_pow one_pos h1,
    PowerSeries.coe_pow] at hI
  simpa only [div_pow, ← pow_mul, Nat.mul_comm m 3] using hI

end
end Dubon2026.SourceFunctionField.InverseJIntegral
