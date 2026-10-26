import Dubon2026.SourceWeierstrassRowSeries
import Dubon2026.SourceFrickeModularLatticeV2

/-! DUB-17/18 -> higher symmetric-power continuation -> arithmetic
automorphy -> original all-weight association -> original finite Gamma1
character realization -> Picard/H1 and diamond comparison -> differential
realization -> rational Fourier structure -> actual Fricke expansions.
Adapted from anthropics/fermats-last-theorem at
6e837e75355538c7f80bab5b956861e86c4eacc2 (Apache License 2.0).
Native Lipschitz summation and Weierstrass absolute summability are reused.
No external proof module or toolchain is imported. -/
namespace Dubon2026.SourceFricke
noncomputable section
open Complex Real PeriodPair
open UpperHalfPlane hiding I
open scoped UpperHalfPlane Manifold MatrixGroups ModularForm

/-- The literal Weierstrass summand indexed by the two integral lattice coordinates. -/
abbrev wpSummand (L : PeriodPair) (z : ℂ) (p : ℤ × ℤ) : ℂ :=
  1 / (z - (p.1 * L.ω₁ + p.2 * L.ω₂)) ^ 2 - 1 / (p.1 * L.ω₁ + p.2 * L.ω₂) ^ 2

theorem hasSum_weierstrassP_prod (L : PeriodPair) (z : ℂ) :
    HasSum (wpSummand L z) (weierstrassP L z) := by
  have h := (L.latticeEquivProd.symm.toEquiv.hasSum_iff (f := fun l : L.lattice ↦
      1 / (z - (l : ℂ)) ^ 2 - 1 / (l : ℂ) ^ 2)).mpr (L.hasSum_weierstrassP z)
  refine h.congr_fun fun p ↦ ?_
  simp only [Function.comp_apply, LinearEquiv.coe_toEquiv, wpSummand]
  have hcoe : ((L.latticeEquivProd.symm p : L.lattice) : ℂ) = p.1 * L.ω₁ + p.2 * L.ω₂ :=
    L.latticeEquiv_symm_apply p
  rw [hcoe]

theorem summable_weierstrassP_prod (L : PeriodPair) (z : ℂ) :
    Summable (wpSummand L z) :=
  (hasSum_weierstrassP_prod L z).summable

theorem weierstrassP_eq_tsum_tsum (L : PeriodPair) (z : ℂ) :
    weierstrassP L z =
      ∑' c : ℤ, ∑' d : ℤ,
        (1 / (z - (c * L.ω₁ + d * L.ω₂)) ^ 2 - 1 / (c * L.ω₁ + d * L.ω₂) ^ 2) := by
  rw [← (hasSum_weierstrassP_prod L z).tsum_eq]
  exact (summable_weierstrassP_prod L z).tsum_prod

theorem summable_weierstrassP_row (L : PeriodPair) (z : ℂ) :
    Summable fun c : ℤ ↦
      ∑' d : ℤ, (1 / (z - (c * L.ω₁ + d * L.ω₂)) ^ 2 - 1 / (c * L.ω₁ + d * L.ω₂) ^ 2) :=
  (summable_weierstrassP_prod L z).prod

theorem wpRow_periodPairOfTau_split (τ : ℍ) (z : ℂ) (c : ℤ) :
    ∑' d : ℤ, wpSummand (periodPairOfTau τ) z (c, d) =
      (∑' d : ℤ, 1 / ((z - c * (τ : ℂ)) + d) ^ 2) - ∑' d : ℤ, 1 / (c * (τ : ℂ) + d) ^ 2 := by
  have hA : Summable fun d : ℤ ↦ (1 : ℂ) / ((z - c * (τ : ℂ)) - d) ^ 2 := by
    have := summable_one_div_add_int_sq (z - c * (τ : ℂ))
    refine ((Equiv.neg ℤ).summable_iff.mpr this).congr fun d ↦ ?_
    simp [sub_eq_add_neg]
  have hB : Summable fun d : ℤ ↦ (1 : ℂ) / (c * (τ : ℂ) + d) ^ 2 :=
    summable_one_div_add_int_sq (c * (τ : ℂ))
  have step : (∑' d : ℤ, wpSummand (periodPairOfTau τ) z (c, d)) =
      (∑' d : ℤ, 1 / ((z - c * (τ : ℂ)) - d) ^ 2) - ∑' d : ℤ, 1 / (c * (τ : ℂ) + d) ^ 2 := by
    rw [← hA.tsum_sub hB]
    refine tsum_congr fun d ↦ ?_
    simp only [wpSummand, periodPairOfTau_ω₁, periodPairOfTau_ω₂, mul_one]
    ring
  rw [step, tsum_one_div_sub_int_sq]

theorem weierstrassP_periodPairOfTau_eq_row_sum (τ : ℍ) (z : ℂ) :
    weierstrassP (periodPairOfTau τ) z =
      ∑' c : ℤ, ((∑' d : ℤ, 1 / ((z - c * (τ : ℂ)) + d) ^ 2)
                  - ∑' d : ℤ, 1 / (c * (τ : ℂ) + d) ^ 2) := by
  rw [weierstrassP_eq_tsum_tsum]
  exact tsum_congr fun c ↦ by
    simpa [wpSummand, periodPairOfTau_ω₁, periodPairOfTau_ω₂, mul_one]
      using wpRow_periodPairOfTau_split τ z c

theorem weierstrassP_periodPairOfTau_qExpansion (τ : ℍ) {z : ℂ}
    (hz₁ : -τ.im < z.im) (hz₂ : z.im < τ.im) (hz : z ∈ Complex.integerComplement) :
    PeriodPair.weierstrassP (periodPairOfTau τ) z =
      (2 * π * I) ^ 2 *
        (cexp (2 * π * I * z) / (1 - cexp (2 * π * I * z)) ^ 2 + 1 / 12 +
          ∑' c : ℕ+, ∑' m : ℕ, (m : ℂ) *
            (cexp (2 * π * I * z) ^ m + (cexp (2 * π * I * z))⁻¹ ^ m - 2) *
              cexp (2 * π * I * (τ : ℂ)) ^ ((c : ℕ) * m)) := by
  rw [weierstrassP_periodPairOfTau_eq_row_sum]
  refine lipschitz_rows_qExpansion τ.im_pos hz₁ hz₂ hz ?_
  exact (summable_weierstrassP_row (periodPairOfTau τ) z).congr
    fun c ↦ wpRow_periodPairOfTau_split τ z c


end
end Dubon2026.SourceFricke
