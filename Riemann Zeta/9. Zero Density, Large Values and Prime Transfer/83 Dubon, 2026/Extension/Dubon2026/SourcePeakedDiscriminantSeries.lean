import Dubon2026.SourceSiegelFiniteSeriesProducts
import Dubon2026.SourceDiscriminantIntegralExpansion
import Dubon2026.SourceQExpansionPeriodWidth

/-! DUB-17/18 -> original Gamma1 degree/genus preservation -> level-power
slash integrality -> actual peaked auxiliary -> exact integral q-expansion.
Reuse the native integral discriminant product and sparse HasSum reindexing.
Only the actual discriminant with its first q factor removed is constructed;
no duplicate Eisenstein divisibility or absolute-convergence framework.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_SiegelUnit_qExpansion_one_coeff_of_coe_eq_prod_siegelFun_pow_mul_discriminant_pow. -/
namespace Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.Coefficients
noncomputable section
open Complex UpperHalfPlane PowerSeries Filter Topology
open scoped MatrixGroups ModularForm
local notation "𝕢" => Function.Periodic.qParam

/-- The actual discriminant series with its first q factor removed, at width N. -/
def deltaN (N : ℕ) : PowerSeries ℂ :=
  PowerSeries.mk fun i => if N ∣ i then (qExpansion 1 ModularForm.discriminant).coeff (i / N + 1) else 0

theorem coeff_deltaN (N i : ℕ) :
    coeff i (deltaN N) = if N ∣ i then (qExpansion 1 ModularForm.discriminant).coeff (i / N + 1) else 0 := by
  rw [deltaN, coeff_mk]

theorem constantCoeff_deltaN (N : ℕ) : constantCoeff (deltaN N) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_deltaN, if_pos (dvd_zero N), Nat.zero_div, zero_add,
    ModularForm.discriminant_qExpansion_coeff_one]

theorem integral_deltaN (N i : ℕ) : coeff i (deltaN N) ∈ (integralClosure ℤ ℂ).toSubring := by
  rw [coeff_deltaN]
  split_ifs
  · rw [qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit, coeff_map]
    exact intCast_mem _ _
  · exact zero_mem _

theorem hasSum_discriminant (τ : ℍ) :
    HasSum (fun n : ℕ => (qExpansion 1 ModularForm.discriminant).coeff n * 𝕢 1 τ ^ n)
      (ModularForm.discriminant τ) := by
  have h := UpperHalfPlane.hasSum_qExpansion one_pos
    (SlashInvariantFormClass.periodic_comp_ofComplex (f := CuspForm.discriminant) one_mem_strictPeriods_SL)
    (ModularFormClass.holo CuspForm.discriminant) (ModularFormClass.bdd_at_infty CuspForm.discriminant) τ
  simpa only [CuspForm.coe_discriminant, smul_eq_mul] using h

theorem expands_deltaN (N : ℕ) [NeZero N] :
    FiniteExpansion.Expands (N : ℝ) (deltaN N)
      (fun τ : ℍ => ModularForm.discriminant τ / 𝕢 (N : ℝ) τ ^ N) := by
  intro τ
  have hN : 0 < N := NeZero.pos N
  set q := 𝕢 (N : ℝ) τ with hqdef
  have hq0 : q ≠ 0 := Complex.exp_ne_zero _
  have h1 := hasSum_discriminant τ
  rw [SourceFricke.qParam_one_eq_pow (NeZero.ne N), ← hqdef] at h1
  have h2 := (hasSum_nat_add_iff' 1).mpr h1
  have hz : (qExpansion 1 ModularForm.discriminant).coeff 0 = 0 := by
    simpa only [CuspForm.coe_discriminant] using
      CuspFormClass.qExpansion_coeff_zero CuspForm.discriminant one_pos one_mem_strictPeriods_SL
  rw [Finset.sum_range_one, pow_zero, mul_one, hz, sub_zero] at h2
  have h3 : HasSum (fun j : ℕ => (qExpansion 1 ModularForm.discriminant).coeff (j + 1) • (q ^ N) ^ j)
      (ModularForm.discriminant τ / q ^ N) := by
    convert h2.div_const (q ^ N) using 1
    funext j
    rw [smul_eq_mul, pow_succ, ← mul_assoc, mul_div_assoc, div_self (pow_ne_zero _ hq0), mul_one]
  have h4 := Dubon2026.hasSum_pow_dvd_reindex hN h3
  simpa only [coeff_deltaN, ite_mul, zero_mul, smul_eq_mul] using h4

end
end Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.Coefficients
