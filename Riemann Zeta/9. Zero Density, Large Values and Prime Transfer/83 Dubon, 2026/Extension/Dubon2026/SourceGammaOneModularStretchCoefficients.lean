import Dubon2026.SourceGammaOneModularStretch
import Dubon2026.SourceGammaOneRatioClosure
import Dubon2026.ModularDegeneracyCoefficients
import Mathlib.RingTheory.PowerSeries.Expand

/-! DUB-17/18 -> original all-weight adic association -> arithmetic Gamma1
realization -> genuine Hecke correspondences -> q-dilation field map.
The existing sparse-sum theorem and native modular expansion uniqueness prove
the integral expansion of the actual translated form. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane
open scoped MatrixGroups ModularForm

theorem modularStretch_coeff (M d : ℕ) [NeZero d] {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k) (n : ℕ) :
    (qExpansion 1 (modularStretch M d f)).coeff n =
      if d ∣ n then (qExpansion 1 f).coeff (n / d) else 0 := by
  have hp : (1 : ℝ) ∈ ((Gamma1 M).map (mapGL ℝ)).strictPeriods :=
    hper (by simp [Gamma1_mem, ModularGroup.T])
  have hp' : (1 : ℝ) ∈ ((Gamma1 M ⊓ Gamma0 (d * M)).map (mapGL ℝ)).strictPeriods :=
    hper (by constructor <;> simp [Gamma1_mem, Gamma0_mem, ModularGroup.T])
  letI : Fact (IsCusp OnePoint.infty ((Gamma1 M).map (mapGL ℝ))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods zero_lt_one hp⟩
  have hsum : ∀ τ : ℍ, HasSum (fun j : ℕ =>
      (if d ∣ j then (qExpansion 1 f).coeff (j / d) else 0) •
        Function.Periodic.qParam 1 (τ : ℂ) ^ j) (modularStretch M d f τ) := by
    intro τ
    rw [modularStretch_apply]
    have hs := UpperHalfPlane.hasSum_qExpansion zero_lt_one
      (SlashInvariantFormClass.periodic_comp_ofComplex f hp)
      (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f) (levelRaiseMatrix d • τ)
    rw [coe_levelRaiseMatrix_smul, qParam_nat_mul_eq_pow] at hs
    have hs' := hasSum_pow_dvd_reindex (Nat.pos_of_neZero d) hs
    convert hs' using 1
    funext j
    split_ifs <;> simp
  exact (ModularFormClass.qExpansion_coeff_unique zero_lt_one hp' hsum n).symm

theorem modularStretch_integral (M d : ℕ) [NeZero d] {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k) {p : PowerSeries ℤ}
    (hf : IsIntegralQExp f p) :
    IsIntegralQExp (modularStretch M d f) (PowerSeries.expand d (NeZero.ne d) p) := by
  unfold IsIntegralQExp
  ext n
  rw [PowerSeries.coeff_map, PowerSeries.coeff_expand, modularStretch_coeff]
  split_ifs with h
  · exact congrArg (PowerSeries.coeff (n / d)) hf
  · simp

end
end Dubon2026.SourceFunctionField.GammaOne
