import Dubon2026.SourceLevelOneCoefficientRing
import Dubon2026.SourceLevelOneIntegralWeightFactor
import Dubon2026.SourceTraceProductCoefficientRing

/-! DUB-17/18 -> original Gamma1 degree preservation -> even-weight slash
integrality -> peaked auxiliary trace. The existing E4/E6 weight factor
reduces the actual level-one trace to the proved weight-12N coefficient
criterion. Its unit constant coefficient then recovers every coefficient
of the original trace. No integrality of the full trace is assumed. -/
namespace Dubon2026.SourceFunctionField.LevelOneCoefficientRing
noncomputable section
open UpperHalfPlane ModularForm
open scoped MatrixGroups

theorem levelOne_trace_coeff_mem_of_initial_coeff_mem
    (k : ℤ) (a b d : ℕ) (hw : k + (4 * (a : ℤ) + 6 * (b : ℤ)) = 12 * (d : ℤ))
    (F : ModularForm 𝒮ℒ k) (R : Subring ℂ)
    (hF : ∀ n ≤ d, (qExpansion 1 (F : ℍ → ℂ)).coeff n ∈ R) (n : ℕ) :
    (qExpansion 1 (F : ℍ → ℂ)).coeff n ∈ R := by
  obtain ⟨E, P, hP, hP1⟩ := exists_integral_weight_factor a b _ rfl
  let H : ModularForm 𝒮ℒ (12 * (d : ℤ)) := (F.mul E).mcast hw
  have hqH : qExpansion 1 (H : ℍ → ℂ) =
      qExpansion 1 (F : ℍ → ℂ) * qExpansion 1 (E : ℍ → ℂ) := by
    change qExpansion 1 (⇑((F.mul E).mcast hw) : ℍ → ℂ) = _
    rw [ModularForm.qExpansion_mcast,
      ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL]
  have hER : ∀ j, (qExpansion 1 (E : ℍ → ℂ)).coeff j ∈ R := by
    intro j
    rw [← hP, PowerSeries.coeff_map]
    exact intCast_mem R _
  have hHint : ∀ m ≤ d, (qExpansion 1 (H : ℍ → ℂ)).coeff m ∈ R := by
    intro m hm
    rw [hqH, PowerSeries.coeff_mul]
    refine R.sum_mem fun p hp => R.mul_mem ?_ (hER _)
    have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    exact hF p.1 (by omega)
  have hHall : ∀ m, (qExpansion 1 (H : ℍ → ℂ)).coeff m ∈ R :=
    levelOne_coeff_mem_of_initial_coeff_mem d H R hHint
  apply coeff_mem_of_product_initial_coeff_mem R (qExpansion 1 (F : ℍ → ℂ))
    (qExpansion 1 (E : ℍ → ℂ)) 0 (n + 1)
  · intro j hj
    omega
  · refine ⟨1, R.one_mem, ?_⟩
    rw [one_mul, ← hP, PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff,
      hP1, map_one]
  · exact hER
  · intro m _
    rw [← hqH]
    exact hHall m
  · omega

end
end Dubon2026.SourceFunctionField.LevelOneCoefficientRing
