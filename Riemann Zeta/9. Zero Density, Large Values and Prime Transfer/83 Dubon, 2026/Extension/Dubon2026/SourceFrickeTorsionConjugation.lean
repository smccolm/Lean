import Dubon2026.SourceFrickeCyclotomicTransport

/-! DUB-17/18 -> original all-weight arithmetic association -> finite Gamma1
character realization -> Picard/H1 and diamond comparison -> differential
realization -> rational Fourier structure -> cyclotomic conjugation.
The coefficient-field power series maps to the native q-expansion of the
actual normalized torsion Weierstrass function. A cyclotomic embedding
maps it to the actual function at the transformed torsion coordinate. -/
namespace Dubon2026.SourceFricke
noncomputable section
open UpperHalfPlane
open scoped Manifold MatrixGroups ModularForm

/-- The actual normalized torsion Fourier series over its cyclotomic coefficient field. -/
def wpQSeriesK {N a₁ : ℕ} (ha₁ : a₁ < N) (a₂ : ℕ) : PowerSeries (kN N) :=
  PowerSeries.mk (wpQCoeffK ha₁ a₂)

theorem wpQSeriesK_map_inclusion {N a₁ a₂ : ℕ}
    (ha₁ : a₁ < N) (ha₂ : a₂ < N) (h₀ : a₁ ≠ 0 ∨ a₂ ≠ 0) :
    (wpQSeriesK ha₁ a₂).map (algebraMap (kN N) ℂ) =
      qExpansion N (wpNorm N a₁ a₂) := by
  ext n
  rw [PowerSeries.coeff_map, wpQSeriesK, PowerSeries.coeff_mk]
  change (wpQCoeffK ha₁ a₂ n : ℂ) = _
  exact (qExpansion_wpNorm_coeff ha₁ ha₂ h₀ n).symm

theorem wpQSeriesK_map_cyclotomic {N a₁ a₂ s : ℕ}
    (ha₁ : a₁ < N) (ha₂ : a₂ < N) (h₀ : a₁ ≠ 0 ∨ a₂ ≠ 0)
    (hs : s.Coprime N) (φ : kN N →+* ℂ)
    (hφ : φ (zetaK N) = zetaN N ^ s) :
    (wpQSeriesK ha₁ a₂).map φ =
      qExpansion N (wpNorm N a₁ (s * a₂ % N)) := by
  have hN : 0 < N := by omega
  have hsa₂ : s * a₂ % N < N := Nat.mod_lt _ hN
  have h₀' : a₁ ≠ 0 ∨ s * a₂ % N ≠ 0 := by
    refine h₀.imp id fun ha₂0 hc => ha₂0 ?_
    rw [← Nat.dvd_iff_mod_eq_zero] at hc
    exact Nat.eq_zero_of_dvd_of_lt (hs.symm.dvd_of_dvd_mul_left hc) ha₂
  ext n
  rw [PowerSeries.coeff_map, wpQSeriesK, PowerSeries.coeff_mk,
    ringHom_wpQCoeffK ha₁ φ hφ]
  exact (qExpansion_wpNorm_coeff ha₁ hsa₂ h₀' n).symm

end
end Dubon2026.SourceFricke
