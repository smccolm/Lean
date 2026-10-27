import Dubon2026.SourceFrickeProductExpansion

/-! DUB-17/18 -> original all-weight association -> finite Gamma1
characters -> Picard/H1 and diamond comparison -> differential realization
-> rational Fourier structure -> Fricke product coefficient transport.
The actual E4 E6 product is multiplied by the actual normalized Weierstrass
torsion function. Analytic expansion and coefficient transport are proved.
The elementary analytic assembly adapts anthropics/fermats-last-theorem,
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache License 2.0. -/
namespace Dubon2026.SourceFricke
noncomputable section
open UpperHalfPlane ModularForm SlashInvariantFormClass ModularFormClass
open scoped Manifold MatrixGroups ModularForm

/-- The actual Fricke numerator Fourier series over the cyclotomic field. -/
def frickeHQSeriesK {N a₁ : ℕ} (ha₁ : a₁ < N) (a₂ : ℕ) : PowerSeries (kN N) :=
  (e4e6QSeries N).map (algebraMap ℚ (kN N)) * wpQSeriesK ha₁ a₂

theorem e4e6QSeries_map_ringHom {N : ℕ} (φ : kN N →+* ℂ) :
    ((e4e6QSeries N).map (algebraMap ℚ (kN N))).map φ =
      (e4e6QSeries N).map (algebraMap ℚ ℂ) := by
  ext n
  simp only [PowerSeries.coeff_map]
  simp

theorem frickeHQSeriesK_map_inclusion {N a₁ a₂ : ℕ}
    (ha₁ : a₁ < N) (ha₂ : a₂ < N) (h₀ : a₁ ≠ 0 ∨ a₂ ≠ 0) :
    (frickeHQSeriesK ha₁ a₂).map (algebraMap (kN N) ℂ) =
      qExpansion N (frickeH N a₁ a₂) := by
  rw [frickeHQSeriesK, map_mul, e4e6QSeries_map_ringHom,
    e4e6QSeries_map (by omega), wpQSeriesK_map_inclusion ha₁ ha₂ h₀,
    qExpansion_frickeH ha₁ ha₂ h₀]

theorem frickeHQSeriesK_map_cyclotomic {N a₁ a₂ s : ℕ}
    (ha₁ : a₁ < N) (ha₂ : a₂ < N) (h₀ : a₁ ≠ 0 ∨ a₂ ≠ 0)
    (hs : s.Coprime N) (φ : kN N →+* ℂ)
    (hφ : φ (zetaK N) = zetaN N ^ s) :
    (frickeHQSeriesK ha₁ a₂).map φ =
      qExpansion N (frickeH N a₁ (s * a₂ % N)) := by
  have hsa₂ : s * a₂ % N < N := Nat.mod_lt _ (by omega)
  have h₀' : a₁ ≠ 0 ∨ s * a₂ % N ≠ 0 := by
    refine h₀.imp id fun ha₂0 hc => ha₂0 ?_
    rw [← Nat.dvd_iff_mod_eq_zero] at hc
    exact Nat.eq_zero_of_dvd_of_lt (hs.symm.dvd_of_dvd_mul_left hc) ha₂
  rw [frickeHQSeriesK, map_mul, e4e6QSeries_map_ringHom,
    e4e6QSeries_map (by omega), wpQSeriesK_map_cyclotomic ha₁ ha₂ h₀ hs φ hφ,
    qExpansion_frickeH ha₁ hsa₂ h₀']

theorem qExpansion_frickeH_coeff_mem_kN {N a₁ a₂ : ℕ}
    (ha₁ : a₁ < N) (ha₂ : a₂ < N) (h₀ : a₁ ≠ 0 ∨ a₂ ≠ 0) (n : ℕ) :
    (qExpansion N (frickeH N a₁ a₂)).coeff n ∈ kN N := by
  rw [← frickeHQSeriesK_map_inclusion ha₁ ha₂ h₀, PowerSeries.coeff_map]
  exact ((frickeHQSeriesK ha₁ a₂).coeff n).property

theorem qExpansion_frickeH_conj {N a₁ a₂ s : ℕ}
    (ha₁ : a₁ < N) (ha₂ : a₂ < N) (h₀ : a₁ ≠ 0 ∨ a₂ ≠ 0)
    (hs : s.Coprime N) (φ : kN N →+* ℂ)
    (hφ : φ (zetaK N) = zetaN N ^ s) (n : ℕ)
    (z : kN N) (hz : (z : ℂ) = (qExpansion N (frickeH N a₁ a₂)).coeff n) :
    (qExpansion N (frickeH N a₁ (s * a₂ % N))).coeff n = φ z := by
  have hz' : z = (frickeHQSeriesK ha₁ a₂).coeff n := by
    apply Subtype.ext
    rw [hz, ← frickeHQSeriesK_map_inclusion ha₁ ha₂ h₀, PowerSeries.coeff_map]
    rfl
  rw [hz', ← frickeHQSeriesK_map_cyclotomic ha₁ ha₂ h₀ hs φ hφ,
    PowerSeries.coeff_map]

end
end Dubon2026.SourceFricke
