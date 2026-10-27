import Dubon2026.SourceGammaOneFieldModularRatio

/-! DUB-17/18 -> actual Gamma1 differential/cusp converse -> meromorphic
realization of the original integral-ratio field. Adapt the proved local
SourceModularRatioEvaluation, retaining actual equal-weight modular forms
and exact q-expansion injectivity. Only translation membership is needed.
The local source credits anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open UpperHalfPlane
open scoped MatrixGroups Topology Manifold

/-- Evaluate the source modular ratio where a denominator is nonzero. -/
def realize (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (x : LaurentSeries ℂ) (τ : ℍ) : ℂ := by
  classical
  exact
    if H : ∃ p : (k : ℤ) × (ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k ×
          ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k),
        (p.2.2 : ℍ → ℂ) τ ≠ 0 ∧
          x * ((qExpansion 1 (p.2.2 : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
            ((qExpansion 1 (p.2.1 : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)
    then (H.choose.2.1 : ℍ → ℂ) τ / (H.choose.2.2 : ℍ → ℂ) τ
    else 0

theorem realize_eq_div (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (hT : ModularGroup.T ∈ Γ) {k : ℤ}
    (g h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (x : LaurentSeries ℂ)
    (hx : x * ((qExpansion 1 (h : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
      ((qExpansion 1 (g : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ))
    (τ : ℍ) (hτ : (h : ℍ → ℂ) τ ≠ 0) :
    realize Γ x τ = (g : ℍ → ℂ) τ / (h : ℍ → ℂ) τ := by
  classical

  have h1 : (1 : ℝ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    exact hper hT
  have H : ∃ p : (k : ℤ) × (ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k ×
        ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k),
      (p.2.2 : ℍ → ℂ) τ ≠ 0 ∧
        x * ((qExpansion 1 (p.2.2 : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
          ((qExpansion 1 (p.2.1 : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) :=
    ⟨⟨k, g, h⟩, hτ, hx⟩
  have hval : realize Γ x τ = (H.choose.2.1 : ℍ → ℂ) τ / (H.choose.2.2 : ℍ → ℂ) τ := by
    simp only [realize, dif_pos H]
  rw [hval]
  obtain ⟨hτ', hx'⟩ := H.choose_spec
  set p := H.choose with hp

  obtain ⟨k', g', h'⟩ := p
  simp only at hτ' hx' ⊢

  have hq : qExpansion 1 ((g' : ℍ → ℂ) * (h : ℍ → ℂ)) = qExpansion 1 ((g : ℍ → ℂ) * (h' : ℍ → ℂ)) := by
    apply (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℂ))
    rw [ModularForm.qExpansion_mul_coe one_pos h1, ModularForm.qExpansion_mul_coe one_pos h1,
      PowerSeries.coe_mul, PowerSeries.coe_mul, ← hx, ← hx']
    ring

  have hAB : (g'.mul h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) (k' + k)) =
      ModularForm.mcast (add_comm k k') (g.mul h') := by
    rw [← sub_eq_zero, ← ModularForm.qExpansion_eq_zero_iff one_pos h1, ModularForm.coe_sub,
      ModularForm.qExpansion_sub one_pos h1, sub_eq_zero, ModularForm.coe_mcast,
      ModularForm.coe_mul, ModularForm.coe_mul, hq]
  have hτeq : (g' : ℍ → ℂ) τ * (h : ℍ → ℂ) τ = (g : ℍ → ℂ) τ * (h' : ℍ → ℂ) τ := by
    have := congrArg (fun f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) (k' + k) => (f : ℍ → ℂ) τ)
      hAB
    simpa [ModularForm.coe_mul, ModularForm.coe_mcast] using this
  rw [div_eq_div_iff hτ' hτ, hτeq]

end
end Dubon2026.SourceFunctionField.GammaOne
