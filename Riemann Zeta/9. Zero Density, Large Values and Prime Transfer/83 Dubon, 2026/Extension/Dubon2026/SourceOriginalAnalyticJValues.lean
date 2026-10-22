import Dubon2026.SourceJSeedRatioValues

/-! DUB-17/18 -> finite-place geometry -> actual analytic j-values.
The explicit seed values and the already proved cusp degeneracy maps
identify every original divisor generator j(q^d) pointwise. Discriminant
nonvanishing discharges the denominator condition at every point.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

theorem realize_coeffEmb_jqd (N d : ℕ) [NeZero d] (hd : d ∣ N) (τ : ℍ) :
    realize N (coeffEmb ℂ (qExpand ℚ d jq)) τ =
      ModularForm.E₄ (levelRaiseMatrix d • τ) ^ 3 /
        ModularForm.discriminant (levelRaiseMatrix d • τ) := by
  obtain ⟨g, h, _, he, hgval, hhval⟩ := exists_jq_cusp_ratio_with_values
  have hd1 : d * 1 ∣ N := by simpa using hd
  let G := cuspDegeneracyMap d hd1 24 g
  let H := cuspDegeneracyMap d hd1 24 h
  have hH : H τ ≠ 0 := by
    dsimp only [H]
    rw [cuspDegeneracyMap_apply, hhval]
    exact mul_ne_zero (ModularForm.discriminant_ne_zero _) (ModularForm.discriminant_ne_zero _)
  have hx : coeffEmb ℂ (qExpand ℚ d jq) *
      (qExpansion 1 (H : ℍ → ℂ) : LaurentSeries ℂ) =
        (qExpansion 1 (G : ℍ → ℂ) : LaurentSeries ℂ) := by
    have hmap : coeffEmb ℂ (qExpand ℚ d jq) = qExpand ℂ d (jqModC ℂ) := by
      calc
        _ = qExpand ℂ d (coeffEmb ℂ jq) := coeffMap_qExpand (algebraMap ℚ ℂ) d jq
        _ = _ := by rw [coeffEmb_jq]
    rw [hmap]
    dsimp only [H, G]
    rw [cuspDegeneracyMap_laurent, cuspDegeneracyMap_laurent, ← map_mul, he]
  rw [realize_eq_div N (CuspForm.toModularFormₗ G) (CuspForm.toModularFormₗ H) _ hx τ hH]
  change G τ / H τ = _
  dsimp only [G, H]
  rw [cuspDegeneracyMap_apply, cuspDegeneracyMap_apply, hgval, hhval,
    mul_div_mul_left _ _ (ModularForm.discriminant_ne_zero _)]

theorem realize_coeffEmb_jq (N : ℕ) (τ : ℍ) :
    realize N (coeffEmb ℂ jq) τ = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ := by
  have h := realize_coeffEmb_jqd N 1 (one_dvd N) τ
  have hτ : levelRaiseMatrix 1 • τ = τ := by
    apply UpperHalfPlane.ext
    simp [coe_levelRaiseMatrix_smul]
  simpa only [qExpand_one_apply, hτ] using h

theorem realize_jOver (N : ℕ) [NeZero N] (τ : ℍ) :
    realize N (jOver N ℂ : LaurentSeries ℂ) τ =
      ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ :=
  realize_coeffEmb_jq N τ

theorem realize_jNOver (N : ℕ) [NeZero N] (τ : ℍ) :
    realize N (jNOver N ℂ : LaurentSeries ℂ) τ =
      ModularForm.E₄ (levelRaiseMatrix N • τ) ^ 3 /
        ModularForm.discriminant (levelRaiseMatrix N • τ) :=
  realize_coeffEmb_jqd N N dvd_rfl τ

end
end Dubon2026.SourceFunctionField
