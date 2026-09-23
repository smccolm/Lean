import TaoTrudgianYang2025.SargosDualTentGram
import TaoTrudgianYang2025.SargosQuarticMomentRegularity

/-! Restrict the dual tent integral to its actual central physical rectangle. -/

noncomputable section

open MeasureTheory Set GafniTao
open scoped BigOperators

namespace TaoTrudgianYang2025

theorem sargosTentPlanarIntegrand_zero_outside {ι : Type*}
    (S : Finset ι) (u v : ι → ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (p : ℝ × ℝ) (hp : p ∉ (Icc (-a) a) ×ˢ (Icc (-b) b)) :
    sargosTentPlanarIntegrand S u v a b p = 0 := by
  have hzero {w x : ℝ} (hw : 0 < w) (hx : x ∉ Icc (-w) w) :
      sargosRealTent w x = 0 := by
    apply sargosRealTent_zero_of_le_abs hw
    by_contra h
    exact hx (abs_le.mp (le_of_lt (lt_of_not_ge h)))
  by_cases hpa : p.1 ∈ Icc (-a) a
  · have hpb : p.2 ∉ Icc (-b) b := fun h => hp ⟨hpa,h⟩
    simp only [sargosTentPlanarIntegrand,hzero hb hpb,mul_zero,zero_mul]
  · simp only [sargosTentPlanarIntegrand,hzero ha hpa,zero_mul]

theorem sargosTentPlanarIntegrand_le_norm_sq {ι : Type*}
    (S : Finset ι) (u v : ι → ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (p : ℝ × ℝ) :
    sargosTentPlanarIntegrand S u v a b p ≤
      ‖sargosPlanarSum S (fun _ => 1) u v p.1 p.2‖^2 := by
  have ht : sargosRealTent a p.1*sargosRealTent b p.2 ≤ 1 := by
    calc
      _ ≤ 1*1 := mul_le_mul (sargosRealTent_le_one ha p.1)
        (sargosRealTent_le_one hb p.2) (sargosRealTent_nonneg b p.2) (by norm_num)
      _ = _ := one_mul 1
  simpa only [sargosTentPlanarIntegrand,one_mul] using
    mul_le_mul_of_nonneg_right ht (sq_nonneg ‖sargosPlanarSum S (fun _ => 1) u v p.1 p.2‖)

theorem sargosTentPlanarIntegral_le_central {ι : Type*}
    (S : Finset ι) (u v : ι → ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ p : ℝ × ℝ, sargosTentPlanarIntegrand S u v a b p ∂(volume.prod volume)) ≤
      ∫ α in Icc (-a) a, ∫ γ in Icc (-b) b,
        ‖sargosPlanarSum S (fun _ => 1) u v α γ‖^2 := by
  have hi : Integrable
      (fun p : ℝ × ℝ => ‖sargosPlanarSum S (fun _ => 1) u v p.1 p.2‖^2)
      ((volume.restrict (Icc (-a) a)).prod (volume.restrict (Icc (-b) b))) := by
    convert integrable_sargosPlanarNormSq_rectangle S (fun _ => 1) u v
      (-a) (2*a) (-b) (2*b) using 1
    congr 3 <;> ring
  have hir : IntegrableOn
      (fun p : ℝ × ℝ => ‖sargosPlanarSum S (fun _ => 1) u v p.1 p.2‖^2)
      ((Icc (-a) a) ×ˢ (Icc (-b) b)) (volume.prod volume) := by
    rwa [IntegrableOn,← Measure.prod_restrict]
  calc
    _ = ∫ p in (Icc (-a) a) ×ˢ (Icc (-b) b),
        sargosTentPlanarIntegrand S u v a b p ∂(volume.prod volume) :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero
        (sargosTentPlanarIntegrand_zero_outside S u v ha hb)).symm
    _ ≤ ∫ p in (Icc (-a) a) ×ˢ (Icc (-b) b),
        ‖sargosPlanarSum S (fun _ => 1) u v p.1 p.2‖^2 ∂(volume.prod volume) :=
      setIntegral_mono_on (integrable_sargosTentPlanarIntegrand S u v ha hb).integrableOn
        hir (measurableSet_Icc.prod measurableSet_Icc)
        (fun p hp => sargosTentPlanarIntegrand_le_norm_sq S u v ha hb p)
    _ = _ := by
      rw [← Measure.prod_restrict]
      exact integral_prod _ hi

theorem sargosNearPairs_card_le_central {ι : Type*}
    (S : Finset ι) (u v : ι → ℝ) {Δ μ : ℝ} (hΔ : 0 < Δ) (hμ : 0 < μ) :
    ((sargosNearPairs S u v (1/Δ) (1/μ)).card : ℝ) ≤
      (64/(Δ*μ))*(∫ α in Icc (-(Δ/2)) (Δ/2), ∫ γ in Icc (-(μ/2)) (μ/2),
        ‖sargosPlanarSum S (fun _ => 1) u v α γ‖^2) := by
  have hA : (Δ/2)*(1/Δ) ≤ 1/2 := by field_simp; norm_num
  have hB : (μ/2)*(1/μ) ≤ 1/2 := by field_simp; norm_num
  have h := (sargosNearPairs_weighted_card_le_tentIntegral S u v
    (by positivity : 0 < Δ/2) (by positivity : 0 < μ/2) hA hB).trans
    (sargosTentPlanarIntegral_le_central S u v (by positivity) (by positivity))
  have he : (Δ/2)*(μ/2)/16 = Δ*μ/64 := by ring
  rw [he] at h
  have hpos : 0 < Δ*μ/64 := by positivity
  have hd : ((sargosNearPairs S u v (1/Δ) (1/μ)).card : ℝ) ≤
      (∫ α in Icc (-(Δ/2)) (Δ/2), ∫ γ in Icc (-(μ/2)) (μ/2),
        ‖sargosPlanarSum S (fun _ => 1) u v α γ‖^2)/(Δ*μ/64) :=
    (le_div_iff₀ hpos).mpr (by simpa only [mul_comm] using h)
  convert hd using 1
  field_simp

end TaoTrudgianYang2025
