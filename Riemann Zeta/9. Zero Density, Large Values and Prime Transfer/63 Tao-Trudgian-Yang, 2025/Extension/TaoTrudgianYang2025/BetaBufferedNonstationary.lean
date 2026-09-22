import TaoTrudgianYang2025.BetaBufferedVariation
import TaoTrudgianYang2025.BetaWeightedPhase
import TaoTrudgianYang2025.BetaFourierModes

/-!
# Width-independent nonstationary bounds for the original Fourier modes

The cutoff variation is proved, the monotone slope comes from the original
model, and the normalized-to-physical factor N is retained.
-/

noncomputable section

open Set Expdb MeasureTheory
open scoped ContDiff FourierTransform

namespace TaoTrudgianYang2025

theorem modelPhaseBufferedCutoff_support_open {l r η : ℝ} (hη : 0 < η) :
    Function.support (modelPhaseBufferedCutoff l r η) ⊆ Ioo (l+η) (r-η) := by
  intro u hu
  constructor
  · by_contra h
    exact hu (modelPhaseBufferedCutoff_zero_left hη (le_of_not_gt h))
  · by_contra h
    exact hu (modelPhaseBufferedCutoff_zero_right hη (le_of_not_gt h))

theorem modelPhaseBufferedCutoff_eq_zero_of_overlap {l r η : ℝ}
    (hη : 0 < η) (h : r-η ≤ l+η) :
    modelPhaseBufferedCutoff l r η = fun _ => 0 := by
  funext u
  apply Function.notMem_support.mp
  intro hu
  have hh := modelPhaseBufferedCutoff_support_open hη hu
  linarith [hh.1,hh.2]

theorem intervalC1Bound_modelPhaseBufferedCutoff
    {l r η a b : ℝ} (hη : 0 < η) (hab : a ≤ b) :
    IntervalC1Bound (fun u => (modelPhaseBufferedCutoff l r η u : ℂ)) a b 2 := by
  have he : (fun u => (modelPhaseBufferedCutoff l r η u : ℂ)) =
      (fun u => (zetaBandCutoff (l+η) (l+2*η) (r-2*η) (r-η) u : ℂ)) := by
    funext u
    rw [modelPhaseBufferedCutoff_eq_band hη]
  rw [he]
  exact intervalC1Bound_zetaBandCutoff (by linarith) (by linarith) hab

theorem norm_modelPhaseBufferedNormalizedMode_nonstationary
    {F : ℝ → ℝ} {σ δ T q l r η lam : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hT : 0 < T) (hη : 0 < η) (hl : 1 ≤ l) (hr : r ≤ 2) (hlam : 0 < lam)
    (hgap : (∀ u ∈ Ioo (1 : ℝ) 2, lam ≤ T*deriv F u-q) ∨
      (∀ u ∈ Ioo (1 : ℝ) 2, T*deriv F u-q ≤ -lam)) :
    ‖modelPhaseNormalizedMode (modelPhaseBufferedCutoff l r η) F T q‖ ≤
      4/(lam*Real.pi) := by
  by_cases hab : l+η ≤ r-η
  · let φ : ℝ → ℝ := fun u => T*F u-q*u
    have hd {u : ℝ} (hu : u ∈ Ioo (1 : ℝ) 2) :
        deriv φ u = T*deriv F u-q := by
      have hFu := (approximateModelPhase_contDiffAt hF hu).differentiableAt (by simp)
      simpa only [φ,mul_one] using
        ((hFu.hasDerivAt.const_mul T).sub ((hasDerivAt_id u).const_mul q)).deriv
    have hφ : ∀ u ∈ Ioo (1 : ℝ) 2, ContDiffAt ℝ 2 φ u := by
      intro u hu
      exact (contDiffAt_const.mul ((approximateModelPhase_contDiffAt hF hu).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))).sub
          (contDiffAt_const.mul contDiffAt_id)
    have hmono : AntitoneOn (deriv φ) (Ioo (1 : ℝ) 2) := by
      intro u hu v hv huv
      rw [hd hu,hd hv]
      exact sub_le_sub_right (mul_le_mul_of_nonneg_left
        ((approximateModelPhase_deriv_strictAntiOn hσ hδ hF).antitoneOn hu hv huv) hT.le) q
    have hsub : Icc (l+η) (r-η) ⊆ Ioo (1 : ℝ) 2 := by
      intro u hu
      constructor <;> linarith [hu.1,hu.2]
    have hg : (∀ u ∈ Ioo (1 : ℝ) 2, lam ≤ deriv φ u) ∨
        (∀ u ∈ Ioo (1 : ℝ) 2, deriv φ u ≤ -lam) := by
      rcases hgap with hp | hn
      · exact Or.inl (fun u hu => by rw [hd hu]; exact hp u hu)
      · exact Or.inr (fun u hu => by rw [hd hu]; exact hn u hu)
    have h := (intervalC1Bound_modelPhaseBufferedCutoff (l := l) (r := r) hη hab).fourierChar_of_slope_gap
      hab hlam isOpen_Ioo hsub hφ hmono hg
    have hs : Function.support (fun u => (modelPhaseBufferedCutoff l r η u : ℂ)*
        (𝐞 (φ u) : ℂ)) ⊆ Ioc (l+η) (r-η) := by
      intro u hu
      have hχ : modelPhaseBufferedCutoff l r η u ≠ 0 := by
        intro hz
        exact hu (by simp only [hz,Complex.ofReal_zero,zero_mul])
      have hh := modelPhaseBufferedCutoff_support_open hη hχ
      exact ⟨hh.1,hh.2.le⟩
    unfold modelPhaseNormalizedMode
    rw [← intervalIntegral.integral_eq_integral_of_support_subset hs]
    convert h using 1
    norm_num
  · have hz := modelPhaseBufferedCutoff_eq_zero_of_overlap hη (le_of_not_ge hab)
    simp only [modelPhaseNormalizedMode,hz,Complex.ofReal_zero,zero_mul,integral_zero,norm_zero]
    positivity

theorem norm_modelPhaseBufferedFourierMode_nonstationary
    {F : ℝ → ℝ} {σ δ T N q l r η lam : ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    (hT : 0 < T) (hN : 0 < N) (hη : 0 < η)
    (hl : 1 ≤ l) (hr : r ≤ 2) (hlam : 0 < lam)
    (hgap : (∀ u ∈ Ioo (1 : ℝ) 2, lam ≤ T*deriv F u-q*N) ∨
      (∀ u ∈ Ioo (1 : ℝ) 2, T*deriv F u-q*N ≤ -lam)) :
    ‖modelPhaseFourierMode (modelPhaseBufferedCutoff l r η) F T N q‖ ≤
      4*N/(lam*Real.pi) := by
  rw [modelPhaseFourierMode_eq_normalized _ _ _ _ hN,norm_smul,Real.norm_eq_abs,abs_of_pos hN]
  exact (mul_le_mul_of_nonneg_left
    (norm_modelPhaseBufferedNormalizedMode_nonstationary hσ hδ hF hT hη hl hr hlam hgap)
    hN.le).trans_eq (by ring)

end TaoTrudgianYang2025
