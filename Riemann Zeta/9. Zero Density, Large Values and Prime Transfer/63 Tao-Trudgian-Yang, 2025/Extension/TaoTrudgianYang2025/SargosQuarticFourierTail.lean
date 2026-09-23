import TaoTrudgianYang2025.SargosQuarticFourierDecay
import TaoTrudgianYang2025.SargosQuarticBufferedPoisson
import TaoTrudgianYang2025.IntegerFourierTails

/-! Quantitative two-sided quartic Fourier tails and the literal truncated source sum. -/

noncomputable section

open Set
open scoped BigOperators

namespace TaoTrudgianYang2025

def sargosQuarticBufferedFarTail (l b η N α γ : ℝ) (R : ℕ) : ℂ :=
  ∑' y : ℤ, if R < y.natAbs then
    sargosQuarticFourierMode (modelPhaseBufferedCutoff l b η) N α γ y else 0

theorem sargosQuarticBufferedFarTail_uniform :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (l b η : ℝ), 1 ≤ l → b ≤ 2 → 0 < η → η ≤ 1 →
      ∀ (N α γ : ℝ), 0 < N → 0 < α → |γ| ≤ α/(96*N^2) →
      ∀ R : ℕ, 0 < R →
        ‖sargosQuarticBufferedFarTail l b η N α γ R‖ ≤
          C*(η⁻¹)^2*(1+α*N^2)^2/(N*(R : ℝ)) := by
  obtain ⟨C,hC,hmode⟩ := sargosQuarticBufferedFourierMode_inverse_square_bound
  refine ⟨2*C,by linarith,?_⟩
  intro l b η hl hb hη hη₁ N α γ hN hα hγ R hR
  have hs := summable_norm_sargosQuarticFourierMode
    (modelPhaseBufferedCutoff_contDiff l b η)
    (modelPhaseBufferedCutoff_tsupport_model hη hl hb) hN α γ
  have hbound : ∀ y : ℤ, y ≠ 0 →
      ‖sargosQuarticFourierMode (modelPhaseBufferedCutoff l b η) N α γ y‖ ≤
        (C*(η⁻¹)^2*(1+α*N^2)^2/N)/(y : ℝ)^2 := by
    intro y hy
    convert hmode l b η hl hb hη hη₁ N α γ y hN hα hγ
      (by exact_mod_cast hy) using 1
    ring
  have h := norm_integer_far_tail_le_of_inverse_square
    (by positivity : 0 ≤ C*(η⁻¹)^2*(1+α*N^2)^2/N) hs hbound hR
  convert h using 1
  ring

theorem sargosQuartic_buffered_poisson_truncated :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (N : ℕ) (η α γ : ℝ),
      1 ≤ N → 0 < η → η ≤ 1 → 0 < α → |γ| ≤ α/(96*(N : ℝ)^2) →
      ∀ R : ℕ, 0 < R →
        ‖sargosQuarticSum N (fun _ => 1) α γ-
          ∑ y ∈ Finset.Icc (-(R : ℤ)) (R : ℤ),
            sargosQuarticFourierMode (sargosQuarticBufferedCutoff N η) N α γ y‖ ≤
          4*N*η+2+C*(η⁻¹)^2*(1+α*(N : ℝ)^2)^2/((N : ℝ)*(R : ℝ)) := by
  obtain ⟨C,hC,htail⟩ := sargosQuarticBufferedFarTail_uniform
  refine ⟨C,hC,?_⟩
  intro N η α γ hN hη hη₁ hα hγ R hR
  have hNp : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  let χ := sargosQuarticBufferedCutoff N η
  have hsource := sargosQuartic_buffered_poisson hN hη α γ
  have hsplit := tsum_int_eq_sum_Icc_add_far hsource.1.of_norm R
  have hl : 1 ≤ ((N : ℝ)+1)/N := (one_le_div hNp).mpr (by linarith)
  have hfar := htail (((N : ℝ)+1)/N) 2 η hl le_rfl hη hη₁ N α γ hNp hα hγ R hR
  have hdiff : ‖(∑' y : ℤ, sargosQuarticFourierMode χ N α γ y)-
      ∑ y ∈ Finset.Icc (-(R : ℤ)) (R : ℤ), sargosQuarticFourierMode χ N α γ y‖ ≤
        C*(η⁻¹)^2*(1+α*(N : ℝ)^2)^2/((N : ℝ)*(R : ℝ)) := by
    rw [hsplit]
    simpa only [χ,add_sub_cancel_left,sargosQuarticBufferedFarTail,sargosQuarticBufferedCutoff] using hfar
  calc
    _ = ‖(sargosQuarticSum N (fun _ => 1) α γ-(∑' y : ℤ, sargosQuarticFourierMode χ N α γ y))+
        ((∑' y : ℤ, sargosQuarticFourierMode χ N α γ y)-
          ∑ y ∈ Finset.Icc (-(R : ℤ)) (R : ℤ), sargosQuarticFourierMode χ N α γ y)‖ := by
      congr 1
      abel
    _ ≤ _ := (norm_add_le _ _).trans (add_le_add hsource.2 hdiff)

theorem sargosQuartic_buffered_poisson_truncated_precision :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (N : ℕ) (η α γ ε : ℝ),
      1 ≤ N → 0 < η → η ≤ 1 → 0 < α → |γ| ≤ α/(96*(N : ℝ)^2) → 0 < ε →
      let R : ℕ := ⌈C*(η⁻¹)^2*(1+α*(N : ℝ)^2)^2/((N : ℝ)*ε)⌉₊+1
      0 < R ∧
        ‖sargosQuarticSum N (fun _ => 1) α γ-
          ∑ y ∈ Finset.Icc (-(R : ℤ)) (R : ℤ),
            sargosQuarticFourierMode (sargosQuarticBufferedCutoff N η) N α γ y‖ ≤
          4*N*η+2+ε := by
  obtain ⟨C,hC,htrunc⟩ := sargosQuartic_buffered_poisson_truncated
  refine ⟨C,hC,?_⟩
  intro N η α γ ε hN hη hη₁ hα hγ hε R
  have hNp : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hR : 0 < R := Nat.succ_pos _
  refine ⟨hR,?_⟩
  have hRp : (0:ℝ) < R := by exact_mod_cast hR
  have hceil : C*(η⁻¹)^2*(1+α*(N : ℝ)^2)^2/((N : ℝ)*ε) ≤ (R : ℝ) := by
    exact (Nat.le_ceil _).trans (by
      dsimp [R]
      rw [Nat.cast_add,Nat.cast_one]
      linarith)
  have hbudget : C*(η⁻¹)^2*(1+α*(N : ℝ)^2)^2/((N : ℝ)*(R : ℝ)) ≤ ε := by
    apply (div_le_iff₀ (mul_pos hNp hRp)).mpr
    have h := (div_le_iff₀ (mul_pos hNp hε)).mp hceil
    nlinarith
  exact (htrunc N η α γ hN hη hη₁ hα hγ R hR).trans (add_le_add le_rfl hbudget)

end TaoTrudgianYang2025

