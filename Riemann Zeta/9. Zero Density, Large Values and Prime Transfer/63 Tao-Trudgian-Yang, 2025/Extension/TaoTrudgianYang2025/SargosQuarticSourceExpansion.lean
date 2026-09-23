import TaoTrudgianYang2025.SargosQuarticFourierWindow
import TaoTrudgianYang2025.SargosQuarticFourierTail

/-! The literal quartic source assembled from the sharp core, exterior sums and actual infinite tail.
The cutoff width and all logarithmic lengths remain explicit. -/

noncomputable section

open scoped BigOperators

namespace TaoTrudgianYang2025

theorem sargosQuartic_source_stationary_expansion :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ D : ℝ, 1 ≤ D ∧ ∃ E : ℝ, 0 < E ∧
      ∀ (N : ℕ) (η α γ : ℝ),
        1 ≤ N → 0 < η → η ≤ 1 → 0 < α → |γ| ≤ α/(96*(N : ℝ)^2) →
        ((N : ℝ)+1)/N+4*η < 2 →
      ∀ R : ℕ, 0 < R →
        -(R : ℤ) ≤ sargosQuarticSupportLower N α γ (((N : ℝ)+1)/N) η →
        sargosQuarticSupportUpper N α γ 2 η ≤ (R : ℤ) →
      let L := sargosQuarticSupportLower N α γ (((N : ℝ)+1)/N) η
      let U := sargosQuarticSupportUpper N α γ 2 η
      let A := sargosQuarticPlateauLower N α γ (((N : ℝ)+1)/N) η
      let B := sargosQuarticPlateauUpper N α γ 2 η
      ‖sargosQuarticSum N (fun _ => 1) α γ-
        (∑ y ∈ Finset.Ioo A B, sargosQuarticStationaryMainTerm N α γ y)‖ ≤
        4*N*η+2+C*(η⁻¹)^2*(1+α*(N : ℝ)^2)^2/((N : ℝ)*(R : ℝ))+
          D*(1+Real.log ((B-A-1).toNat : ℝ))+(5*α*N*η+6)*E/Real.sqrt α+
          (4/Real.pi)*(2+Real.log ((L+(R : ℤ)).toNat : ℝ)+Real.log (((R : ℤ)-U).toNat : ℝ)) := by
  obtain ⟨C,hC,hsource⟩ := sargosQuartic_buffered_poisson_truncated
  obtain ⟨D,hD,E,hE,hwindow⟩ := sargosQuarticBufferedWindow_error
  refine ⟨C,hC,D,hD,E,hE,?_⟩
  intro N η α γ hN hη hη₁ hα hγ hflat R hR hRL hUR L U A B
  have hNp : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hl : 1 ≤ ((N : ℝ)+1)/N := (one_le_div hNp).mpr (by linarith)
  let f : ℤ → ℂ := fun y => sargosQuarticFourierMode (sargosQuarticBufferedCutoff N η) N α γ y
  let main := ∑ y ∈ Finset.Ioo A B, sargosQuarticStationaryMainTerm N α γ y
  have hs := hsource N η α γ hN hη hη₁ hα hγ R hR
  have hw := hwindow (((N : ℝ)+1)/N) 2 η hl le_rfl hη hflat N α γ hNp hα hγ
    (-(R : ℤ)) R hRL hUR
  have hnorm := norm_add_le
    (sargosQuarticSum N (fun _ => 1) α γ-(∑ y ∈ Finset.Icc (-(R : ℤ)) R, f y))
    ((∑ y ∈ Finset.Icc (-(R : ℤ)) R, f y)-main)
  rw [sub_add_sub_cancel] at hnorm
  have hw' : ‖(∑ y ∈ Finset.Icc (-(R : ℤ)) R, f y)-main‖ ≤
      D*(1+Real.log ((B-A-1).toNat : ℝ))+(5*α*N*η+6)*E/Real.sqrt α+
        (4/Real.pi)*(2+Real.log ((L+(R : ℤ)).toNat : ℝ)+Real.log (((R : ℤ)-U).toNat : ℝ)) := by
    simpa only [f,main,L,U,A,B,sargosQuarticBufferedCutoff,sub_neg_eq_add] using hw
  apply (hnorm.trans (add_le_add hs hw')).trans_eq
  ring

theorem sargosQuartic_source_stationary_expansion_precision :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ D : ℝ, 1 ≤ D ∧ ∃ E : ℝ, 0 < E ∧
      ∀ (N : ℕ) (η α γ ε : ℝ),
        1 ≤ N → 0 < η → η ≤ 1 → 0 < α → |γ| ≤ α/(96*(N : ℝ)^2) →
        ((N : ℝ)+1)/N+4*η < 2 → 0 < ε →
      let L := sargosQuarticSupportLower N α γ (((N : ℝ)+1)/N) η
      let U := sargosQuarticSupportUpper N α γ 2 η
      let A := sargosQuarticPlateauLower N α γ (((N : ℝ)+1)/N) η
      let B := sargosQuarticPlateauUpper N α γ 2 η
      let R : ℕ := ⌈C*(η⁻¹)^2*(1+α*(N : ℝ)^2)^2/((N : ℝ)*ε)⌉₊+L.natAbs+U.natAbs+1
      0 < R ∧ -(R : ℤ) ≤ L ∧ U ≤ (R : ℤ) ∧
        ‖sargosQuarticSum N (fun _ => 1) α γ-
          (∑ y ∈ Finset.Ioo A B, sargosQuarticStationaryMainTerm N α γ y)‖ ≤
          4*N*η+2+ε+D*(1+Real.log ((B-A-1).toNat : ℝ))+(5*α*N*η+6)*E/Real.sqrt α+
            (4/Real.pi)*(2+Real.log ((L+(R : ℤ)).toNat : ℝ)+Real.log (((R : ℤ)-U).toNat : ℝ)) := by
  obtain ⟨C,hC,D,hD,E,hE,hsource⟩ := sargosQuartic_source_stationary_expansion
  refine ⟨C,hC,D,hD,E,hE,?_⟩
  intro N η α γ ε hN hη hη₁ hα hγ hflat hε L U A B R
  have hNp : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hR : 0 < R := Nat.succ_pos _
  have hRL : -(R : ℤ) ≤ L := by dsimp [R]; omega
  have hUR : U ≤ (R : ℤ) := by dsimp [R]; omega
  refine ⟨hR,hRL,hUR,?_⟩
  have hRp : (0:ℝ) < R := by exact_mod_cast hR
  have hceil : C*(η⁻¹)^2*(1+α*(N : ℝ)^2)^2/((N : ℝ)*ε) ≤ (R : ℝ) := by
    exact (Nat.le_ceil _).trans (by
      dsimp [R]
      push_cast
      linarith [Nat.cast_nonneg (α := ℝ) L.natAbs,Nat.cast_nonneg (α := ℝ) U.natAbs])
  have hbudget : C*(η⁻¹)^2*(1+α*(N : ℝ)^2)^2/((N : ℝ)*(R : ℝ)) ≤ ε := by
    apply (div_le_iff₀ (mul_pos hNp hRp)).mpr
    have h := (div_le_iff₀ (mul_pos hNp hε)).mp hceil
    nlinarith
  have hs := hsource N η α γ hN hη hη₁ hα hγ hflat R hR hRL hUR
  exact hs.trans (by linarith)

end TaoTrudgianYang2025

