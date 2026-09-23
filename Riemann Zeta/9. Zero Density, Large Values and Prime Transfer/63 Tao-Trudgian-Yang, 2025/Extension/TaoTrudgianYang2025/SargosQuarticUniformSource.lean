import TaoTrudgianYang2025.SargosQuarticLogBudget

/-! Uniform stationary-scale error for the literal quartic source and its buffered main range.
The remaining bridge to the paper's full stationary range is not asserted here. -/

noncomputable section

open scoped BigOperators

namespace TaoTrudgianYang2025

theorem sargosQuartic_source_buffered_uniform :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ (N : ℕ) (α γ : ℝ),
      9216 ≤ N → 1/Real.sqrt (N : ℝ) ≤ α → |γ| ≤ 1/(N : ℝ)^3 →
      let η := sargosQuarticStationaryWidth N α
      let A := sargosQuarticPlateauLower N α γ (((N : ℝ)+1)/N) η
      let B := sargosQuarticPlateauUpper N α γ 2 η
      ‖sargosQuarticSum N (fun _ => 1) α γ-
        (∑ y ∈ Finset.Ioo A B, sargosQuarticStationaryMainTerm N α γ y)‖ ≤
        M*(1/Real.sqrt α+1+Real.log (α*(N : ℝ)^2+1)) := by
  obtain ⟨C,hC,D,hD,E,hE,hsource⟩ := sargosQuartic_source_stationary_expansion_precision
  let F := D+8/Real.pi
  let K := Real.log (C+24)
  let a := 4+6*E
  let b := 3+5*E+F*(1+K)
  let M := max 1 (max a (max b (3*F)))
  have hM : 1 ≤ M := le_max_left _ _
  have ha : a ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  have hb : b ≤ M := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hF : 3*F ≤ M := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨M,hM,?_⟩
  intro N α γ hN hα hγ η A B
  have hNr : (9216:ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0:ℝ) < N := by linarith
  have hN₁ : 1 ≤ N := by omega
  have hNr₁ : (1:ℝ) ≤ N := by linarith
  have hαp := (sargosQuartic_source_scale hNr hα).1
  have hγs := sargosQuartic_source_smallness hNr hα hγ
  have hηs := sargosQuarticStationaryWidth_source hN hα
  have hl : 1 ≤ ((N : ℝ)+1)/N := (one_le_div hNp).mpr (by linarith)
  let L := sargosQuarticSupportLower N α γ (((N : ℝ)+1)/N) η
  let U := sargosQuarticSupportUpper N α γ 2 η
  let R := sargosQuarticSharpRadius C N α γ (((N : ℝ)+1)/N) 2 η
  let G := K+3*Real.log (α*(N : ℝ)^2+1)
  have he : η⁻¹^2 = α*(N : ℝ)^2 := sargosQuarticStationaryWidth_inverse_sq hαp.le
  have hs := hsource N η α γ 1 hN₁ hηs.1 hηs.2.1 hαp hγs hηs.2.2 (by norm_num)
  simp only [he,mul_one] at hs
  have hs' :
      ‖sargosQuarticSum N (fun _ => 1) α γ-
        (∑ y ∈ Finset.Ioo A B, sargosQuarticStationaryMainTerm N α γ y)‖ ≤
        4*N*η+2+1+D*(1+Real.log ((B-A-1).toNat : ℝ))+(5*α*N*η+6)*E/Real.sqrt α+
          (4/Real.pi)*(2+Real.log ((L+(R : ℤ)).toNat : ℝ)+Real.log (((R : ℤ)-U).toNat : ℝ)) :=
    hs.2.2.2
  have hlogs := sargosQuarticSharpLengths_log_budget (show 0 ≤ C by linarith)
    hNr₁ hαp hγs hηs.1 hl le_rfl hηs.2.2
  have hi : Real.log ((B-A-1).toNat : ℝ) ≤ G := hlogs.1
  have hleft : Real.log ((L+(R : ℤ)).toNat : ℝ) ≤ G := hlogs.2.1
  have hright : Real.log (((R : ℤ)-U).toNat : ℝ) ≤ G := hlogs.2.2
  have hcore : D*(1+Real.log ((B-A-1).toNat : ℝ)) ≤ D*(1+G) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have hfar :
      (4/Real.pi)*(2+Real.log ((L+(R : ℤ)).toNat : ℝ)+Real.log (((R : ℤ)-U).toNat : ℝ)) ≤
        (8/Real.pi)*(1+G) := by
    have hh := mul_le_mul_of_nonneg_left (show
      2+Real.log ((L+(R : ℤ)).toNat : ℝ)+Real.log (((R : ℤ)-U).toNat : ℝ) ≤ 2*(1+G) by
        linarith) (show 0 ≤ 4/Real.pi by positivity)
    convert hh using 1
    ring
  have hsm : 4*(N : ℝ)*η = 4/Real.sqrt α := sargosQuarticStationaryWidth_smoothing hNp hαp
  have htr : (5*α*N*η+6)*E/Real.sqrt α = 5*E+6*E/Real.sqrt α :=
    sargosQuarticStationaryWidth_transition hNp hαp E
  rw [hsm,htr] at hs'
  have hx : 0 ≤ 1/Real.sqrt α := by positivity
  have ht : 0 ≤ Real.log (α*(N : ℝ)^2+1) :=
    Real.log_nonneg (by nlinarith [mul_nonneg hαp.le (sq_nonneg (N : ℝ))])
  have hax := mul_le_mul_of_nonneg_right ha hx
  have hft := mul_le_mul_of_nonneg_right hF ht
  calc
    _ ≤ a*(1/Real.sqrt α)+b+3*F*Real.log (α*(N : ℝ)^2+1) := by
      calc
        _ ≤ 4/Real.sqrt α+3+D*(1+G)+(5*E+6*E/Real.sqrt α)+
            (8/Real.pi)*(1+G) := by linarith only [hs',hcore,hfar]
        _ = _ := by dsimp [a,b,F,G]; ring
    _ ≤ M*(1/Real.sqrt α+1+Real.log (α*(N : ℝ)^2+1)) := by
      nlinarith only [hax,hft,hb]

theorem sargosQuartic_source_buffered_uniform_logN :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ (N : ℕ) (α γ : ℝ),
      9216 ≤ N → 1/Real.sqrt (N : ℝ) ≤ α → α ≤ 1 → |γ| ≤ 1/(N : ℝ)^3 →
      let η := sargosQuarticStationaryWidth N α
      let A := sargosQuarticPlateauLower N α γ (((N : ℝ)+1)/N) η
      let B := sargosQuarticPlateauUpper N α γ 2 η
      ‖sargosQuarticSum N (fun _ => 1) α γ-
        (∑ y ∈ Finset.Ioo A B, sargosQuarticStationaryMainTerm N α γ y)‖ ≤
        M*(1/Real.sqrt α+1+Real.log ((N : ℝ)+1)) := by
  obtain ⟨M,hM,hsource⟩ := sargosQuartic_source_buffered_uniform
  refine ⟨2*M,by linarith,?_⟩
  intro N α γ hN hα hα₁ hγ η A B
  have hNr : (9216:ℝ) ≤ N := by exact_mod_cast hN
  have hαp := (sargosQuartic_source_scale hNr hα).1
  have hNp : (0:ℝ) < N := by linarith
  have ht : α*(N : ℝ)^2+1 ≤ ((N : ℝ)+1)^2 := by
    nlinarith [mul_le_mul_of_nonneg_right hα₁ (sq_nonneg (N : ℝ))]
  have hlog := Real.log_le_log (show 0 < α*(N : ℝ)^2+1 by positivity) ht
  rw [Real.log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  have hs := hsource N α γ hN hα hγ
  apply hs.trans
  have hmul := mul_le_mul_of_nonneg_left hlog (show 0 ≤ M by linarith)
  have hx : 0 ≤ M*(1/Real.sqrt α+1) := by positivity
  nlinarith

end TaoTrudgianYang2025
