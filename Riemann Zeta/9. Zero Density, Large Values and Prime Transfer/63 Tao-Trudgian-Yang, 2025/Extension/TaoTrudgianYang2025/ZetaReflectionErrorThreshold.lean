import TaoTrudgianYang2025.ZetaReflectionErrorPowers

/-! One physical window absorbs every retained reflection remainder. -/

noncomputable section
open Complex Filter MeasureTheory Set
namespace TaoTrudgianYang2025

theorem exists_reflection_remainders_absorbed {τ : ℝ} (hτ : 1 < τ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ C : ℝ, 0 ≤ C →
      ∃ j : ℕ, ∃ δ : ℝ, 0 < δ ∧ ∃ N₀ : ℝ, 1 ≤ N₀ ∧
        ∀ P : ZetaLargeValuePattern, N₀ ≤ P.N →
          ∀ σ : ℝ, 1/2 ≤ σ →
            P.N^(τ-δ) ≤ P.T → P.T ≤ P.N^(τ+δ) → P.N^(σ-δ) ≤ P.V →
              2*Real.pi ≤ P.T ∧ 1 ≤ P.T/(4*Real.pi*P.N) ∧
                ∀ t ∈ P.ordinates,
                  Real.sqrt (t/(2*Real.pi))*
                      (zetaReflectionTailConstant j/(4*Real.pi*P.N)^(j+1))+
                    C*(P.N/Real.sqrt (t/(2*Real.pi))+(t/(2*Real.pi))^ε) ≤ P.V/2 := by
  let a := (τ+1)/2
  let b := τ+1
  let δ := min (1/8) ((τ-1)/16)
  let ε := 1/(8*b)
  have ha : 1 < a := by dsimp [a]; linarith
  have hb : 0 < b := by dsimp [b]; linarith
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos (sub_pos.mpr hτ) (by norm_num))
  have hδsmall : δ ≤ 1/8 := min_le_left _ _
  have hδgap : δ ≤ (τ-1)/16 := min_le_right _ _
  have hε : 0 < ε := by dsimp [ε]; positivity
  refine ⟨ε,hε,?_⟩
  intro C hC
  obtain ⟨j,hj⟩ := exists_nat_ge (b/2)
  have hj' : b/2 ≤ (j : ℝ)+1 := by linarith
  let K := C*(Real.sqrt (2*Real.pi)+1)+zetaReflectionTailConstant j
  have hlarge := (tendsto_rpow_atTop hδ).eventually (eventually_ge_atTop (2*K))
  have hscale := (tendsto_rpow_atTop (show 0 < a-1 by linarith)).eventually
    (eventually_ge_atTop (4*Real.pi))
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp (hlarge.and hscale)
  refine ⟨j,δ,hδ,max 1 N₀,le_max_left _ _,?_⟩
  intro P hN σ hσ hTL hTU hV
  have hNpos : 0 < P.N := zero_lt_one.trans P.one_lt_N
  obtain ⟨hlarge,hscale⟩ := hN₀ P.N ((le_max_right _ _).trans hN)
  have hlo : P.N^a ≤ P.T :=
    (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by dsimp [a]; linarith)).trans hTL
  have hhi : P.T ≤ P.N^b := hTU.trans
    (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by dsimp [b]; linarith))
  have hTN : 4*Real.pi*P.N ≤ P.T := by
    have h := mul_le_mul_of_nonneg_right hscale hNpos.le
    have he : P.N^(a-1)*P.N = P.N^a := by
      simpa only [Real.rpow_one,sub_add_cancel] using (Real.rpow_add hNpos (a-1) 1).symm
    rw [he] at h
    exact h.trans hlo
  have hTmin : 2*Real.pi ≤ P.T := by
    have h := mul_le_mul_of_nonneg_left P.one_lt_N.le (show 0 ≤ 4*Real.pi by positivity)
    nlinarith [Real.pi_pos]
  refine ⟨hTmin,(le_div_iff₀ (by positivity : 0 < 4*Real.pi*P.N)).2 (by simpa using hTN),?_⟩
  intro t ht
  have htime : t ∈ Icc P.T (2*P.T) := by
    simpa only [P.intervalLeft_eq,P.intervalRight_eq] using P.ordinates_in_interval t ht
  have hfirst : 1-a/2 ≤ 1/2-2*δ := by dsimp [a]; linarith
  have hsecond : b*ε ≤ 1/2-2*δ := by
    have he : b*ε = 1/8 := by dsimp [ε]; field_simp
    rw [he]
    linarith
  have herr := reflection_remainders_le_power P.one_lt_N.le P.T_pos htime hlo hhi hε.le hC
    (by linarith : 0 ≤ 1/2-2*δ) hfirst hsecond j hj'
  have hbudget : K*P.N^(1/2-2*δ) ≤ P.V/2 := by
    have h := mul_le_mul_of_nonneg_right hlarge (Real.rpow_nonneg hNpos.le (1/2-2*δ))
    have he : P.N^δ*P.N^(1/2-2*δ) = P.N^(1/2-δ) := by
      rw [← Real.rpow_add hNpos]
      congr 1
      ring
    rw [he] at h
    have hv := (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le
      (by linarith : 1/2-δ ≤ σ-δ)).trans hV
    nlinarith
  exact herr.trans hbudget

end TaoTrudgianYang2025
