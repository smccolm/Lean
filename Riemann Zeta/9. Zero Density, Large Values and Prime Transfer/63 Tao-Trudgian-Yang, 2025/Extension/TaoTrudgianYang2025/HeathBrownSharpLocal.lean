import TaoTrudgianYang2025.HeathBrownSharpAsymptotics
import TaoTrudgianYang2025.ClassicalMeanSquareBound

/-! The actual finite dichotomy gives a uniform local large-value exponent. -/

noncomputable section
open Filter
namespace TaoTrudgianYang2025

theorem heathBrown_sharp_local_largeValueBound {σ τ : ℝ}
    (hσ : 7/8 ≤ σ) (hτ : 3/2 ≤ τ) :
    IsLargeValueBound σ τ (max (2-2*σ) (18+2*τ-24*σ)) := by
  intro ε hε
  let δ : ℝ := min (1/100) (ε/108)
  let η : ℝ := min (ε/4) (ε/(4*(τ+1)))
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  have hd1 : δ ≤ 1/100 := min_le_left _ _
  have hde : δ ≤ ε/108 := min_le_right _ _
  have he1 : η ≤ ε/4 := min_le_left _ _
  have het : η ≤ ε/(4*(τ+1)) := min_le_right _ _
  have het' : η*(τ+1) ≤ ε/4 := by
    have hh := (le_div_iff₀ (by positivity : (0 : ℝ) < 4*(τ+1))).mp het
    nlinarith
  have hediag : η+2*δ ≤ ε := by linarith
  have hefar : 26*δ+η*(τ+δ) ≤ ε := by
    have hh := mul_le_mul_of_nonneg_left (show τ+δ ≤ τ+1 by linarith) hη.le
    nlinarith
  obtain ⟨D,T₀,hD,hT₀,hfinite⟩ := exists_heathBrown_sharp_finite_bound hη
  obtain ⟨Na,hNa⟩ := eventually_atTop.mp eventually_heathBrown_near_value_factor
  obtain ⟨Nd,hNd⟩ := eventually_atTop.mp (eventually_heathBrown_diagonal_factor hη)
  let C := max 1 (max D (max T₀ (max Na Nd)))
  have hC : 1 ≤ C := le_max_left _ _
  have hCD : D ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCT : T₀ ≤ C := (le_max_left _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))
  have hCA : Na ≤ C := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hCN : Nd ≤ C := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  refine ⟨C,hC,δ,hδ,?_⟩
  intro P hN hTl hTu hVl _
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hN1 : 1 ≤ P.N := P.one_lt_N.le
  have hT : T₀ ≤ P.T := calc
    _ ≤ P.N := hCT.trans hN
    _ ≤ P.N^(τ-δ) := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hN1
        (show 1 ≤ τ-δ by linarith)
    _ ≤ P.T := hTl
  have hVpow (k : ℕ) : P.N^((σ-δ)*(k : ℝ)) ≤ P.V^k := by
    rw [Real.rpow_mul_natCast hNp.le]
    exact pow_le_pow_left₀ (Real.rpow_nonneg hNp.le _) hVl k
  have hvalue : 4*P.N*(2+200*Real.sqrt (P.N^(7/5 : ℝ))) ≤ P.V^2 := calc
    _ ≤ P.N^(171/100 : ℝ) := hNa P.N (hCA.trans hN)
    _ ≤ P.N^((σ-δ)*(2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    _ ≤ P.V^2 := hVpow 2
  have hR : (0 : ℝ) ≤ P.ordinates.card := Nat.cast_nonneg _
  rcases hfinite P hT hvalue with hsmall | hlarge
  · have hr : (P.ordinates.card : ℝ) ≤ P.N^((2+η)-(σ-δ)*2) := by
      rw [Real.rpow_sub hNp]
      apply (le_div_iff₀ (Real.rpow_pos_of_pos hNp _)).mpr
      exact (mul_le_mul_of_nonneg_left (hVpow 2) hR).trans
        (hsmall.trans (hNd P.N (hCN.trans hN)))
    calc
      _ ≤ P.N^((2+η)-(σ-δ)*2) := hr
      _ ≤ P.N^(max (2-2*σ) (18+2*τ-24*σ)+ε) :=
        Real.rpow_le_rpow_of_exponent_le hN1
          (by have hh := le_max_left (2-2*σ) (18+2*τ-24*σ); linarith)
      _ ≤ C*P.N^(max (2-2*σ) (18+2*τ-24*σ)+ε) :=
        le_mul_of_one_le_left (Real.rpow_nonneg hNp.le _) hC
  · have htPower : P.T^(2+η) ≤ P.N^((τ+δ)*(2+η)) := by
      rw [Real.rpow_mul hNp.le]
      exact Real.rpow_le_rpow P.T_pos.le hTu (by linarith)
    have hr : (P.ordinates.card : ℝ) ≤ D*P.N^((18+(τ+δ)*(2+η))-(σ-δ)*24) := by
      rw [Real.rpow_sub hNp,← mul_div_assoc]
      apply (le_div_iff₀ (Real.rpow_pos_of_pos hNp _)).mpr
      calc
        _ ≤ (P.ordinates.card : ℝ)*P.V^24 :=
          mul_le_mul_of_nonneg_left (hVpow 24) hR
        _ ≤ D*P.N^18*P.T^(2+η) := hlarge
        _ ≤ D*P.N^18*P.N^((τ+δ)*(2+η)) :=
          mul_le_mul_of_nonneg_left htPower (mul_nonneg hD.le (pow_nonneg hNp.le _))
        _ = _ := by rw [Real.rpow_add hNp,Real.rpow_ofNat]; ring
    exact hr.trans (mul_le_mul hCD
      (Real.rpow_le_rpow_of_exponent_le hN1 (by
        have hh := le_max_right (2-2*σ) (18+2*τ-24*σ)
        nlinarith))
      (Real.rpow_nonneg hNp.le _) (zero_le_one.trans hC))

end TaoTrudgianYang2025
