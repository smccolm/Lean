import TaoTrudgianYang2025.IvicSixthSmoothing
import TaoTrudgianYang2025.LargeValueExponent

/-! The restricted sixth moment bounds the genuine general-coefficient exponent. -/

noncomputable section
open Filter
namespace TaoTrudgianYang2025

theorem ivicSixth_general_loss_parameters {σ τ ε : ℝ}
    (hτ : 0 < τ) (hgap : (11/72)*τ < 2*σ-3/2) (hε : 0 < ε) :
    ∃ η δ : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < δ ∧ δ ≤ τ/2 ∧ 2*δ ≤ ε ∧
      3/2+η+(τ+δ)*(11/72+2*η) ≤ 2*(σ-δ) ∧
      7*τ*η+δ*(13+7*η) ≤ ε := by
  let g : ℝ := 2*σ-3/2-(11/72)*τ
  have hg : 0 < g := sub_pos.mpr hgap
  have ht : 0 < τ+1 := by linarith
  let η : ℝ := min 1 (min (g/(16*(τ+1))) (ε/(28*(τ+1))))
  let δ : ℝ := min (τ/2) (min (g/16) (ε/80))
  have hη : 0 < η := lt_min (by norm_num)
    (lt_min (div_pos hg (by positivity)) (div_pos hε (by positivity)))
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηg : η*(16*(τ+1)) ≤ g :=
    (le_div_iff₀ (by positivity : 0 < 16*(τ+1))).mp
      ((min_le_right _ _).trans (min_le_left _ _))
  have hηε : η*(28*(τ+1)) ≤ ε :=
    (le_div_iff₀ (by positivity : 0 < 28*(τ+1))).mp
      ((min_le_right _ _).trans (min_le_right _ _))
  have hδ : 0 < δ := lt_min (by positivity)
    (lt_min (div_pos hg (by norm_num)) (div_pos hε (by norm_num)))
  have hδg : δ*16 ≤ g :=
    (le_div_iff₀ (by norm_num : (0:ℝ) < 16)).mp
      ((min_le_right _ _).trans (min_le_left _ _))
  have hδε : δ*80 ≤ ε :=
    (le_div_iff₀ (by norm_num : (0:ℝ) < 80)).mp
      ((min_le_right _ _).trans (min_le_right _ _))
  have hδη : δ*η ≤ δ := by nlinarith
  refine ⟨η,δ,hη,hη1,hδ,min_le_left _ _,by linarith,?_,?_⟩
  · dsimp [g] at hηg hδg
    nlinarith
  · nlinarith

theorem ivicSixth_general_largeValueBound {σ τ : ℝ}
    (hτ : 0 < τ) (hgap : (11/72)*τ < 2*σ-3/2) :
    IsLargeValueBound σ τ (max (2-2*σ) (τ+9-12*σ)) := by
  intro ε hε
  obtain ⟨η,δ,hη,hη1,hδ,hδτ,hδε,hgap',hloss⟩ :=
    ivicSixth_general_loss_parameters hτ hgap hε
  obtain ⟨C,D,T₀,hC,hD,hT₀,hphysical⟩ := exists_ivicSixth_smoothed_pattern_bound hη hη1
  obtain ⟨A,hA⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop hη).eventually (eventually_ge_atTop (4*C)))
  obtain ⟨B,hB⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (by positivity : 0 < τ/2)).eventually (eventually_ge_atTop T₀))
  let K : ℝ := max 1 (max A (max B D))
  have hK : 1 ≤ K := le_max_left _ _
  have hKA : A ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hKB : B ≤ K := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hKD : D ≤ K := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨K,hK,δ,hδ,?_⟩
  intro P hPN hTl hTu hVl _
  have hN : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hT : 0 < P.T := P.T_pos
  have hPT : T₀ ≤ P.T := calc
    _ ≤ P.N^(τ/2) := hB P.N (hKB.trans hPN)
    _ ≤ P.N^(τ-δ) := Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith)
    _ ≤ _ := hTl
  have hVpow (n : ℕ) : P.N^((n:ℝ)*(σ-δ)) ≤ P.V^n := by
    have hh := pow_le_pow_left₀ (Real.rpow_nonneg hN.le _) hVl n
    rw [← Real.rpow_mul_natCast hN.le] at hh
    simpa only [mul_comm] using hh
  have hTp : P.T^(11/72+2*η) ≤ P.N^((τ+δ)*(11/72+2*η)) := by
    have hh := Real.rpow_le_rpow hT.le hTu (by linarith : 0 ≤ 11/72+2*η)
    rwa [← Real.rpow_mul hN.le] at hh
  have hNs : P.N*Real.sqrt P.N = P.N^(3/2:ℝ) := by
    calc
      _ = P.N^(1:ℝ)*P.N^(1/2:ℝ) := by rw [Real.rpow_one,Real.sqrt_eq_rpow]
      _ = _ := by rw [← Real.rpow_add hN]; norm_num
  have hsmall : 4*C*P.N*Real.sqrt P.N*P.T^(11/72+2*η) ≤ P.V^2 := by
    calc
      _ = (4*C)*P.N^(3/2:ℝ)*P.T^(11/72+2*η) := by rw [← hNs]; ring
      _ ≤ (P.N^η*P.N^(3/2:ℝ))*P.N^((τ+δ)*(11/72+2*η)) :=
        mul_le_mul (mul_le_mul_of_nonneg_right (hA P.N (hKA.trans hPN)) (by positivity))
          hTp (by positivity) (by positivity)
      _ = P.N^(3/2+η+(τ+δ)*(11/72+2*η)) := by
        rw [← Real.rpow_add hN,← Real.rpow_add hN]
        congr 1
        ring
      _ ≤ P.N^(2*(σ-δ)) := Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le hgap'
      _ ≤ _ := by simpa only [Nat.cast_ofNat] using hVpow 2
  rcases hphysical P hPT hsmall with hd | hm
  · have hExp : (2:ℝ) ≤ (max (2-2*σ) (τ+9-12*σ)+ε)+2*(σ-δ) := by
      have hh := le_max_left (2-2*σ) (τ+9-12*σ)
      linarith
    apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hN (2*(σ-δ)))).mp
    calc
      _ ≤ (P.ordinates.card:ℝ)*P.V^2 :=
        mul_le_mul_of_nonneg_left (by simpa only [Nat.cast_ofNat] using hVpow 2) (by positivity)
      _ ≤ D*P.N^2 := hd
      _ ≤ K*P.N^2 := mul_le_mul_of_nonneg_right hKD (sq_nonneg _)
      _ ≤ K*P.N^((max (2-2*σ) (τ+9-12*σ)+ε)+2*(σ-δ)) := by
        rw [← Real.rpow_two]
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le hExp) (zero_le_one.trans hK)
      _ = _ := by rw [Real.rpow_add hN,mul_assoc]
  · have hTp' : P.T^(1+7*η) ≤ P.N^((τ+δ)*(1+7*η)) := by
      have hh := Real.rpow_le_rpow hT.le hTu (by linarith : 0 ≤ 1+7*η)
      rwa [← Real.rpow_mul hN.le] at hh
    have hExp : 9+(τ+δ)*(1+7*η) ≤
        (max (2-2*σ) (τ+9-12*σ)+ε)+12*(σ-δ) := by
      have hh := le_max_right (2-2*σ) (τ+9-12*σ)
      nlinarith
    apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hN (12*(σ-δ)))).mp
    calc
      _ ≤ (P.ordinates.card:ℝ)*P.V^12 :=
        mul_le_mul_of_nonneg_left (by simpa only [Nat.cast_ofNat] using hVpow 12) (by positivity)
      _ ≤ D*P.N^9*P.T^(1+7*η) := hm
      _ ≤ K*P.N^9*P.N^((τ+δ)*(1+7*η)) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hKD (by positivity)) hTp'
          (by positivity) (by positivity)
      _ = K*P.N^(9+(τ+δ)*(1+7*η)) := by
        rw [mul_assoc,← Real.rpow_ofNat,← Real.rpow_add hN]
      _ ≤ K*P.N^((max (2-2*σ) (τ+9-12*σ)+ε)+12*(σ-δ)) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le hExp) (zero_le_one.trans hK)
      _ = _ := by rw [Real.rpow_add hN,mul_assoc]

theorem ivicSixth_general_largeValueExponent_le {σ τ : ℝ}
    (hτ : 0 < τ) (hgap : (11/72)*τ < 2*σ-3/2) :
    largeValueExponent σ τ ≤ ((max (2-2*σ) (τ+9-12*σ):ℝ):EReal) :=
  largeValueExponent_le_of_bound (ivicSixth_general_largeValueBound hτ hgap)

end TaoTrudgianYang2025
