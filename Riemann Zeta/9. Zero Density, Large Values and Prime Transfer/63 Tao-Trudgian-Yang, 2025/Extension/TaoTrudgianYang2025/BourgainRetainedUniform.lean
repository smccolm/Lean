import TaoTrudgianYang2025.BourgainMomentWindows

/-!
# The retained-zeta estimate with one physical epsilon loss

The actual integer smoothing radius is enlarged to T^epsilon by a
proved monotonicity bridge. Constants are uniform before the pattern.
The high-value threshold remains explicit at this intermediate layer.
-/

open Filter Finset RiemannZeta.GuthMaynard

noncomputable section

namespace TaoTrudgianYang2025

/-- The three retained source terms, with one uniform loss and the actual
zeta moment at physical radius T^epsilon. This still displays the numerical
threshold required by the present near-term absorption argument. -/
theorem bourgain_retained_cardinality_uniform (cutoff : GMSmoothCutoff)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C T₀ : ℝ, 1 ≤ C ∧ 2 ≤ T₀ ∧
      ∀ P : LargeValuePattern,
        30 ≤ P.scale → 1 < P.V → T₀ ≤ P.T → P.N ≤ P.T →
        C*P.T^ε*P.N^6 ≤ (P.V-1)^8 →
        ∃ W : Finset ℝ,
          W ⊆ P.reflectedOrdinates ∧ IsSeparated 2 W ∧ InBaseInterval P.T W ∧
          (P.ordinates.card : ℝ) ≤ C*P.T^ε*(W.card : ℝ) ∧
          (P.ordinates.card : ℝ) ≤ C*P.T^ε *
            (P.N^2/(P.V-1)^2 + P.T^2*P.N^4/(P.V-1)^8 +
              P.N^3*Real.sqrt (bourgainZetaDifferenceMoment W (P.T^ε))/(P.V-1)^4) := by
  let ν := ε/3
  have hν : 0 < ν := by dsimp [ν]; positivity
  have hnue : ν < ε := by dsimp [ν]; linarith
  have h2nue : 2*ν ≤ ε := by dsimp [ν]; linarith
  obtain ⟨θ,B,Ta,hθ,hθ1,hθν,hB,hTa,hp⟩ := bourgain_high_value_pattern_retained cutoff hν
  obtain ⟨Tr,hTr⟩ := eventually_atTop.mp
    (eventually_bourgain_smoothing_radius_le hθ.le (hθν.trans_lt hnue))
  let S : ℝ := (2*(4 : ℝ)^4*(2 : ℝ)^2*(3 : ℝ)^8)*B
  let C₁ : ℝ := 72*B
  let C₂ : ℝ := 2*B^2*(4 : ℝ)^4*(3 : ℝ)^8
  let C₃ : ℝ := 2*B*Real.sqrt (2*B)*(4 : ℝ)^2*(3 : ℝ)^4
  let C : ℝ := 1+S+C₁+C₂+C₃+B
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hC₁ : 0 ≤ C₁ := by dsimp [C₁]; positivity
  have hC₂ : 0 ≤ C₂ := by dsimp [C₂]; positivity
  have hC₃ : 0 ≤ C₃ := by dsimp [C₃]; positivity
  have hC : 1 ≤ C := by dsimp [C]; linarith
  have hSC : S ≤ C := by dsimp [C]; linarith
  have h1C : C₁ ≤ C := by dsimp [C]; linarith
  have h2C : C₂ ≤ C := by dsimp [C]; linarith
  have h3C : C₃ ≤ C := by dsimp [C]; linarith
  have hBC : B ≤ C := by dsimp [C]; linarith
  refine ⟨C,max Ta Tr,hC,hTa.trans (le_max_left _ _),?_⟩
  intro P hN hV hT hNT hvalue
  have hT1 : 1 ≤ P.T := by linarith [hTa.trans ((le_max_left _ _).trans hT)]
  have hTp := P.T_pos
  have hNp : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hv : 0 < P.V-1 := by linarith
  have ht1 := Real.rpow_le_rpow_of_exponent_le hT1 hnue.le
  have ht2 := Real.rpow_le_rpow_of_exponent_le hT1 h2nue
  have ha : 2*(B*P.T^ν*(4*P.N)^4)*(2*P.N)^2 ≤ ((P.V-1)/3)^8 := by
    rw [div_pow]
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 3^8)).mpr
    rw [bourgain_retained_absorption_identity]
    calc
      _ = S*P.T^ν*P.N^6 := by dsimp [S]; ring
      _ ≤ C*P.T^ε*P.N^6 := by gcongr
      _ ≤ _ := hvalue
  obtain ⟨W,hsub,hsep,hbase,hcard,hbound⟩ :=
    hp P hN hV ((le_max_left _ _).trans hT) hNT ha
  refine ⟨W,hsub,hsep,hbase,hcard.trans ?_,?_⟩
  · gcongr
  let H := heathBrownSmoothingHeight P.T θ
  let M := bourgainZetaDifferenceMoment W (P.T^ε)
  have hradius : (H : ℝ)+1 ≤ P.T^ε := hTr P.T ((le_max_right _ _).trans hT)
  have hmoment : bourgainZetaDifferenceMoment W ((H : ℝ)+1) ≤ M :=
    bourgainZetaDifferenceMoment_mono W (by positivity) hradius
  let X := P.N^2/(P.V-1)^2
  let Y := P.T^2*P.N^4/(P.V-1)^8
  let Z := P.N^3*Real.sqrt M/(P.V-1)^4
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hY : 0 ≤ Y := by dsimp [Y]; positivity
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have hpow := (jutila_local_smoothing_powers (B := B) (ν := ν) hTp).1
  have hsqrt := bourgain_retained_sqrt_coefficient_le hB.le hT1 hν.le
  have hc3 :
      2*(B*P.T^ν)*Real.sqrt (2*(B*P.T^ν))*(4 : ℝ)^2*(3 : ℝ)^4 ≤ C₃*P.T^(2*ν) := by
    have hh := mul_le_mul_of_nonneg_left hsqrt
      (by positivity : (0 : ℝ) ≤ 2*(4 : ℝ)^2*(3 : ℝ)^4)
    convert hh using 1 <;> dsimp [C₃] <;> ring
  have hform :
      bourgainRetainedCardinalityBound P.N P.T P.V (B*P.T^ν)
        (bourgainZetaDifferenceMoment W ((H : ℝ)+1)) ≤
          C₁*P.T^ν*X + C₂*P.T^(2*ν)*Y + C₃*P.T^(2*ν)*Z := by
    rw [bourgainRetainedCardinalityBound_expand _ _ _ _ _ (by positivity) hV, hpow]
    have hr : Real.sqrt (bourgainZetaDifferenceMoment W ((H : ℝ)+1)) ≤ Real.sqrt M :=
      Real.sqrt_le_sqrt hmoment
    calc
      _ ≤ (72*(B*P.T^ν))*P.N^2/(P.V-1)^2 +
          (2*(B^2*P.T^(2*ν))*(4 : ℝ)^4*(3 : ℝ)^8)*P.T^2*P.N^4/(P.V-1)^8 +
          (C₃*P.T^(2*ν))*P.N^3*Real.sqrt M/(P.V-1)^4 := by gcongr
      _ = _ := by dsimp [C₁,C₂,X,Y,Z]; ring
  have h1 : C₁*P.T^ν ≤ C*P.T^ε := by gcongr
  have h2 : C₂*P.T^(2*ν) ≤ C*P.T^ε := by gcongr
  have h3 : C₃*P.T^(2*ν) ≤ C*P.T^ε := by gcongr
  calc
    _ ≤ bourgainRetainedCardinalityBound P.N P.T P.V (B*P.T^ν)
        (bourgainZetaDifferenceMoment W ((H : ℝ)+1)) := hbound
    _ ≤ C₁*P.T^ν*X + C₂*P.T^(2*ν)*Y + C₃*P.T^(2*ν)*Z := hform
    _ ≤ C*P.T^ε*X+C*P.T^ε*Y+C*P.T^ε*Z := by gcongr
    _ = _ := by dsimp [X,Y,Z,M]; ring

end TaoTrudgianYang2025
