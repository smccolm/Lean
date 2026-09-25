import TaoTrudgianYang2025.AtkinsonPairPhysicalBudget
import TaoTrudgianYang2025.AtkinsonPairDyadicBudget

/-! Uniform model entry at the literal Atkinson source cutoff. -/

noncomputable section
open Filter
namespace TaoTrudgianYang2025

theorem exists_atkinsonPhysicalCutoff_pair_geometry {δ η : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) :
    ∃ H₀ : ℝ, 40000 ≤ H₀ ∧ ∀ H G : ℝ, H₀ ≤ H →
      H^δ ≤ G → G ≤ Real.sqrt (2*H) →
      1 ≤ Real.log (2*H) ∧
      (atkinsonSourceCutoff (2*H) G (Real.log (2*H)) : ℝ) ≤ H ∧
      Real.pi*(atkinsonSourceCutoff (2*H) G (Real.log (2*H)) : ℝ)/(2*H) < η := by
  obtain ⟨A,hA,hgeometry⟩ := exists_atkinsonPhysicalCutoff_prefix_geometry hδ
  have hevent : ∀ᶠ H : ℝ in atTop,
      A ≤ H ∧ (Real.log (2*H))^2 ≤ H^δ ∧
      37*Real.pi/η < H^δ ∧ 1 ≤ Real.log H := by
    filter_upwards [eventually_ge_atTop A,
      eventually_atkinson_height_log_pow_le_rpow 2 hδ,
      (tendsto_rpow_atTop hδ).eventually (eventually_gt_atTop (37*Real.pi/η)),
      Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)] with H h1 h2 h3 h4
    exact ⟨h1,h2,h3,h4⟩
  obtain ⟨B,hB⟩ := eventually_atTop.mp hevent
  refine ⟨max A B,hA.trans (le_max_left _ _),?_⟩
  intro H G hH hwidth hupper
  obtain ⟨hAH,hlogpow,hpowlarge,hlogH⟩ := hB H ((le_max_right _ _).trans hH)
  have hH1 : 1 ≤ H := by linarith [hA.trans hAH]
  have hH0 : 0 < H := by linarith
  have hpow : 0 < H^δ := Real.rpow_pos_of_pos hH0 δ
  have hG : 0 < G := hpow.trans_le hwidth
  have hlog : 1 ≤ Real.log (2*H) :=
    hlogH.trans (Real.log_le_log hH0 (by linarith))
  have hN : (atkinsonSourceCutoff (2*H) G (Real.log (2*H)) : ℝ) ≤ H := by
    have hc := hgeometry H G hAH hwidth
    have hn := Nat.cast_nonneg (α := ℝ) (atkinsonSourceCutoff (2*H) G (Real.log (2*H)))
    linarith
  refine ⟨hlog,hN,?_⟩
  have hcut := atkinsonPhysicalCutoff_le_natural hH1 hG hupper hlog
  have hs := pow_le_pow_left₀ hpow.le hwidth 2
  calc
    _ ≤ Real.pi*(74*H*(Real.log (2*H))^2/G^2)/(2*H) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hcut Real.pi_pos.le) (by positivity)
    _ = 37*Real.pi*(Real.log (2*H))^2/G^2 := by field_simp; ring
    _ ≤ 37*Real.pi*H^δ/G^2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlogpow (by positivity)) (sq_nonneg G)
    _ ≤ 37*Real.pi*H^δ/(H^δ)^2 :=
      div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hpow) hs
    _ = 37*Real.pi/H^δ := by field_simp
    _ < η := (div_lt_iff₀ hpow).2 (by
      have h := (div_lt_iff₀ hη).mp hpowlarge
      nlinarith)

theorem ExponentPair.atkinson_physical_gram_budget {k l δ ν : ℝ}
    (hpair : ExponentPair k l) (hδ : 0 < δ) (hν : 0 < ν) :
    ∃ F : ℝ, 0 < F ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧
      ∀ (H G L : ℝ) (W : Finset ℝ), H₀ ≤ H →
        H^δ ≤ G → G ≤ Real.sqrt (2*H) → 0 < L → L ≤ H →
        RiemannZeta.GuthMaynard.IsSeparated G W →
        (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H) →
        (∀ t ∈ W, ∀ u ∈ W, |u-t| ≤ L) →
        G^2*H^(-(1/2:ℝ))*
          atkinsonDyadicGramBudget (atkinsonSourceCutoff (2*H) G (Real.log (2*H))) W ≤
          F*H^ν*((W.card : ℝ)*H/G+
            (W.card : ℝ)^2*L^k*H^(l-k)*G^(1+k-2*l)) := by
  obtain ⟨η,hη,C,hC,D,hD,hgram⟩ :=
    hpair.atkinson_dyadic_gram_le_pair_budget (show 0 < ν/6 by linarith)
  obtain ⟨A,hA,hgeometry⟩ := exists_atkinsonPhysicalCutoff_pair_geometry hδ hη
  obtain ⟨B,hB⟩ := eventually_atTop.mp
    (eventually_atkinson_height_log_pow_le_rpow 5 (show 0 < ν/2 by linarith))
  let K := 10000*C*(1/Real.log 2+1)^2
  have hK : 0 < K := by
    have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    dsimp [K]
    positivity
  refine ⟨D*K,mul_pos hD hK,max A B,hA.trans (le_max_left _ _),?_⟩
  intro H G L W hH hwidth hupper hL hLH hsep hrange hdiam
  have hAH : A ≤ H := (le_max_left _ _).trans hH
  have hBH : B ≤ H := (le_max_right _ _).trans hH
  have hH1 : 1 ≤ H := by linarith [hA.trans hAH]
  have hH0 : 0 < H := by linarith
  have hG1 : 1 ≤ G := (Real.one_le_rpow hH1 hδ.le).trans hwidth
  have hG : 0 < G := by linarith
  obtain ⟨hlog,hN,hsmall⟩ := hgeometry H G hAH hwidth hupper
  have hb := hgram H G L (atkinsonSourceCutoff (2*H) G (Real.log (2*H))) W
    hH1 hG hL hLH hN hsep hrange hdiam hsmall
  have ht := atkinsonPairPowerBudget_physical_log_le W.card hC hH1 hG1 hL.le hLH hlog
    hpair.inTriangle hN (atkinsonPhysicalCutoff_le_natural hH1 hG hupper hlog)
  have he : H^(3*(ν/6))*H^(ν/2) = H^ν := by
    rw [← Real.rpow_add hH0]; congr 1; ring
  calc
    _ ≤ (G^2*H^(-(1/2:ℝ)))*
        (D*H^(3*(ν/6))*atkinsonPairPowerBudget C k l H G L
          (atkinsonSourceCutoff (2*H) G (Real.log (2*H))) W.card) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = D*H^(3*(ν/6))*(G^2*H^(-(1/2:ℝ))*
        atkinsonPairPowerBudget C k l H G L
          (atkinsonSourceCutoff (2*H) G (Real.log (2*H))) W.card) := by ring
    _ ≤ D*H^(3*(ν/6))*(K*(Real.log (2*H))^5*
        ((W.card : ℝ)*H/G+(W.card : ℝ)^2*L^k*H^(l-k)*G^(1+k-2*l))) :=
      mul_le_mul_of_nonneg_left ht (by positivity)
    _ ≤ D*H^(3*(ν/6))*(K*H^(ν/2)*
        ((W.card : ℝ)*H/G+(W.card : ℝ)^2*L^k*H^(l-k)*G^(1+k-2*l))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left (hB H hBH) hK.le
    _ = _ := by
      calc
        _ = (D*K)*(H^(3*(ν/6))*H^(ν/2))*
            ((W.card : ℝ)*H/G+(W.card : ℝ)^2*L^k*H^(l-k)*G^(1+k-2*l)) := by ring
        _ = _ := by rw [he]

end TaoTrudgianYang2025
