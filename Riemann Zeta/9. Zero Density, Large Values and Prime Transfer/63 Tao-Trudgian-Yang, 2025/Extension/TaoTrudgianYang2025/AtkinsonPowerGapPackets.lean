import TaoTrudgianYang2025.AtkinsonPowerGapBudget

/-!
# Actual source packets with closed localized power budgets

Both phase-pair sums and the dyadic sum have been estimated. The same
physical source cutoff and local-mean error restrictions remain visible.
The localized statements quantify their constants before the interval;
the physical statements derive that interval from [H,2H].
-/

noncomputable section

open RiemannZeta.GuthMaynard

namespace TaoTrudgianYang2025

theorem exists_atkinsonStationaryPacket_sq_le_localizedPowers {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧ ∀ H G A L : ℝ, ∀ W : Finset ℝ,
      H₀ ≤ H → 0 < G → IsSeparated G W →
      (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H ∧ t^δ ≤ G ∧ G ≤ t^(1/2-δ)) →
      (∀ t ∈ W, A ≤ t ∧ t ≤ A+L) →
      (∑ t ∈ W, ‖atkinsonStationaryLeadingSum t G (Real.log t)‖)^2 ≤
        C*G^2*H^(-(1/2:ℝ))*
          atkinsonPowerGapBudget η H G L (atkinsonSourceCutoff (2*H) G (Real.log (2*H))) W.card := by
  obtain ⟨C,hC,B,hB,hsource⟩ := exists_atkinsonStationaryPacket_sq_le_separatedNear hδ hη
  refine ⟨C,hC,B,hB,?_⟩
  intro H G A L W hH hG hSep hrange hlocal
  have hH0 : 0 < H := by linarith [hB.trans hH]
  have hs := hsource H G W hH hG hSep hrange
  have hf := atkinsonSeparatedGapBudget_le_localized (η := η) (G := G)
    (N := atkinsonSourceCutoff (2*H) G (Real.log (2*H))) hH0
    (fun t ht => ⟨(hrange t ht).1,(hrange t ht).2.1⟩)
    (atkinson_height_interval_diameter hlocal)
  have hp := atkinsonLocalizedGapBudget_le_power (η := η) (L := L)
    (atkinsonSourceCutoff (2*H) G (Real.log (2*H))) W.card hH0 hG hη.le
  exact hs.trans (mul_le_mul_of_nonneg_left (hf.trans hp) (by positivity))

theorem exists_atkinsonLocalMeanExcessPacket_sq_le_localizedPowers
    {δ ε η : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℝ, 0 < D ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧
      ∀ H G A L : ℝ, ∀ W : Finset ℝ, H₀ ≤ H → 0 < G → IsSeparated G W →
      (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H ∧ t^δ ≤ G ∧ G ≤ t^(1/2-δ) ∧ t^(1/4 : ℝ) ≤ G) →
      (∀ t ∈ W, A ≤ t ∧ t ≤ A+L) →
      (∑ t ∈ W, atkinsonLocalMeanExcess G t (C*(G*Real.log t+t^(1/4+ε))))^2 ≤
        D*G^2*H^(-(1/2:ℝ))*
          atkinsonPowerGapBudget η H G L (atkinsonSourceCutoff (2*H) G (Real.log (2*H))) W.card := by
  obtain ⟨C,hC,D,hD,B,hB,hsource⟩ := exists_atkinsonLocalMeanExcessPacket_sq_le_separatedNear hδ hε hη
  refine ⟨C,hC,D,hD,B,hB,?_⟩
  intro H G A L W hH hG hSep hrange hlocal
  have hH0 : 0 < H := by linarith [hB.trans hH]
  have hs := hsource H G W hH hG hSep hrange
  have hf := atkinsonSeparatedGapBudget_le_localized (η := η) (G := G)
    (N := atkinsonSourceCutoff (2*H) G (Real.log (2*H))) hH0
    (fun t ht => ⟨(hrange t ht).1,(hrange t ht).2.1⟩)
    (atkinson_height_interval_diameter hlocal)
  have hp := atkinsonLocalizedGapBudget_le_power (η := η) (L := L)
    (atkinsonSourceCutoff (2*H) G (Real.log (2*H))) W.card hH0 hG hη.le
  exact hs.trans (mul_le_mul_of_nonneg_left (hf.trans hp) (by positivity))

theorem exists_atkinsonLocalMeanExcessPacket_sq_le_localizedPowers_above_fourthRoot
    {δ κ η : ℝ} (hδ : 0 < δ) (hκ : 0 < κ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℝ, 0 < D ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧
      ∀ H G A L : ℝ, ∀ W : Finset ℝ, H₀ ≤ H → 0 < G → IsSeparated G W →
      (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H ∧ t^δ ≤ G ∧ G ≤ t^(1/2-δ) ∧ t^(1/4+κ) ≤ G) →
      (∀ t ∈ W, A ≤ t ∧ t ≤ A+L) →
      (∑ t ∈ W, atkinsonLocalMeanExcess G t (C*G*Real.log t))^2 ≤
        D*G^2*H^(-(1/2:ℝ))*
          atkinsonPowerGapBudget η H G L (atkinsonSourceCutoff (2*H) G (Real.log (2*H))) W.card := by
  obtain ⟨C,hC,D,hD,B,hB,hsource⟩ := exists_atkinsonLocalMeanExcessPacket_sq_le_separatedNear_above_fourthRoot hδ hκ hη
  refine ⟨C,hC,D,hD,B,hB,?_⟩
  intro H G A L W hH hG hSep hrange hlocal
  have hH0 : 0 < H := by linarith [hB.trans hH]
  have hs := hsource H G W hH hG hSep hrange
  have hf := atkinsonSeparatedGapBudget_le_localized (η := η) (G := G)
    (N := atkinsonSourceCutoff (2*H) G (Real.log (2*H))) hH0
    (fun t ht => ⟨(hrange t ht).1,(hrange t ht).2.1⟩)
    (atkinson_height_interval_diameter hlocal)
  have hp := atkinsonLocalizedGapBudget_le_power (η := η) (L := L)
    (atkinsonSourceCutoff (2*H) G (Real.log (2*H))) W.card hH0 hG hη.le
  exact hs.trans (mul_le_mul_of_nonneg_left (hf.trans hp) (by positivity))

theorem exists_atkinsonStationaryPacket_sq_le_physicalPowers {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧ ∀ H G : ℝ, ∀ W : Finset ℝ,
      H₀ ≤ H → 0 < G → IsSeparated G W →
      (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H ∧ t^δ ≤ G ∧ G ≤ t^(1/2-δ)) →
      (∑ t ∈ W, ‖atkinsonStationaryLeadingSum t G (Real.log t)‖)^2 ≤
        C*G^2*H^(-(1/2:ℝ))*
          atkinsonPowerGapBudget η H G H (atkinsonSourceCutoff (2*H) G (Real.log (2*H))) W.card := by
  obtain ⟨C,hC,B,hB,hsource⟩ := exists_atkinsonStationaryPacket_sq_le_localizedPowers hδ hη
  refine ⟨C,hC,B,hB,?_⟩
  intro H G W hH hG hSep hrange
  exact hsource H G H H W hH hG hSep hrange (fun t ht =>
    ⟨(hrange t ht).1,by linarith [(hrange t ht).2.1]⟩)

theorem exists_atkinsonLocalMeanExcessPacket_sq_le_physicalPowers
    {δ ε η : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℝ, 0 < D ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧
      ∀ H G : ℝ, ∀ W : Finset ℝ, H₀ ≤ H → 0 < G → IsSeparated G W →
      (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H ∧ t^δ ≤ G ∧ G ≤ t^(1/2-δ) ∧ t^(1/4 : ℝ) ≤ G) →
      (∑ t ∈ W, atkinsonLocalMeanExcess G t (C*(G*Real.log t+t^(1/4+ε))))^2 ≤
        D*G^2*H^(-(1/2:ℝ))*
          atkinsonPowerGapBudget η H G H (atkinsonSourceCutoff (2*H) G (Real.log (2*H))) W.card := by
  obtain ⟨C,hC,D,hD,B,hB,hsource⟩ := exists_atkinsonLocalMeanExcessPacket_sq_le_localizedPowers hδ hε hη
  refine ⟨C,hC,D,hD,B,hB,?_⟩
  intro H G W hH hG hSep hrange
  exact hsource H G H H W hH hG hSep hrange (fun t ht =>
    ⟨(hrange t ht).1,by linarith [(hrange t ht).2.1]⟩)

theorem exists_atkinsonLocalMeanExcessPacket_sq_le_physicalPowers_above_fourthRoot
    {δ κ η : ℝ} (hδ : 0 < δ) (hκ : 0 < κ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℝ, 0 < D ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧
      ∀ H G : ℝ, ∀ W : Finset ℝ, H₀ ≤ H → 0 < G → IsSeparated G W →
      (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H ∧ t^δ ≤ G ∧ G ≤ t^(1/2-δ) ∧ t^(1/4+κ) ≤ G) →
      (∑ t ∈ W, atkinsonLocalMeanExcess G t (C*G*Real.log t))^2 ≤
        D*G^2*H^(-(1/2:ℝ))*
          atkinsonPowerGapBudget η H G H (atkinsonSourceCutoff (2*H) G (Real.log (2*H))) W.card := by
  obtain ⟨C,hC,D,hD,B,hB,hsource⟩ := exists_atkinsonLocalMeanExcessPacket_sq_le_localizedPowers_above_fourthRoot hδ hκ hη
  refine ⟨C,hC,D,hD,B,hB,?_⟩
  intro H G W hH hG hSep hrange
  exact hsource H G H H W hH hG hSep hrange (fun t ht =>
    ⟨(hrange t ht).1,by linarith [(hrange t ht).2.1]⟩)

end TaoTrudgianYang2025
