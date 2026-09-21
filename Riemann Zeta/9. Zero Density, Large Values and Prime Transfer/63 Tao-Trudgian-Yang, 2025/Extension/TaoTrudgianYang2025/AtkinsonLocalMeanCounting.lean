import TaoTrudgianYang2025.AtkinsonGlobalCardinality

/-!
# Sixth-power counting for actual local zeta-mean excesses

No analytic packet estimate or localization covering is assumed:
both are consumed from the preceding source theorems. The threshold
is the actual integral excess, not a pointwise zeta-value proxy.
-/

noncomputable section

open RiemannZeta.GuthMaynard MeasureTheory

namespace TaoTrudgianYang2025

theorem atkinsonLocalMeanExcess_threshold_iff {G t error Y : ℝ} (hY : 0 < Y) :
    Y ≤ atkinsonLocalMeanExcess G t error ↔
      error+Y ≤ ∫ u in t-G..t+G, zetaMomentCriticalNorm u^2 := by
  unfold atkinsonLocalMeanExcess
  rw [le_max_iff]
  constructor
  · rintro (h | h)
    · linarith
    · linarith
  · intro h
    right
    linarith

theorem exists_atkinsonLocalMeanExcess_card_le
    {δ ε ν : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (hν : 0 < ν) :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℝ, 0 < D ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧
      ∀ H G Y : ℝ, ∀ W : Finset ℝ, H₀ ≤ H → 0 < G → 0 < Y → IsSeparated G W →
      (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H ∧ t^δ ≤ G ∧ G ≤ t^(1/2-δ) ∧ t^(1/4 : ℝ) ≤ G) →
      (∀ t ∈ W, Y ≤ atkinsonLocalMeanExcess G t (C*(G*Real.log t+t^(1/4+ε)))) →
      (W.card:ℝ) ≤ D*H^ν*(H/(G*Y^2)+H^2/Y^6) := by
  obtain ⟨C,hC,D,hD,B,hB,hsource⟩ :=
    exists_atkinsonLocalMeanExcessPacket_sq_le_localizedPhysical
      hδ hε (show 0 < ν/3 by linarith)
  refine ⟨C,hC,2*D+32*D^3,by positivity,B,hB,?_⟩
  intro H G Y W hH hG hY hSep hrange hlarge
  have hH1 : 1 ≤ H := by linarith [hB.trans hH]
  have hH0 : 0 < H := by linarith
  have hA : 0 < D*H^(ν/3) := by positivity
  have hpacket : ∀ U : Finset ℝ, U ⊆ W →
      ∀ A : ℝ, (∀ t ∈ U, A ≤ t ∧ t ≤ A+atkinsonAbsorptionLength (D*H^(ν/3)) G Y) →
      (∑ t ∈ U, atkinsonLocalMeanExcess G t (C*(G*Real.log t+t^(1/4+ε))))^2 ≤
        (D*H^(ν/3))*((U.card:ℝ)*H/G+(U.card:ℝ)^2*
          Real.sqrt (G*atkinsonAbsorptionLength (D*H^(ν/3)) G Y)) := by
    intro U hsub A hlocal
    have hsepU : IsSeparated G U := by
      intro x hx y hy hxy
      exact hSep x (hsub hx) y (hsub hy) hxy
    exact hsource H G A (atkinsonAbsorptionLength (D*H^(ν/3)) G Y)
      U hH hG hsepU (fun t ht => hrange t (hsub ht)) hlocal
  have hc := atkinson_card_le_of_local_packets hA hH0.le hG hY
    (fun t ht => ⟨(hrange t ht).1,(hrange t ht).2.1⟩) hlarge hpacket
  exact hc.trans (atkinson_count_exponent_budget hD.le hH1 hG hY hν.le)

theorem exists_atkinsonLocalMeanExcess_card_le_above_fourthRoot
    {δ κ ν : ℝ} (hδ : 0 < δ) (hκ : 0 < κ) (hν : 0 < ν) :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℝ, 0 < D ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧
      ∀ H G Y : ℝ, ∀ W : Finset ℝ, H₀ ≤ H → 0 < G → 0 < Y → IsSeparated G W →
      (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H ∧ t^δ ≤ G ∧ G ≤ t^(1/2-δ) ∧ t^(1/4+κ) ≤ G) →
      (∀ t ∈ W, Y ≤ atkinsonLocalMeanExcess G t (C*G*Real.log t)) →
      (W.card:ℝ) ≤ D*H^ν*(H/(G*Y^2)+H^2/Y^6) := by
  obtain ⟨C,hC,D,hD,B,hB,hsource⟩ :=
    exists_atkinsonLocalMeanExcessPacket_sq_le_localizedPhysical_above_fourthRoot
      hδ hκ (show 0 < ν/3 by linarith)
  refine ⟨C,hC,2*D+32*D^3,by positivity,B,hB,?_⟩
  intro H G Y W hH hG hY hSep hrange hlarge
  have hH1 : 1 ≤ H := by linarith [hB.trans hH]
  have hH0 : 0 < H := by linarith
  have hA : 0 < D*H^(ν/3) := by positivity
  have hpacket : ∀ U : Finset ℝ, U ⊆ W →
      ∀ A : ℝ, (∀ t ∈ U, A ≤ t ∧ t ≤ A+atkinsonAbsorptionLength (D*H^(ν/3)) G Y) →
      (∑ t ∈ U, atkinsonLocalMeanExcess G t (C*G*Real.log t))^2 ≤
        (D*H^(ν/3))*((U.card:ℝ)*H/G+(U.card:ℝ)^2*
          Real.sqrt (G*atkinsonAbsorptionLength (D*H^(ν/3)) G Y)) := by
    intro U hsub A hlocal
    have hsepU : IsSeparated G U := by
      intro x hx y hy hxy
      exact hSep x (hsub hx) y (hsub hy) hxy
    exact hsource H G A (atkinsonAbsorptionLength (D*H^(ν/3)) G Y)
      U hH hG hsepU (fun t ht => hrange t (hsub ht)) hlocal
  have hc := atkinson_card_le_of_local_packets hA hH0.le hG hY
    (fun t ht => ⟨(hrange t ht).1,(hrange t ht).2.1⟩) hlarge hpacket
  exact hc.trans (atkinson_count_exponent_budget hD.le hH1 hG hY hν.le)

theorem exists_atkinsonLocalMean_superlevel_card_le
    {δ ε ν : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (hν : 0 < ν) :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℝ, 0 < D ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧
      ∀ H G Y : ℝ, ∀ W : Finset ℝ, H₀ ≤ H → 0 < G → 0 < Y → IsSeparated G W →
      (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H ∧ t^δ ≤ G ∧ G ≤ t^(1/2-δ) ∧ t^(1/4 : ℝ) ≤ G) →
      (({t ∈ W | C*(G*Real.log t+t^(1/4+ε))+Y ≤
        ∫ u in t-G..t+G, zetaMomentCriticalNorm u^2}).card:ℝ) ≤
        D*H^ν*(H/(G*Y^2)+H^2/Y^6) := by
  obtain ⟨C,hC,D,hD,B,hB,hcount⟩ := exists_atkinsonLocalMeanExcess_card_le
    hδ hε hν
  refine ⟨C,hC,D,hD,B,hB,?_⟩
  intro H G Y W hH hG hY hSep hrange
  let U := {t ∈ W | C*(G*Real.log t+t^(1/4+ε))+Y ≤
    ∫ u in t-G..t+G, zetaMomentCriticalNorm u^2}
  have hsub : U ⊆ W := Finset.filter_subset _ W
  have hsepU : IsSeparated G U := by
    intro x hx y hy hxy
    exact hSep x (hsub hx) y (hsub hy) hxy
  have hlarge : ∀ t ∈ U, Y ≤ atkinsonLocalMeanExcess G t (C*(G*Real.log t+t^(1/4+ε))) := by
    intro t ht
    exact (atkinsonLocalMeanExcess_threshold_iff hY).mpr (Finset.mem_filter.mp ht).2
  exact hcount H G Y U hH hG hY hsepU (fun t ht => hrange t (hsub ht)) hlarge

theorem exists_atkinsonLocalMean_superlevel_card_le_above_fourthRoot
    {δ κ ν : ℝ} (hδ : 0 < δ) (hκ : 0 < κ) (hν : 0 < ν) :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℝ, 0 < D ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧
      ∀ H G Y : ℝ, ∀ W : Finset ℝ, H₀ ≤ H → 0 < G → 0 < Y → IsSeparated G W →
      (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H ∧ t^δ ≤ G ∧ G ≤ t^(1/2-δ) ∧ t^(1/4+κ) ≤ G) →
      (({t ∈ W | C*G*Real.log t+Y ≤
        ∫ u in t-G..t+G, zetaMomentCriticalNorm u^2}).card:ℝ) ≤
        D*H^ν*(H/(G*Y^2)+H^2/Y^6) := by
  obtain ⟨C,hC,D,hD,B,hB,hcount⟩ := exists_atkinsonLocalMeanExcess_card_le_above_fourthRoot
    hδ hκ hν
  refine ⟨C,hC,D,hD,B,hB,?_⟩
  intro H G Y W hH hG hY hSep hrange
  let U := {t ∈ W | C*G*Real.log t+Y ≤
    ∫ u in t-G..t+G, zetaMomentCriticalNorm u^2}
  have hsub : U ⊆ W := Finset.filter_subset _ W
  have hsepU : IsSeparated G U := by
    intro x hx y hy hxy
    exact hSep x (hsub hx) y (hsub hy) hxy
  have hlarge : ∀ t ∈ U, Y ≤ atkinsonLocalMeanExcess G t (C*G*Real.log t) := by
    intro t ht
    exact (atkinsonLocalMeanExcess_threshold_iff hY).mpr (Finset.mem_filter.mp ht).2
  exact hcount H G Y U hH hG hY hsepU (fun t ht => hrange t (hsub ht)) hlarge

end TaoTrudgianYang2025
