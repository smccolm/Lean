import TaoTrudgianYang2025.AtkinsonPhysicalBudget
import TaoTrudgianYang2025.AtkinsonPowerGapPackets

/-!
# Actual source packets on optimized physical scales

All cutoff and logarithmic losses are eliminated in favor of an arbitrary
positive power of H. The two physical cardinality terms are retained.
Local-mean source errors and fourth-root restrictions are unchanged.
-/

noncomputable section

open RiemannZeta.GuthMaynard

namespace TaoTrudgianYang2025

theorem atkinson_packet_width_scales {δ H G : ℝ} {W : Finset ℝ}
    (hδ : 0 < δ) (hH : 1 ≤ H) (hG : 0 < G) (hW : W.Nonempty)
    (hrange : ∀ t ∈ W, H ≤ t ∧ t ≤ 2*H ∧ t^δ ≤ G ∧ G ≤ t^(1/2-δ)) :
    H^δ ≤ G ∧ G ≤ Real.sqrt (2*H) := by
  obtain ⟨t,ht⟩ := hW
  obtain ⟨hHt,htH,hlower,hupper⟩ := hrange t ht
  have hH0 : 0 < H := by linarith
  have hs := gaussian_width_sq_le_height (hH.trans hHt) hG.le hδ.le hupper
  exact ⟨(Real.rpow_le_rpow hH0.le hHt hδ.le).trans hlower,
    (Real.le_sqrt hG.le (by positivity)).mpr (hs.trans htH)⟩

theorem exists_atkinsonStationaryPacket_sq_le_localizedPhysical
    {δ ν : ℝ} (hδ : 0 < δ) (hν : 0 < ν) :
    ∃ D : ℝ, 0 < D ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧
      ∀ H G A L : ℝ, ∀ W : Finset ℝ, H₀ ≤ H → 0 < G → IsSeparated G W →
      (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H ∧ t^δ ≤ G ∧ G ≤ t^(1/2-δ)) →
      (∀ t ∈ W, A ≤ t ∧ t ≤ A+L) →
      (∑ t ∈ W, ‖atkinsonStationaryLeadingSum t G (Real.log t)‖)^2 ≤
        D*H^ν*((W.card:ℝ)*H/G+(W.card:ℝ)^2*Real.sqrt (G*L)) := by
  obtain ⟨D,hD,B,hB,hsource⟩ :=
    exists_atkinsonStationaryPacket_sq_le_localizedPowers
      hδ (show 0 < ν/2 by linarith)
  obtain ⟨E,hE,F,hF,hbudget⟩ := exists_atkinsonPhysicalGapBudget_le_twoTerm hδ hν
  refine ⟨D*E,mul_pos hD hE,max B F,hB.trans (le_max_left _ _),?_⟩
  intro H G A L W hH hG hSep hrange hlocal
  by_cases hW : W.Nonempty
  · have hBH : B ≤ H := (le_max_left _ _).trans hH
    have hFH : F ≤ H := (le_max_right _ _).trans hH
    have hw := atkinson_packet_width_scales hδ (by linarith [hB.trans hBH] : 1 ≤ H) hG hW
      hrange
    have hs := hsource H G A L W hBH hG hSep hrange hlocal
    have hp := mul_le_mul_of_nonneg_left (hbudget H G L W.card hFH hw.1 hw.2) hD.le
    exact hs.trans (by convert hp using 1 <;> ring)
  · have he : W = ∅ := Finset.not_nonempty_iff_eq_empty.mp hW
    subst W
    simp

theorem exists_atkinsonLocalMeanExcessPacket_sq_le_localizedPhysical
    {δ ε ν : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (hν : 0 < ν) :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℝ, 0 < D ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧
      ∀ H G A L : ℝ, ∀ W : Finset ℝ, H₀ ≤ H → 0 < G → IsSeparated G W →
      (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H ∧ t^δ ≤ G ∧ G ≤ t^(1/2-δ) ∧ t^(1/4 : ℝ) ≤ G) →
      (∀ t ∈ W, A ≤ t ∧ t ≤ A+L) →
      (∑ t ∈ W, atkinsonLocalMeanExcess G t (C*(G*Real.log t+t^(1/4+ε))))^2 ≤
        D*H^ν*((W.card:ℝ)*H/G+(W.card:ℝ)^2*Real.sqrt (G*L)) := by
  obtain ⟨C,hC,D,hD,B,hB,hsource⟩ :=
    exists_atkinsonLocalMeanExcessPacket_sq_le_localizedPowers
      hδ hε (show 0 < ν/2 by linarith)
  obtain ⟨E,hE,F,hF,hbudget⟩ := exists_atkinsonPhysicalGapBudget_le_twoTerm hδ hν
  refine ⟨C,hC,D*E,mul_pos hD hE,max B F,hB.trans (le_max_left _ _),?_⟩
  intro H G A L W hH hG hSep hrange hlocal
  by_cases hW : W.Nonempty
  · have hBH : B ≤ H := (le_max_left _ _).trans hH
    have hFH : F ≤ H := (le_max_right _ _).trans hH
    have hw := atkinson_packet_width_scales hδ (by linarith [hB.trans hBH] : 1 ≤ H) hG hW
      (fun t ht => ⟨(hrange t ht).1,(hrange t ht).2.1,
        (hrange t ht).2.2.1,(hrange t ht).2.2.2.1⟩)
    have hs := hsource H G A L W hBH hG hSep hrange hlocal
    have hp := mul_le_mul_of_nonneg_left (hbudget H G L W.card hFH hw.1 hw.2) hD.le
    exact hs.trans (by convert hp using 1 <;> ring)
  · have he : W = ∅ := Finset.not_nonempty_iff_eq_empty.mp hW
    subst W
    simp

theorem exists_atkinsonLocalMeanExcessPacket_sq_le_localizedPhysical_above_fourthRoot
    {δ κ ν : ℝ} (hδ : 0 < δ) (hκ : 0 < κ) (hν : 0 < ν) :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℝ, 0 < D ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧
      ∀ H G A L : ℝ, ∀ W : Finset ℝ, H₀ ≤ H → 0 < G → IsSeparated G W →
      (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H ∧ t^δ ≤ G ∧ G ≤ t^(1/2-δ) ∧ t^(1/4+κ) ≤ G) →
      (∀ t ∈ W, A ≤ t ∧ t ≤ A+L) →
      (∑ t ∈ W, atkinsonLocalMeanExcess G t (C*G*Real.log t))^2 ≤
        D*H^ν*((W.card:ℝ)*H/G+(W.card:ℝ)^2*Real.sqrt (G*L)) := by
  obtain ⟨C,hC,D,hD,B,hB,hsource⟩ :=
    exists_atkinsonLocalMeanExcessPacket_sq_le_localizedPowers_above_fourthRoot
      hδ hκ (show 0 < ν/2 by linarith)
  obtain ⟨E,hE,F,hF,hbudget⟩ := exists_atkinsonPhysicalGapBudget_le_twoTerm hδ hν
  refine ⟨C,hC,D*E,mul_pos hD hE,max B F,hB.trans (le_max_left _ _),?_⟩
  intro H G A L W hH hG hSep hrange hlocal
  by_cases hW : W.Nonempty
  · have hBH : B ≤ H := (le_max_left _ _).trans hH
    have hFH : F ≤ H := (le_max_right _ _).trans hH
    have hw := atkinson_packet_width_scales hδ (by linarith [hB.trans hBH] : 1 ≤ H) hG hW
      (fun t ht => ⟨(hrange t ht).1,(hrange t ht).2.1,
        (hrange t ht).2.2.1,(hrange t ht).2.2.2.1⟩)
    have hs := hsource H G A L W hBH hG hSep hrange hlocal
    have hp := mul_le_mul_of_nonneg_left (hbudget H G L W.card hFH hw.1 hw.2) hD.le
    exact hs.trans (by convert hp using 1 <;> ring)
  · have he : W = ∅ := Finset.not_nonempty_iff_eq_empty.mp hW
    subst W
    simp

theorem exists_atkinsonStationaryPacket_sq_le_globalPhysical
    {δ ν : ℝ} (hδ : 0 < δ) (hν : 0 < ν) :
    ∃ D : ℝ, 0 < D ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧
      ∀ H G : ℝ, ∀ W : Finset ℝ, H₀ ≤ H → 0 < G → IsSeparated G W →
      (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H ∧ t^δ ≤ G ∧ G ≤ t^(1/2-δ)) →
      (∑ t ∈ W, ‖atkinsonStationaryLeadingSum t G (Real.log t)‖)^2 ≤
        D*H^ν*((W.card:ℝ)*H/G+(W.card:ℝ)^2*Real.sqrt (G*H)) := by
  obtain ⟨D,hD,B,hB,hsource⟩ :=
    exists_atkinsonStationaryPacket_sq_le_localizedPhysical hδ hν
  refine ⟨D,hD,B,hB,?_⟩
  intro H G W hH hG hSep hrange
  exact hsource H G H H W hH hG hSep hrange (fun t ht =>
    ⟨(hrange t ht).1,by linarith [(hrange t ht).2.1]⟩)

theorem exists_atkinsonLocalMeanExcessPacket_sq_le_globalPhysical
    {δ ε ν : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (hν : 0 < ν) :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℝ, 0 < D ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧
      ∀ H G : ℝ, ∀ W : Finset ℝ, H₀ ≤ H → 0 < G → IsSeparated G W →
      (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H ∧ t^δ ≤ G ∧ G ≤ t^(1/2-δ) ∧ t^(1/4 : ℝ) ≤ G) →
      (∑ t ∈ W, atkinsonLocalMeanExcess G t (C*(G*Real.log t+t^(1/4+ε))))^2 ≤
        D*H^ν*((W.card:ℝ)*H/G+(W.card:ℝ)^2*Real.sqrt (G*H)) := by
  obtain ⟨C,hC,D,hD,B,hB,hsource⟩ :=
    exists_atkinsonLocalMeanExcessPacket_sq_le_localizedPhysical hδ hε hν
  refine ⟨C,hC,D,hD,B,hB,?_⟩
  intro H G W hH hG hSep hrange
  exact hsource H G H H W hH hG hSep hrange (fun t ht =>
    ⟨(hrange t ht).1,by linarith [(hrange t ht).2.1]⟩)

theorem exists_atkinsonLocalMeanExcessPacket_sq_le_globalPhysical_above_fourthRoot
    {δ κ ν : ℝ} (hδ : 0 < δ) (hκ : 0 < κ) (hν : 0 < ν) :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℝ, 0 < D ∧ ∃ H₀ : ℝ, 40000 ≤ H₀ ∧
      ∀ H G : ℝ, ∀ W : Finset ℝ, H₀ ≤ H → 0 < G → IsSeparated G W →
      (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H ∧ t^δ ≤ G ∧ G ≤ t^(1/2-δ) ∧ t^(1/4+κ) ≤ G) →
      (∑ t ∈ W, atkinsonLocalMeanExcess G t (C*G*Real.log t))^2 ≤
        D*H^ν*((W.card:ℝ)*H/G+(W.card:ℝ)^2*Real.sqrt (G*H)) := by
  obtain ⟨C,hC,D,hD,B,hB,hsource⟩ :=
    exists_atkinsonLocalMeanExcessPacket_sq_le_localizedPhysical_above_fourthRoot hδ hκ hν
  refine ⟨C,hC,D,hD,B,hB,?_⟩
  intro H G W hH hG hSep hrange
  exact hsource H G H H W hH hG hSep hrange (fun t ht =>
    ⟨(hrange t ht).1,by linarith [(hrange t ht).2.1]⟩)

end TaoTrudgianYang2025
