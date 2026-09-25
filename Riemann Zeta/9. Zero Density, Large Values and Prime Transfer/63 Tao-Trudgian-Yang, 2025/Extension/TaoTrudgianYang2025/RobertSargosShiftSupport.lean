import TaoTrudgianYang2025.RobertSargosCorrelationBoundary

/-! A genuinely common interval for every translated source correlation. -/

noncomputable section
open scoped BigOperators
namespace TaoTrudgianYang2025

def robertSargosShiftedMInterval (M : ℕ) (h q n : ℤ) : Finset ℤ :=
  Finset.Icc (max (h+1) (h+1-q)-n) (min ((M:ℤ)-h) ((M:ℤ)-h-q)-n)

def robertSargosCommonMInterval (M H Q N : ℕ) : Finset ℤ :=
  Finset.Icc (2*(H:ℤ)+Q) ((M:ℤ)-2*H-Q-N)

theorem robertSargos_common_interval_subset (M H Q N : ℕ) (h q n : ℤ)
    (hh : h ∈ Finset.Ico (H:ℤ) (2*H))
    (hq : q ∈ Finset.Ioo (-(Q:ℤ)) Q)
    (hn : n ∈ Finset.Icc (1:ℤ) N) :
    robertSargosCommonMInterval M H Q N ⊆ robertSargosShiftedMInterval M h q n := by
  intro m hm
  simp only [Finset.mem_Ico] at hh
  simp only [Finset.mem_Ioo] at hq
  simp only [Finset.mem_Icc] at hn
  simp only [robertSargosCommonMInterval,Finset.mem_Icc] at hm
  simp only [robertSargosShiftedMInterval,Finset.mem_Icc]
  omega

theorem robertSargos_shifted_interval_outer (M H Q N : ℕ) (h q n : ℤ)
    (hh : h ∈ Finset.Ico (H:ℤ) (2*H))
    (hq : q ∈ Finset.Ioo (-(Q:ℤ)) Q)
    (hn : n ∈ Finset.Icc (1:ℤ) N) :
    robertSargosShiftedMInterval M h q n ⊆ Finset.Icc (-(Q:ℤ)-N) ((M:ℤ)+Q) := by
  intro m hm
  simp only [Finset.mem_Ico] at hh
  simp only [Finset.mem_Ioo] at hq
  simp only [Finset.mem_Icc] at hn ⊢
  simp only [robertSargosShiftedMInterval,Finset.mem_Icc] at hm
  omega

theorem robertSargos_shifted_boundary_card (M H Q N : ℕ) (h q n : ℤ)
    (hh : h ∈ Finset.Ico (H:ℤ) (2*H))
    (hq : q ∈ Finset.Ioo (-(Q:ℤ)) Q)
    (hn : n ∈ Finset.Icc (1:ℤ) N) :
    ((robertSargosShiftedMInterval M h q n \ robertSargosCommonMInterval M H Q N).card:ℝ)
      ≤ 4*(H:ℝ)+4*Q+2*N := by
  have hs : robertSargosShiftedMInterval M h q n \ robertSargosCommonMInterval M H Q N ⊆
      Finset.Icc (-(Q:ℤ)-N) (2*(H:ℤ)+Q-1) ∪
        Finset.Icc ((M:ℤ)-2*H-Q-N+1) ((M:ℤ)+Q) := by
    intro m hm
    have ht := Finset.mem_sdiff.mp hm
    have ho := robertSargos_shifted_interval_outer M H Q N h q n hh hq hn ht.1
    simp only [robertSargosCommonMInterval,Finset.mem_Icc] at ht
    simp only [Finset.mem_Icc] at ho
    simp only [Finset.mem_union,Finset.mem_Icc]
    omega
  have hc := (Finset.card_le_card hs).trans (Finset.card_union_le _ _)
  have hl : (Finset.Icc (-(Q:ℤ)-N) (2*(H:ℤ)+Q-1)).card = 2*H+2*Q+N := by
    rw [Int.card_Icc]
    omega
  have hr : (Finset.Icc ((M:ℤ)-2*H-Q-N+1) ((M:ℤ)+Q)).card = 2*H+2*Q+N := by
    rw [Int.card_Icc]
    omega
  rw [hl,hr] at hc
  have hc' : ((robertSargosShiftedMInterval M h q n \
      robertSargosCommonMInterval M H Q N).card:ℝ) ≤
      (2*(H:ℝ)+2*Q+N)+(2*(H:ℝ)+2*Q+N) := by exact_mod_cast hc
  linarith

end TaoTrudgianYang2025
