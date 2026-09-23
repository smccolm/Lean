import TaoTrudgianYang2025.SargosQuarticSource
import TaoTrudgianYang2025.SargosFourthCountBound
import Mathlib.Data.Fin.VecNotation

/-! Injecting the actual ordered pair-of-pairs into the literal source quadruples. -/

noncomputable section

namespace TaoTrudgianYang2025

def sargosPairPairsToQuad (p : (ℤ × ℤ) × (ℤ × ℤ)) : Fin 4 → ℤ :=
  ![p.1.1,p.1.2,p.2.1,p.2.2]

theorem sargosPairPairsToQuad_injective : Function.Injective sargosPairPairsToQuad := by
  intro p q h
  exact Prod.ext (Prod.ext (congr_fun h 0) (congr_fun h 1))
    (Prod.ext (congr_fun h 2) (congr_fun h 3))

theorem sargosQuarticNearPair_mem_source {N : ℕ} {a b : ℝ}
    (ha : a ≤ N) (hb : b ≤ (N : ℝ)^3) {p : (ℤ × ℤ) × (ℤ × ℤ)}
    (hp : p ∈ sargosNearPairs ((sargosSourceInterval N) ×ˢ (sargosSourceInterval N))
      sargosSquarePairFrequency sargosFourthPairFrequency a b) :
    sargosPairPairsToQuad p ∈ sargosFourthNearSolutions N := by
  obtain ⟨hpI,hp₂,hp₄⟩ := Finset.mem_filter.mp hp
  obtain ⟨hleft,hright⟩ := Finset.mem_product.mp hpI
  obtain ⟨hp₀,hp₁⟩ := Finset.mem_product.mp hleft
  obtain ⟨hp₂I,hp₃⟩ := Finset.mem_product.mp hright
  apply Finset.mem_filter.mpr
  refine ⟨Fintype.mem_piFinset.mpr ?_,?_,?_⟩
  · intro i
    fin_cases i
    · exact hp₀
    · exact hp₁
    · exact hp₂I
    · exact hp₃
  · have hs : |(p.1.1 : ℝ)^2+(p.1.2 : ℝ)^2-(p.2.1 : ℝ)^2-(p.2.2 : ℝ)^2| ≤ N := by
      simpa only [sargosSquarePairFrequency,sub_add_eq_sub_sub] using hp₂.trans ha
    change |p.1.1^2+p.1.2^2-p.2.1^2-p.2.2^2| ≤ (N : ℤ)
    exact_mod_cast hs
  · have hs : |(p.1.1 : ℝ)^4+(p.1.2 : ℝ)^4-(p.2.1 : ℝ)^4-(p.2.2 : ℝ)^4| ≤ (N : ℝ)^3 := by
      simpa only [sargosFourthPairFrequency,sub_add_eq_sub_sub] using hp₄.trans hb
    change |p.1.1^4+p.1.2^4-p.2.1^4-p.2.2^4| ≤ (N : ℤ)^3
    exact_mod_cast hs

theorem card_sargosQuarticNearPairs_le_source {N : ℕ} {a b : ℝ}
    (ha : a ≤ N) (hb : b ≤ (N : ℝ)^3) :
    (sargosNearPairs ((sargosSourceInterval N) ×ˢ (sargosSourceInterval N))
      sargosSquarePairFrequency sargosFourthPairFrequency a b).card ≤
        (sargosFourthNearSolutions N).card :=
  Finset.card_le_card_of_injOn sargosPairPairsToQuad
    (fun _ hp => sargosQuarticNearPair_mem_source ha hb hp) sargosPairPairsToQuad_injective.injOn

end TaoTrudgianYang2025
