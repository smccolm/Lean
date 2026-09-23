import TaoTrudgianYang2025.FiniteSignMoments
import TaoTrudgianYang2025.FiniteMomentSelection
import Mathlib.Data.List.OfFn

/-! Lower-tail counts for actual finite sign samples, indexed with multiplicity. -/

open Finset

namespace TaoTrudgianYang2025

theorem finiteSignSamples_large_count (v : List ℂ)
    (hV : 0 < (v.map Complex.normSq).sum) :
    ((finiteSignSamples v).length:ℝ) ≤
      12*({i ∈ (univ : Finset (Fin (finiteSignSamples v).length)) |
        (v.map Complex.normSq).sum/2 ≤
          Complex.normSq ((finiteSignSamples v).get i)}.card:ℝ) := by
  classical
  have hm : ∑ i : Fin (finiteSignSamples v).length,
      Complex.normSq ((finiteSignSamples v).get i) =
      (2:ℝ)^v.length*(v.map Complex.normSq).sum := by
    rw [← List.sum_ofFn]
    simpa only [List.get_eq_getElem,List.ofFn_getElem_eq_map] using
      finiteSignSamples_second_moment v
  have hq : ∑ i : Fin (finiteSignSamples v).length,
      Complex.normSq ((finiteSignSamples v).get i)^2 ≤
      3*(2:ℝ)^v.length*((v.map Complex.normSq).sum)^2 := by
    rw [← List.sum_ofFn]
    simp only [List.get_eq_getElem]
    rw [List.ofFn_getElem_eq_map (finiteSignSamples v) (fun w : ℂ => Complex.normSq w^2)]
    exact finiteSignSamples_fourth_moment v
  have hc : ((univ : Finset (Fin (finiteSignSamples v).length)).card:ℝ) =
      (2:ℝ)^v.length := by
    simp only [card_univ,Fintype.card_fin,finiteSignSamples_length,Nat.cast_pow,Nat.cast_ofNat]
  have h := finite_moment_large_value_count
    (univ : Finset (Fin (finiteSignSamples v).length))
    (fun i => Complex.normSq ((finiteSignSamples v).get i))
    (v.map Complex.normSq).sum
    (fun i _ => Complex.normSq_nonneg _) hV
    (by simpa only [hc] using hm) (by simpa only [hc] using hq)
  simpa only [card_univ,Fintype.card_fin] using h

end TaoTrudgianYang2025
