import TaoTrudgianYang2025.FiniteSignLargeValues

/-! Finite sign moments after an actual additive evaluation map. -/

namespace TaoTrudgianYang2025

theorem finiteSignSamples_second_moment_map {E : Type*} [AddGroup E]
    (f : E →+ ℂ) (v : List E) :
    ((finiteSignSamples v).map (fun a => Complex.normSq (f a))).sum =
      (2:ℝ)^v.length*(v.map (fun a => Complex.normSq (f a))).sum := by
  have h := finiteSignSamples_second_moment (v.map f)
  rw [← finiteSignSamples_map f v] at h
  simpa only [List.map_map,List.length_map,Function.comp_def] using h

theorem finiteSignSamples_fourth_moment_map {E : Type*} [AddGroup E]
    (f : E →+ ℂ) (v : List E) :
    ((finiteSignSamples v).map (fun a => Complex.normSq (f a)^2)).sum ≤
      3*(2:ℝ)^v.length*((v.map (fun a => Complex.normSq (f a))).sum)^2 := by
  have h := finiteSignSamples_fourth_moment (v.map f)
  rw [← finiteSignSamples_map f v] at h
  simpa only [List.map_map,List.length_map,Function.comp_def] using h

theorem finiteSignSamples_large_count_map {E : Type*} [AddGroup E]
    (f : E →+ ℂ) (v : List E)
    (hV : 0 < (v.map (fun a => Complex.normSq (f a))).sum) :
    ((finiteSignSamples v).length:ℝ) ≤
      12*({i ∈ (Finset.univ : Finset (Fin (finiteSignSamples v).length)) |
        (v.map (fun a => Complex.normSq (f a))).sum/2 ≤
          Complex.normSq (f ((finiteSignSamples v).get i))}.card:ℝ) := by
  classical
  have hm : ∑ i : Fin (finiteSignSamples v).length,
      Complex.normSq (f ((finiteSignSamples v).get i)) =
      (2:ℝ)^v.length*(v.map (fun a => Complex.normSq (f a))).sum := by
    rw [← List.sum_ofFn]
    simp only [List.get_eq_getElem]
    rw [List.ofFn_getElem_eq_map (finiteSignSamples v) (fun a => Complex.normSq (f a))]
    exact finiteSignSamples_second_moment_map f v
  have hq : ∑ i : Fin (finiteSignSamples v).length,
      Complex.normSq (f ((finiteSignSamples v).get i))^2 ≤
      3*(2:ℝ)^v.length*((v.map (fun a => Complex.normSq (f a))).sum)^2 := by
    rw [← List.sum_ofFn]
    simp only [List.get_eq_getElem]
    rw [List.ofFn_getElem_eq_map (finiteSignSamples v) (fun a => Complex.normSq (f a)^2)]
    exact finiteSignSamples_fourth_moment_map f v
  have hc : ((Finset.univ : Finset (Fin (finiteSignSamples v).length)).card:ℝ) =
      (2:ℝ)^v.length := by
    simp only [Finset.card_univ,Fintype.card_fin,finiteSignSamples_length,
      Nat.cast_pow,Nat.cast_ofNat]
  have h := finite_moment_large_value_count
    (Finset.univ : Finset (Fin (finiteSignSamples v).length))
    (fun i => Complex.normSq (f ((finiteSignSamples v).get i)))
    (v.map (fun a => Complex.normSq (f a))).sum
    (fun i _ => Complex.normSq_nonneg _) hV
    (by simpa only [hc] using hm) (by simpa only [hc] using hq)
  simpa only [Finset.card_univ,Fintype.card_fin] using h

end TaoTrudgianYang2025

