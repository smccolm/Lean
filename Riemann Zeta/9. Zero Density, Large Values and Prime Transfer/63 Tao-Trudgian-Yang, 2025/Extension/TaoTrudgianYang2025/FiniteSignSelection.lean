import TaoTrudgianYang2025.FiniteSignEvaluationMoments
import TaoTrudgianYang2025.FiniteIncidenceSelection

/-! One actual coefficient sample has large values at many evaluation points. -/

namespace TaoTrudgianYang2025

theorem finiteSignSamples_exists_many_large {E ι : Type*} [AddGroup E]
    (v : List E) (W : Finset ι) (f : ι → E →+ ℂ)
    (hV : ∀ t ∈ W, 0 < (v.map (fun a => Complex.normSq (f t a))).sum) :
    ∃ a ∈ finiteSignSamples v,
      (W.card:ℝ) ≤ 12*({t ∈ W |
        (v.map (fun b => Complex.normSq (f t b))).sum/2 ≤ Complex.normSq (f t a)}.card:ℝ) := by
  classical
  have hlen : 0 < (finiteSignSamples v).length := by
    rw [finiteSignSamples_length]
    positivity
  let s : Finset (Fin (finiteSignSamples v).length) := Finset.univ
  let R (i : Fin (finiteSignSamples v).length) (t : ι) : Prop :=
    (v.map (fun b => Complex.normSq (f t b))).sum/2 ≤
      Complex.normSq (f t ((finiteSignSamples v).get i))
  have hs : s.Nonempty := ⟨⟨0,hlen⟩,Finset.mem_univ _⟩
  have hcol (t : ι) (ht : t ∈ W) :
      (s.card:ℝ) ≤ 12*({i ∈ s | R i t}.card:ℝ) := by
    simpa only [s,Finset.card_univ,Fintype.card_fin] using
      finiteSignSamples_large_count_map (f t) v (hV t ht)
  obtain ⟨i,_hi,hgood⟩ := finite_incidence_exists_row s W R 12 hs hcol
  exact ⟨(finiteSignSamples v).get i,List.get_mem _ _,hgood⟩

end TaoTrudgianYang2025

