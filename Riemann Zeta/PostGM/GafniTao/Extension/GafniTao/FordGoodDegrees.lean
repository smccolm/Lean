import GafniTao.FordCoefficientGrowth

/-!
# A central band of degrees in Ford's Lemma 5.1

For `lambda` between `0.69 k` and `0.70 k`, every degree in the band
`0.82 k ≤ d ≤ 0.87 k` makes all three nontrivial terms of Ford's displayed
`W_d` small.  This file records the finite band and a conservative cardinality
lower bound, independently of the later analytic estimates.
-/

namespace GafniTao

noncomputable section

def fordGoodDegree (k : ℕ) (j : Fin k) : Prop :=
  41 * k ≤ 50 * ((j : ℕ) + 1) ∧
    100 * ((j : ℕ) + 1) ≤ 87 * k

instance fordGoodDegreeDecidable (k : ℕ) :
    DecidablePred (fordGoodDegree k) := by
  intro j
  unfold fordGoodDegree
  infer_instance

def fordGoodDegreeSet (k : ℕ) : Finset (Fin k) :=
  Finset.univ.filter (fordGoodDegree k)

private def fordGoodDegreeEmbedding {k : ℕ} (hk : 1000 ≤ k) :
    Fin (k / 21) ↪ {j : Fin k // j ∈ fordGoodDegreeSet k} where
  toFun i := by
    let d := (41 * k + 49) / 50 + (i : ℕ)
    have hdlt : d < k := by
      dsimp [d]
      have hi := i.isLt
      omega
    refine ⟨⟨d, hdlt⟩, ?_⟩
    simp only [fordGoodDegreeSet, Finset.mem_filter, Finset.mem_univ, true_and,
      fordGoodDegree]
    constructor <;> (dsimp [d]; omega)
  inj' := by
    intro i₁ i₂ h
    apply Fin.ext
    have hv := congrArg
      (fun z => ((z : {j : Fin k // j ∈ fordGoodDegreeSet k}).1 : ℕ)) h
    dsimp at hv
    omega

theorem fordGoodDegreeSet_card_lower
    {k : ℕ} (hk : 1000 ≤ k) :
    k / 21 ≤ (fordGoodDegreeSet k).card := by
  have hcard := Fintype.card_le_of_injective
    (fordGoodDegreeEmbedding hk) (fordGoodDegreeEmbedding hk).injective
  simpa only [Fintype.card_fin, Fintype.card_coe] using hcard

theorem fordGoodDegree_mem_bounds
    {k : ℕ} {j : Fin k} (hj : j ∈ fordGoodDegreeSet k) :
    41 * k ≤ 50 * ((j : ℕ) + 1) ∧
      100 * ((j : ℕ) + 1) ≤ 87 * k := by
  simpa [fordGoodDegreeSet] using hj

#print axioms fordGoodDegreeSet_card_lower
#print axioms fordGoodDegree_mem_bounds

end

end GafniTao
