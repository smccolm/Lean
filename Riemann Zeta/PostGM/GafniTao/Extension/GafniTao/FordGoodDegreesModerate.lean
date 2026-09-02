import GafniTao.FordGoodDegrees

/-!
# Good degrees below Ford's asymptotic threshold

The interval `41k/50 <= d <= 87k/100` already contains a degree once
`k >= 40`.  For `k >= 50` it contains a linearly large subfamily.  These
finite statements let the literal Lemma 5.1 machinery be used in Ford's
bounded and moderate degree ranges; the earlier `k >= 1000` estimate remains
the sharper large-degree version.
-/

namespace GafniTao

noncomputable section

private def fordModerateGoodDegree {k : ℕ} (hk : 40 ≤ k) : Fin k :=
  ⟨(41 * k + 49) / 50, by omega⟩

theorem fordGoodDegreeSet_nonempty
    {k : ℕ} (hk : 40 ≤ k) :
    (fordGoodDegreeSet k).Nonempty := by
  refine ⟨fordModerateGoodDegree hk, ?_⟩
  simp only [fordGoodDegreeSet, Finset.mem_filter, Finset.mem_univ, true_and,
    fordGoodDegree, fordModerateGoodDegree]
  constructor
  · omega
  · have hdiv := Nat.div_mul_le_self (41 * k + 49) 50
    omega

theorem one_le_fordGoodDegreeSet_card
    {k : ℕ} (hk : 40 ≤ k) :
    1 ≤ (fordGoodDegreeSet k).card :=
  Finset.card_pos.mpr (fordGoodDegreeSet_nonempty hk)

private def fordModerateGoodDegreeEmbedding {k : ℕ} (hk : 50 ≤ k) :
    Fin (k / 50) ↪ {j : Fin k // j ∈ fordGoodDegreeSet k} where
  toFun i := by
    let d := (41 * k + 49) / 50 + (i : ℕ)
    have hdlt : d < k := by
      dsimp [d]
      have hi := i.isLt
      omega
    refine ⟨⟨d, hdlt⟩, ?_⟩
    simp only [fordGoodDegreeSet, Finset.mem_filter, Finset.mem_univ, true_and,
      fordGoodDegree]
    constructor
    · dsimp [d]
      omega
    · dsimp [d]
      have hdiv := Nat.div_mul_le_self (41 * k + 49) 50
      have hi := i.isLt
      omega
  inj' := by
    intro i₁ i₂ h
    apply Fin.ext
    have hv := congrArg
      (fun z => ((z : {j : Fin k // j ∈ fordGoodDegreeSet k}).1 : ℕ)) h
    dsimp at hv
    omega

theorem fordGoodDegreeSet_card_lower_moderate
    {k : ℕ} (hk : 50 ≤ k) :
    k / 50 ≤ (fordGoodDegreeSet k).card := by
  have hcard := Fintype.card_le_of_injective
    (fordModerateGoodDegreeEmbedding hk)
    (fordModerateGoodDegreeEmbedding hk).injective
  simpa only [Fintype.card_fin, Fintype.card_coe] using hcard

theorem fordGoodDegreeSet_card_real_lower_moderate
    {k : ℕ} (hk : 50 ≤ k) :
    (k : ℝ) / 100 ≤ ((fordGoodDegreeSet k).card : ℝ) := by
  have hq : 1 ≤ k / 50 := Nat.one_le_iff_ne_zero.mpr (by omega)
  have hmod : k % 50 < 50 := Nat.mod_lt _ (by norm_num)
  have hdecomp : 50 * (k / 50) + k % 50 = k := Nat.div_add_mod k 50
  have hkq : k ≤ 100 * (k / 50) := by omega
  have hreal : (k : ℝ) / 100 ≤ (k / 50 : ℕ) := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 100)]
    exact_mod_cast (by simpa [Nat.mul_comm] using hkq)
  exact hreal.trans (by
    exact_mod_cast fordGoodDegreeSet_card_lower_moderate hk)

#print axioms fordGoodDegreeSet_nonempty
#print axioms fordGoodDegreeSet_card_lower_moderate
#print axioms fordGoodDegreeSet_card_real_lower_moderate

end

end GafniTao
