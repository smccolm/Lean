import GafniTao.FordIntegerInterval

/-!
# Ford's spacing estimate (5.6)

The counted set is the literal integer set
`{|d| ≤ K : ∃ m : ℤ, |dγ-m| < δ}`.  Thus the distance-to-an-integer
condition is not replaced by an abstract spacing hypothesis.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

def fordSpacingSet (K gamma delta : ℝ) : Finset ℤ :=
  by
    classical
    exact (Finset.Icc ⌈-K⌉ ⌊K⌋).filter fun d =>
      ∃ m : ℤ, |(d : ℝ) * gamma - m| < delta

theorem mem_fordSpacingSet {K gamma delta : ℝ} {d : ℤ} :
    d ∈ fordSpacingSet K gamma delta ↔
      |(d : ℝ)| ≤ K ∧ ∃ m : ℤ, |(d : ℝ) * gamma - m| < delta := by
  classical
  unfold fordSpacingSet
  constructor
  · intro hd
    obtain ⟨hdIcc, hm⟩ := Finset.mem_filter.mp hd
    have hlo : -K ≤ (d : ℝ) :=
      (Int.le_ceil (-K)).trans (by exact_mod_cast (Finset.mem_Icc.mp hdIcc).1)
    have hhi : (d : ℝ) ≤ K :=
      (by exact_mod_cast (Finset.mem_Icc.mp hdIcc).2 :
        (d : ℝ) ≤ (⌊K⌋ : ℤ)).trans (Int.floor_le K)
    exact ⟨(abs_le.mpr ⟨by linarith, hhi⟩), hm⟩
  · rintro ⟨hdK, hm⟩
    have hdBounds := abs_le.mp hdK
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_Icc.mpr
      ⟨Int.ceil_le.mpr hdBounds.1, Int.le_floor.mpr hdBounds.2⟩, hm⟩

/-- Ford's equation (5.6). -/
theorem ford_equation_5_6
    {K gamma delta : ℝ} (hK : 0 < K) (hgamma : 0 < gamma)
    (hdelta : 0 < delta) :
    ((fordSpacingSet K gamma delta).card : ℝ) ≤
      4 * K * delta + 2 * K * gamma + 4 * delta / gamma + 2 := by
  classical
  by_cases hhalf : (1 / 2 : ℝ) ≤ delta
  · have hsub : fordSpacingSet K gamma delta ⊆ Finset.Icc ⌈-K⌉ ⌊K⌋ := by
      intro d hd
      have hdK := (mem_fordSpacingSet.mp hd).1
      have hdBounds := abs_le.mp hdK
      exact Finset.mem_Icc.mpr
        ⟨Int.ceil_le.mpr hdBounds.1, Int.le_floor.mpr hdBounds.2⟩
    have hcardNat := Finset.card_le_card hsub
    have hcard : ((fordSpacingSet K gamma delta).card : ℝ) ≤
        ((Finset.Icc ⌈-K⌉ ⌊K⌋).card : ℝ) := by
      exact_mod_cast hcardNat
    have hIcc := card_int_Icc_ceil_floor_cast_le
      (a := -K) (b := K) (by linarith)
    have hnonneg : 0 ≤ 4 * delta / gamma := by positivity
    calc
      ((fordSpacingSet K gamma delta).card : ℝ) ≤
          ((Finset.Icc ⌈-K⌉ ⌊K⌋).card : ℝ) := hcard
      _ ≤ K - (-K) + 1 := hIcc
      _ ≤ 4 * K * delta + 2 * K * gamma + 4 * delta / gamma + 2 := by
        nlinarith
  · have hdeltaHalf : delta < 1 / 2 := lt_of_not_ge hhalf
    let Mset : Finset ℤ :=
      fordIntegerOpenInterval (-K * gamma - delta) (K * gamma + delta)
    let fiber : ℤ → Finset ℤ := fun m =>
      fordIntegerOpenInterval (((m : ℝ) - delta) / gamma)
        (((m : ℝ) + delta) / gamma)
    have hsub : fordSpacingSet K gamma delta ⊆ Mset.biUnion fiber := by
      intro d hd
      obtain ⟨hdK, m, hdm⟩ := mem_fordSpacingSet.mp hd
      have hdm' := abs_lt.mp hdm
      apply Finset.mem_biUnion.mpr
      refine ⟨m, ?_, ?_⟩
      · apply mem_fordIntegerOpenInterval.mpr
        have hdBounds := abs_le.mp hdK
        constructor <;> nlinarith
      · apply mem_fordIntegerOpenInterval.mpr
        constructor
        · apply (div_lt_iff₀ hgamma).2
          linarith
        · apply (lt_div_iff₀ hgamma).2
          linarith
    have hcardUnionNat := Finset.card_le_card hsub
    have hcardUnion : ((fordSpacingSet K gamma delta).card : ℝ) ≤
        ((Mset.biUnion fiber).card : ℝ) := by
      exact_mod_cast hcardUnionNat
    have hUnionSum : ((Mset.biUnion fiber).card : ℝ) ≤
        ∑ m ∈ Mset, ((fiber m).card : ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le (s := Mset) (t := fiber))
    have hfiber (m : ℤ) : ((fiber m).card : ℝ) ≤ 2 * delta / gamma + 1 := by
      have hab : ((m : ℝ) - delta) / gamma ≤
          ((m : ℝ) + delta) / gamma := by
        apply (div_le_div_iff_of_pos_right hgamma).2
        linarith
      have h := fordIntegerOpenInterval_card_cast_le hab
      change ((fiber m).card : ℝ) ≤ 2 * delta / gamma + 1
      have heq : ((m : ℝ) + delta) / gamma -
          ((m : ℝ) - delta) / gamma + 1 = 2 * delta / gamma + 1 := by
        field_simp [hgamma.ne']
        ring
      exact h.trans_eq heq
    have hsum : (∑ m ∈ Mset, ((fiber m).card : ℝ)) ≤
        (Mset.card : ℝ) * (2 * delta / gamma + 1) := by
      calc
        (∑ m ∈ Mset, ((fiber m).card : ℝ)) ≤
            ∑ m ∈ Mset, (2 * delta / gamma + 1) := by
          exact Finset.sum_le_sum fun m _hm => hfiber m
        _ = (Mset.card : ℝ) * (2 * delta / gamma + 1) := by
          simp [mul_add]
    have hMraw : (Mset.card : ℝ) ≤
        (K * gamma + delta) - (-K * gamma - delta) + 1 := by
      exact fordIntegerOpenInterval_card_cast_le (by
        have hKg : 0 < K * gamma := mul_pos hK hgamma
        linarith)
    have hM : (Mset.card : ℝ) ≤ 2 * K * gamma + 2 := by
      calc
        (Mset.card : ℝ) ≤
            (K * gamma + delta) - (-K * gamma - delta) + 1 := hMraw
        _ ≤ 2 * K * gamma + 2 := by linarith
    have hfactor : 0 ≤ 2 * delta / gamma + 1 := by positivity
    calc
      ((fordSpacingSet K gamma delta).card : ℝ) ≤
          ((Mset.biUnion fiber).card : ℝ) := hcardUnion
      _ ≤ ∑ m ∈ Mset, ((fiber m).card : ℝ) := hUnionSum
      _ ≤ (Mset.card : ℝ) * (2 * delta / gamma + 1) := hsum
      _ ≤ (2 * K * gamma + 2) * (2 * delta / gamma + 1) := by
        exact mul_le_mul_of_nonneg_right hM hfactor
      _ = 4 * K * delta + 2 * K * gamma + 4 * delta / gamma + 2 := by
        field_simp [hgamma.ne']
        ring

#print axioms mem_fordSpacingSet
#print axioms ford_equation_5_6

end

end GafniTao
