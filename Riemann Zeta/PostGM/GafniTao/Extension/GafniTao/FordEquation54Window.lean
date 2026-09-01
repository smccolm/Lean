import GafniTao.FordEquation54Counting

/-!
# Ford Lemma 5.1: restriction to the degree window `[h,g]`

After (5.5), Ford discards every equation outside `h ≤ j ≤ g`.  This file
implements that operation on the actual tuple-pair set, groups by the retained
power-difference vector, and applies Proposition ZRD.  Thus no independent
cardinality certificate is substituted for the source consumer.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- Source degrees `j` satisfying `h ≤ j ≤ g`, represented using the internal
zero-based coordinate `j-1 : Fin k`. -/
abbrev FordLemma51DegreeWindow (k h g : ℕ) :=
  {j : Fin k // h ≤ (j : ℕ) + 1 ∧ (j : ℕ) + 1 ≤ g}

/-- The power-sum vector restricted to Ford's degrees `h,...,g`. -/
def fordLemma51WindowPowerVector
    (k h g s : ℕ) (B : Finset ℕ) (x : FordLemma51BTuple s B) :
    FordLemma51DegreeWindow k h g → ℤ :=
  fun j => fordLemma51SourcePowerVector k s B x j.1

/-- Ford's incomplete mean value `J_{s,g,h}(B)`. -/
def fordLemma51WindowMoment
    (k h g s : ℕ) (B : Finset ℕ) : ℕ :=
  fordRepresentationCount
    (Finset.univ : Finset (FordLemma51BTuple s B))
    (fordLemma51WindowPowerVector k h g s B) 0

/-- The shifted incomplete representation count in degrees `h,...,g`. -/
def fordLemma51WindowShiftedCount
    (k h g s : ℕ) (B : Finset ℕ)
    (d : FordLemma51DegreeWindow k h g → ℤ) : ℕ :=
  fordRepresentationCount
    (Finset.univ : Finset (FordLemma51BTuple s B))
    (fordLemma51WindowPowerVector k h g s B) d

theorem fordLemma51WindowShiftedCount_le_moment
    (k h g s : ℕ) (B : Finset ℕ)
    (d : FordLemma51DegreeWindow k h g → ℤ) :
    fordLemma51WindowShiftedCount k h g s B d ≤
      fordLemma51WindowMoment k h g s B := by
  exact ford_zeroRepresentationDominates
    (Finset.univ : Finset (FordLemma51BTuple s B))
    (fordLemma51WindowPowerVector k h g s B) d

/-- The product of resonant displacement sets retained in degrees `h,...,g`. -/
def fordLemma51WindowResonantBox
    {k : ℕ} (h g s M₂ r M : ℕ) (t z : ℝ) :
    Finset (FordLemma51DegreeWindow k h g → ℤ) :=
  Fintype.piFinset fun j => fordLemma51ResonantSet s M₂ r M t z j.1

theorem mem_fordLemma51WindowResonantBox
    {k h g s M₂ r M : ℕ} {t z : ℝ}
    {d : FordLemma51DegreeWindow k h g → ℤ} :
    d ∈ fordLemma51WindowResonantBox h g s M₂ r M t z ↔
      ∀ j : FordLemma51DegreeWindow k h g,
        d j ∈ fordLemma51ResonantSet s M₂ r M t z j.1 := by
  simp [fordLemma51WindowResonantBox]

theorem card_fordLemma51WindowResonantBox
    {k h g s M₂ r M : ℕ} (t z : ℝ) :
    (fordLemma51WindowResonantBox (k := k) h g s M₂ r M t z).card =
      ∏ j : FordLemma51DegreeWindow k h g,
        (fordLemma51ResonantSet s M₂ r M t z j.1).card := by
  simp [fordLemma51WindowResonantBox]

/-- Ordered tuple pairs satisfying the resonant conditions only in the
retained degree window. -/
def fordLemma51WindowResonantPairs
    {k : ℕ} (h g s M₂ r M : ℕ) (B : Finset ℕ) (t z : ℝ) :
    Finset (FordLemma51BTuple s B × FordLemma51BTuple s B) :=
  Finset.univ.filter fun p => ∀ j : FordLemma51DegreeWindow k h g,
    fordLemma51DifferenceVector k s B p.1 p.2 j.1 ∈
      fordLemma51ResonantSet s M₂ r M t z j.1

theorem fordLemma51ResonantPairs_card_le_windowPairs_card
    {k h g s M₂ r M : ℕ} (B : Finset ℕ) (t z : ℝ) :
    (fordLemma51ResonantTuplePairs (k := k) s M₂ r M B t z).card ≤
      (fordLemma51WindowResonantPairs (k := k) h g s M₂ r M B t z).card := by
  apply Finset.card_le_card
  intro p hp
  simp only [fordLemma51ResonantTuplePairs, fordLemma51WindowResonantPairs,
    mem_filter, mem_univ, true_and] at hp ⊢
  exact fun j => hp j.1

theorem fordLemma51WindowDifference_eq_power_sub
    (k h g s : ℕ) (B : Finset ℕ) (x y : FordLemma51BTuple s B) :
    (fun j : FordLemma51DegreeWindow k h g =>
      fordLemma51DifferenceVector k s B x y j.1) =
      fordLemma51WindowPowerVector k h g s B x -
        fordLemma51WindowPowerVector k h g s B y := by
  funext j
  rfl

/-- Exact grouping of the window-resonant pairs by their retained difference
vector. -/
theorem fordLemma51WindowResonantPairs_card_eq_sum_shifted
    {k h g s M₂ r M : ℕ} (B : Finset ℕ) (t z : ℝ) :
    (fordLemma51WindowResonantPairs (k := k) h g s M₂ r M B t z).card =
      ∑ d ∈ fordLemma51WindowResonantBox (k := k) h g s M₂ r M t z,
        fordLemma51WindowShiftedCount k h g s B d := by
  classical
  let U : Finset (FordLemma51BTuple s B) := Finset.univ
  let F : FordLemma51BTuple s B → (FordLemma51DegreeWindow k h g → ℤ) :=
    fordLemma51WindowPowerVector k h g s B
  let D : Finset (FordLemma51DegreeWindow k h g → ℤ) :=
    fordLemma51WindowResonantBox (k := k) h g s M₂ r M t z
  let S : Finset (FordLemma51BTuple s B × FordLemma51BTuple s B) :=
    (U ×ˢ U).filter fun p => F p.1 - F p.2 ∈ D
  have hS : S = fordLemma51WindowResonantPairs
      (k := k) h g s M₂ r M B t z := by
    ext p
    simp only [S, U, F, D, mem_filter, mem_product, mem_univ, true_and]
    rw [mem_fordLemma51WindowResonantBox]
    simp only [fordLemma51WindowResonantPairs, mem_filter, mem_univ, true_and]
    rw [← fordLemma51WindowDifference_eq_power_sub]
  calc
    (fordLemma51WindowResonantPairs (k := k) h g s M₂ r M B t z).card =
        S.card := by rw [hS]
    _ = ∑ d ∈ D, (S.filter fun p => F p.1 - F p.2 = d).card := by
      apply Finset.card_eq_sum_card_fiberwise
      intro p hp
      exact (mem_filter.mp hp).2
    _ = ∑ d ∈ D, fordLemma51WindowShiftedCount k h g s B d := by
      apply Finset.sum_congr rfl
      intro d hd
      unfold fordLemma51WindowShiftedCount fordRepresentationCount
      congr 1
      ext p
      simp only [S, U, F, mem_filter, mem_product, mem_univ, true_and]
      constructor
      · exact fun hp => hp.2
      · intro hp
        exact ⟨hp ▸ hd, hp⟩
    _ = ∑ d ∈ fordLemma51WindowResonantBox (k := k) h g s M₂ r M t z,
          fordLemma51WindowShiftedCount k h g s B d := rfl

/-- Ford's Proposition-ZRD count after discarding degrees outside `[h,g]`. -/
theorem fordLemma51WindowResonantPairs_card_le
    {k h g s M₂ r M : ℕ} (B : Finset ℕ) (t z : ℝ) :
    (fordLemma51WindowResonantPairs (k := k) h g s M₂ r M B t z).card ≤
      fordLemma51WindowMoment k h g s B *
        ∏ j : FordLemma51DegreeWindow k h g,
          (fordLemma51ResonantSet s M₂ r M t z j.1).card := by
  rw [fordLemma51WindowResonantPairs_card_eq_sum_shifted]
  calc
    (∑ d ∈ fordLemma51WindowResonantBox (k := k) h g s M₂ r M t z,
        fordLemma51WindowShiftedCount k h g s B d) ≤
        ∑ _d ∈ fordLemma51WindowResonantBox (k := k) h g s M₂ r M t z,
          fordLemma51WindowMoment k h g s B := by
      apply Finset.sum_le_sum
      intro d hd
      exact fordLemma51WindowShiftedCount_le_moment k h g s B d
    _ = fordLemma51WindowMoment k h g s B *
          (fordLemma51WindowResonantBox (k := k) h g s M₂ r M t z).card := by
      simp [mul_comm]
    _ = fordLemma51WindowMoment k h g s B *
          ∏ j : FordLemma51DegreeWindow k h g,
            (fordLemma51ResonantSet s M₂ r M t z j.1).card := by
      rw [card_fordLemma51WindowResonantBox]

/-- The source count used immediately after (5.5): full resonance is bounded
by `J_{s,g,h}(B)` times the product of the retained `|D_j|`. -/
theorem fordLemma51ResonantPairs_card_le_windowMoment_mul
    {k h g s M₂ r M : ℕ} (B : Finset ℕ) (t z : ℝ) :
    (fordLemma51ResonantTuplePairs (k := k) s M₂ r M B t z).card ≤
      fordLemma51WindowMoment k h g s B *
        ∏ j : FordLemma51DegreeWindow k h g,
          (fordLemma51ResonantSet s M₂ r M t z j.1).card :=
  (fordLemma51ResonantPairs_card_le_windowPairs_card B t z).trans
    (fordLemma51WindowResonantPairs_card_le B t z)

#print axioms fordLemma51WindowShiftedCount_le_moment
#print axioms fordLemma51ResonantPairs_card_le_windowPairs_card
#print axioms fordLemma51WindowDifference_eq_power_sub
#print axioms fordLemma51WindowResonantPairs_card_eq_sum_shifted
#print axioms fordLemma51WindowResonantPairs_card_le
#print axioms fordLemma51ResonantPairs_card_le_windowMoment_mul

end

end GafniTao
