import GafniTao.FordEquation54Resonance

/-!
# Ford Lemma 5.1: equations (5.4) and (5.5)

This file groups the exact resonant tuple pairs by their signed power-
difference vector.  The resulting finite sum is Ford's literal shifted
representation sum in (5.4), and its membership condition is exactly the
system (5.5).
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- The source power-sum vector attached to one `s`-tuple from `B`. -/
def fordLemma51SourcePowerVector
    (k s : ℕ) (B : Finset ℕ) (x : FordLemma51BTuple s B) : Fin k → ℤ :=
  fun j => ∑ i : Fin s, ((x i : ℕ) : ℤ) ^ ((j : ℕ) + 1)

theorem fordLemma51DifferenceVector_eq_sourcePower_sub
    (k s : ℕ) (B : Finset ℕ) (x y : FordLemma51BTuple s B) :
    fordLemma51DifferenceVector k s B x y =
      fordLemma51SourcePowerVector k s B x -
        fordLemma51SourcePowerVector k s B y := by
  rfl

/-- The finite Cartesian product of Ford's literal resonant sets `D_j`. -/
def fordLemma51ResonantDisplacementBox
    {k : ℕ} (s M₂ r M : ℕ) (t z : ℝ) : Finset (Fin k → ℤ) :=
  Fintype.piFinset fun j => fordLemma51ResonantSet s M₂ r M t z j

theorem mem_fordLemma51ResonantDisplacementBox
    {k s M₂ r M : ℕ} {t z : ℝ} {d : Fin k → ℤ} :
    d ∈ fordLemma51ResonantDisplacementBox s M₂ r M t z ↔
      ∀ j : Fin k, d j ∈ fordLemma51ResonantSet s M₂ r M t z j := by
  simp [fordLemma51ResonantDisplacementBox]

theorem card_fordLemma51ResonantDisplacementBox
    {k s M₂ r M : ℕ} (t z : ℝ) :
    (fordLemma51ResonantDisplacementBox (k := k) s M₂ r M t z).card =
      ∏ j : Fin k, (fordLemma51ResonantSet s M₂ r M t z j).card := by
  simp [fordLemma51ResonantDisplacementBox]

/-- Ford's shifted count `J_{s,k,1}(B;d)` in exact ordered-pair form. -/
def fordLemma51ShiftedCount
    (k s : ℕ) (B : Finset ℕ) (d : Fin k → ℤ) : ℕ :=
  fordRepresentationCount
    (Finset.univ : Finset (FordLemma51BTuple s B))
    (fordLemma51SourcePowerVector k s B) d

/-- Equation (5.5): the resonant-pair cardinality is exactly the sum of
shifted representation counts over `d_j ∈ D_j` for every degree. -/
theorem ford_equation_5_5
    {k s M₂ r M : ℕ} (B : Finset ℕ) (t z : ℝ) :
    (fordLemma51ResonantTuplePairs (k := k) s M₂ r M B t z).card =
      ∑ d ∈ fordLemma51ResonantDisplacementBox (k := k) s M₂ r M t z,
        fordLemma51ShiftedCount k s B d := by
  classical
  let U : Finset (FordLemma51BTuple s B) := Finset.univ
  let F : FordLemma51BTuple s B → (Fin k → ℤ) :=
    fordLemma51SourcePowerVector k s B
  let D : Finset (Fin k → ℤ) :=
    fordLemma51ResonantDisplacementBox (k := k) s M₂ r M t z
  let S : Finset (FordLemma51BTuple s B × FordLemma51BTuple s B) :=
    (U ×ˢ U).filter fun p => F p.1 - F p.2 ∈ D
  have hS : S = fordLemma51ResonantTuplePairs (k := k) s M₂ r M B t z := by
    ext p
    simp only [S, U, F, D, mem_filter, mem_product, mem_univ, true_and]
    rw [mem_fordLemma51ResonantDisplacementBox]
    simp only [fordLemma51ResonantTuplePairs, mem_filter, mem_univ, true_and]
    rw [← fordLemma51DifferenceVector_eq_sourcePower_sub]
  calc
    (fordLemma51ResonantTuplePairs (k := k) s M₂ r M B t z).card = S.card := by
      rw [hS]
    _ = ∑ d ∈ D, (S.filter fun p => F p.1 - F p.2 = d).card := by
      apply Finset.card_eq_sum_card_fiberwise
      intro p hp
      exact (mem_filter.mp hp).2
    _ = ∑ d ∈ D, fordLemma51ShiftedCount k s B d := by
      apply Finset.sum_congr rfl
      intro d hd
      unfold fordLemma51ShiftedCount fordRepresentationCount
      congr 1
      ext p
      simp only [S, U, F, mem_filter, mem_product, mem_univ, true_and]
      constructor
      · exact fun hp => hp.2
      · intro hp
        exact ⟨hp ▸ hd, hp⟩
    _ = ∑ d ∈ fordLemma51ResonantDisplacementBox (k := k) s M₂ r M t z,
          fordLemma51ShiftedCount k s B d := rfl

/-- Ford's equation (5.4), now with the exact shifted representation sum
rather than an abstract support cardinality. -/
theorem ford_equation_5_4
    {k s M₂ r M : ℕ} (hs : 2 ≤ s) (hM₂ : 1 ≤ M₂)
    (hr : 0 < r) (hM : 0 < M) {B : Finset ℕ}
    (hBpos : ∀ b ∈ B, 0 < b) (hBtop : ∀ b ∈ B, b ≤ M₂)
    (t z : ℝ) :
    (fordLemma51MomentT k M r s B t z : ℝ) ≤
      (5 * (r : ℝ)) ^ k * (M : ℝ) ^ fordVinogradovKappa k *
        (∑ d ∈ fordLemma51ResonantDisplacementBox (k := k) s M₂ r M t z,
          fordLemma51ShiftedCount k s B d) := by
  calc
    (fordLemma51MomentT k M r s B t z : ℝ) ≤
        (5 * (r : ℝ)) ^ k * (M : ℝ) ^ fordVinogradovKappa k *
          (∑ x : FordLemma51BTuple s B, ∑ y : FordLemma51BTuple s B,
            fordLemma51TuplePairTentProduct k M r s B t z x y) :=
      fordLemma51MomentT_le_fiveScalar_tupleTentSum hr hM B t z
    _ ≤ (5 * (r : ℝ)) ^ k * (M : ℝ) ^ fordVinogradovKappa k *
          (fordLemma51ResonantTuplePairs (k := k) s M₂ r M B t z).card := by
      gcongr
      exact fordLemma51TuplePairTentSum_le_card_resonantPairs
        hs hM₂ hr hM hBpos hBtop t z
    _ = (5 * (r : ℝ)) ^ k * (M : ℝ) ^ fordVinogradovKappa k *
          (∑ d ∈ fordLemma51ResonantDisplacementBox (k := k) s M₂ r M t z,
            fordLemma51ShiftedCount k s B d) := by
      rw [ford_equation_5_5]

#print axioms fordLemma51DifferenceVector_eq_sourcePower_sub
#print axioms mem_fordLemma51ResonantDisplacementBox
#print axioms card_fordLemma51ResonantDisplacementBox
#print axioms ford_equation_5_5
#print axioms ford_equation_5_4

end

end GafniTao
