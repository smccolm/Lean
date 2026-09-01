import GafniTao.FordEquation54Window

/-!
# Ford Lemma 5.1: bounding the literal sets `D_j`

This file applies equation (5.6) to the strict resonant set from (5.4), and
also proves Ford's trivial `2 s M₂^j` bound.  Their minimum is the exact
pre-simplification form of the factor `W_j`.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

theorem fordLemma51SourceRadius_pos
    {k s M₂ : ℕ} (hs : 2 ≤ s) (hM₂ : 1 ≤ M₂) (j : Fin k) :
    0 < fordLemma51SourceRadius s M₂ j := by
  have hpow : 1 ≤ M₂ ^ ((j : ℕ) + 1) := one_le_pow₀ hM₂
  have hprod : 1 < s * M₂ ^ ((j : ℕ) + 1) := by
    nlinarith
  unfold fordLemma51SourceRadius
  exact sub_pos.mpr (by exact_mod_cast hprod)

theorem abs_fordTaylorGamma_pos
    {t z : ℝ} (ht : 0 < t) (hz : 0 < z) (j : ℕ) :
    0 < |fordTaylorGamma t z j| := by
  apply abs_pos.mpr
  unfold fordTaylorGamma
  apply div_ne_zero
  · exact mul_ne_zero (by positivity) ht.ne'
  · positivity

/-- The direct right-hand side obtained by substituting Ford's `K`, `gamma`
and `delta` into equation (5.6). -/
def fordLemma51RawSpacingBound
    {k : ℕ} (s M₂ r M : ℕ) (t z : ℝ) (j : Fin k) : ℝ :=
  let K := fordLemma51SourceRadius s M₂ j
  let gamma := |fordTaylorGamma t z (j : ℕ)|
  let delta := fordLemma51TentWidth r M j
  4 * K * delta + 2 * K * gamma + 4 * delta / gamma + 2

theorem fordLemma51ResonantSet_card_le_rawSpacingBound
    {k s M₂ r M : ℕ} (hs : 2 ≤ s) (hM₂ : 1 ≤ M₂)
    (hr : 0 < r) (hM : 0 < M) {t z : ℝ}
    (ht : 0 < t) (hz : 0 < z) (j : Fin k) :
    ((fordLemma51ResonantSet s M₂ r M t z j).card : ℝ) ≤
      fordLemma51RawSpacingBound s M₂ r M t z j := by
  have hsubset : fordLemma51ResonantSet s M₂ r M t z j ⊆
      fordSpacingSet (fordLemma51SourceRadius s M₂ j)
        |fordTaylorGamma t z (j : ℕ)| (fordLemma51TentWidth r M j) := by
    exact Finset.filter_subset _ _
  have hcardNat := Finset.card_le_card hsubset
  have hcardReal :
      ((fordLemma51ResonantSet s M₂ r M t z j).card : ℝ) ≤
        ((fordSpacingSet (fordLemma51SourceRadius s M₂ j)
          |fordTaylorGamma t z (j : ℕ)|
          (fordLemma51TentWidth r M j)).card : ℝ) := by
    exact_mod_cast hcardNat
  exact hcardReal.trans (by
    simpa [fordLemma51RawSpacingBound] using
      (ford_equation_5_6 (fordLemma51SourceRadius_pos hs hM₂ j)
        (abs_fordTaylorGamma_pos ht hz (j : ℕ))
        (fordLemma51TentWidth_pos hr hM j)))

theorem fordLemma51ResonantSet_subset_openInterval
    {k s M₂ r M : ℕ} (t z : ℝ) (j : Fin k) :
    fordLemma51ResonantSet s M₂ r M t z j ⊆
      fordIntegerOpenInterval (-fordLemma51SourceRadius s M₂ j)
        (fordLemma51SourceRadius s M₂ j) := by
  intro d hd
  rw [mem_fordIntegerOpenInterval]
  have hstrict := (mem_fordLemma51ResonantSet.mp hd).1
  exact (abs_lt.mp hstrict)

/-- The trivial source bound `|D_j| ≤ 2 s M₂^j`; the strict cutoff removes
the otherwise possible endpoint ambiguity. -/
theorem fordLemma51ResonantSet_card_le_trivial
    {k s M₂ r M : ℕ} (hs : 2 ≤ s) (hM₂ : 1 ≤ M₂)
    (t z : ℝ) (j : Fin k) :
    ((fordLemma51ResonantSet s M₂ r M t z j).card : ℝ) ≤
      2 * (s : ℝ) * (M₂ : ℝ) ^ ((j : ℕ) + 1) := by
  have hcardNat := Finset.card_le_card
    (fordLemma51ResonantSet_subset_openInterval (s := s) (M₂ := M₂)
      (r := r) (M := M) t z j)
  have hcardReal :
      ((fordLemma51ResonantSet s M₂ r M t z j).card : ℝ) ≤
        ((fordIntegerOpenInterval (-fordLemma51SourceRadius s M₂ j)
          (fordLemma51SourceRadius s M₂ j)).card : ℝ) := by
    exact_mod_cast hcardNat
  calc
    ((fordLemma51ResonantSet s M₂ r M t z j).card : ℝ) ≤
        ((fordIntegerOpenInterval (-fordLemma51SourceRadius s M₂ j)
          (fordLemma51SourceRadius s M₂ j)).card : ℝ) := hcardReal
    _ ≤ fordLemma51SourceRadius s M₂ j -
          (-fordLemma51SourceRadius s M₂ j) + 1 :=
      fordIntegerOpenInterval_card_cast_le
        (by linarith [fordLemma51SourceRadius_pos hs hM₂ j])
    _ ≤ 2 * (s : ℝ) * (M₂ : ℝ) ^ ((j : ℕ) + 1) := by
      unfold fordLemma51SourceRadius
      push_cast
      ring_nf
      norm_num

/-- Ford's factor `W_j` before expanding `|gamma_j|` and replacing `z` by
the endpoint bounds `N ≤ z ≤ 2N`. -/
def fordLemma51RawW
    {k : ℕ} (s M₂ r M : ℕ) (t z : ℝ) (j : Fin k) : ℝ :=
  min (2 * (s : ℝ) * (M₂ : ℝ) ^ ((j : ℕ) + 1))
    (fordLemma51RawSpacingBound s M₂ r M t z j)

theorem fordLemma51ResonantSet_card_le_rawW
    {k s M₂ r M : ℕ} (hs : 2 ≤ s) (hM₂ : 1 ≤ M₂)
    (hr : 0 < r) (hM : 0 < M) {t z : ℝ}
    (ht : 0 < t) (hz : 0 < z) (j : Fin k) :
    ((fordLemma51ResonantSet s M₂ r M t z j).card : ℝ) ≤
      fordLemma51RawW s M₂ r M t z j := by
  rw [fordLemma51RawW, le_min_iff]
  exact ⟨fordLemma51ResonantSet_card_le_trivial hs hM₂ t z j,
    fordLemma51ResonantSet_card_le_rawSpacingBound
      hs hM₂ hr hM ht hz j⟩

/-- The conclusion at the end of Ford's counting argument, before the
algebraic expansion of `W_j`: `T` is bounded by the incomplete moment, the
published `(5r)^k M^κ` scalar, and the product of the literal spacing
majorants over `h,...,g`. -/
theorem fordLemma51MomentT_le_windowMoment_mul_rawW
    {k h g s M₂ r M : ℕ} (hs : 2 ≤ s) (hM₂ : 1 ≤ M₂)
    (hr : 0 < r) (hM : 0 < M) {B : Finset ℕ}
    (hBpos : ∀ b ∈ B, 0 < b) (hBtop : ∀ b ∈ B, b ≤ M₂)
    {t z : ℝ} (ht : 0 < t) (hz : 0 < z) :
    (fordLemma51MomentT k M r s B t z : ℝ) ≤
      (5 * (r : ℝ)) ^ k * (M : ℝ) ^ fordVinogradovKappa k *
        (fordLemma51WindowMoment k h g s B : ℝ) *
          ∏ j : FordLemma51DegreeWindow k h g,
            fordLemma51RawW s M₂ r M t z j.1 := by
  let C : ℝ := (5 * (r : ℝ)) ^ k * (M : ℝ) ^ fordVinogradovKappa k
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hmoment : (fordLemma51MomentT k M r s B t z : ℝ) ≤
      C * (fordLemma51ResonantTuplePairs (k := k) s M₂ r M B t z).card := by
    calc
      (fordLemma51MomentT k M r s B t z : ℝ) ≤
          C * (∑ x : FordLemma51BTuple s B, ∑ y : FordLemma51BTuple s B,
            fordLemma51TuplePairTentProduct k M r s B t z x y) := by
        simpa [C] using
          (fordLemma51MomentT_le_fiveScalar_tupleTentSum hr hM B t z)
      _ ≤ C * (fordLemma51ResonantTuplePairs
            (k := k) s M₂ r M B t z).card := by
        exact mul_le_mul_of_nonneg_left
          (fordLemma51TuplePairTentSum_le_card_resonantPairs
            hs hM₂ hr hM hBpos hBtop t z) hC
  have hcountNat := fordLemma51ResonantPairs_card_le_windowMoment_mul
    (k := k) (h := h) (g := g) (s := s) (M₂ := M₂) (r := r) (M := M) B t z
  have hcountReal :
      ((fordLemma51ResonantTuplePairs (k := k) s M₂ r M B t z).card : ℝ) ≤
        (fordLemma51WindowMoment k h g s B : ℝ) *
          (∏ j : FordLemma51DegreeWindow k h g,
            (fordLemma51ResonantSet s M₂ r M t z j.1).card : ℕ) := by
    exact_mod_cast hcountNat
  have hprod :
      ((∏ j : FordLemma51DegreeWindow k h g,
          (fordLemma51ResonantSet s M₂ r M t z j.1).card : ℕ) : ℝ) ≤
        ∏ j : FordLemma51DegreeWindow k h g,
          fordLemma51RawW s M₂ r M t z j.1 := by
    push_cast
    apply Finset.prod_le_prod
    · intro j hj
      positivity
    · intro j hj
      exact fordLemma51ResonantSet_card_le_rawW hs hM₂ hr hM ht hz j.1
  calc
    (fordLemma51MomentT k M r s B t z : ℝ) ≤
        C * (fordLemma51ResonantTuplePairs (k := k) s M₂ r M B t z).card :=
      hmoment
    _ ≤ C * ((fordLemma51WindowMoment k h g s B : ℝ) *
          (∏ j : FordLemma51DegreeWindow k h g,
            (fordLemma51ResonantSet s M₂ r M t z j.1).card : ℕ)) :=
      mul_le_mul_of_nonneg_left hcountReal hC
    _ ≤ C * ((fordLemma51WindowMoment k h g s B : ℝ) *
          ∏ j : FordLemma51DegreeWindow k h g,
            fordLemma51RawW s M₂ r M t z j.1) := by
      gcongr
    _ = (5 * (r : ℝ)) ^ k * (M : ℝ) ^ fordVinogradovKappa k *
          (fordLemma51WindowMoment k h g s B : ℝ) *
            ∏ j : FordLemma51DegreeWindow k h g,
              fordLemma51RawW s M₂ r M t z j.1 := by
      simp only [C]
      ring

#print axioms fordLemma51SourceRadius_pos
#print axioms abs_fordTaylorGamma_pos
#print axioms fordLemma51ResonantSet_card_le_rawSpacingBound
#print axioms fordLemma51ResonantSet_card_le_trivial
#print axioms fordLemma51ResonantSet_card_le_rawW
#print axioms fordLemma51MomentT_le_windowMoment_mul_rawW

end

end GafniTao
