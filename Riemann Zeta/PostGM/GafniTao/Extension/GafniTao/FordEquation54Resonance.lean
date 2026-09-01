import GafniTao.FordEquation54Bound

/-!
# Ford Lemma 5.1: the resonant displacement sets in equation (5.4)

The tuple entries in Ford's set `B` are embedded into the complete
Vinogradov box without changing their values.  This yields the source's strict
displacement cutoff `|d_j| < s M₂^(j+1) - 1`, which is then combined with
the literal periodic-tent support condition.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- A positive element of `B ⊆ [1,M₂]`, reindexed as an element of
`Fin M₂` while retaining its source value after the standard `+1` shift. -/
def fordLemma51TupleToVinogradov
    {s M₂ : ℕ} {B : Finset ℕ}
    (hBpos : ∀ b ∈ B, 0 < b) (hBtop : ∀ b ∈ B, b ≤ M₂)
    (x : FordLemma51BTuple s B) : FordVinogradovTuple s M₂ :=
  fun i => ⟨(x i : ℕ) - 1, by
    have hp := hBpos (x i) (x i).property
    have ht := hBtop (x i) (x i).property
    omega⟩

theorem fordLemma51TupleToVinogradov_value
    {s M₂ : ℕ} {B : Finset ℕ}
    (hBpos : ∀ b ∈ B, 0 < b) (hBtop : ∀ b ∈ B, b ≤ M₂)
    (x : FordLemma51BTuple s B) (i : Fin s) :
    ((fordLemma51TupleToVinogradov hBpos hBtop x i : ℕ) + 1) = (x i : ℕ) := by
  change ((x i : ℕ) - 1) + 1 = (x i : ℕ)
  exact Nat.sub_add_cancel (hBpos (x i) (x i).property)

theorem fordLemma51DifferenceVector_eq_vinogradovSub
    {k s M₂ : ℕ} {B : Finset ℕ}
    (hBpos : ∀ b ∈ B, 0 < b) (hBtop : ∀ b ∈ B, b ≤ M₂)
    (x y : FordLemma51BTuple s B) :
    fordLemma51DifferenceVector k s B x y =
      fordVinogradovPowerVector s k M₂
          (fordLemma51TupleToVinogradov hBpos hBtop x) -
        fordVinogradovPowerVector s k M₂
          (fordLemma51TupleToVinogradov hBpos hBtop y) := by
  funext j
  unfold fordLemma51DifferenceVector fordVinogradovPowerVector
  simp only [Pi.sub_apply]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _hi
    congr 1
    exact_mod_cast (fordLemma51TupleToVinogradov_value
      hBpos hBtop x i).symm
  · apply Finset.sum_congr rfl
    intro i _hi
    congr 1
    exact_mod_cast (fordLemma51TupleToVinogradov_value
      hBpos hBtop y i).symm

theorem fordLemma51DifferenceVector_mem_vinogradovBox
    {k s M₂ : ℕ} {B : Finset ℕ} (hM₂ : 1 ≤ M₂)
    (hBpos : ∀ b ∈ B, 0 < b) (hBtop : ∀ b ∈ B, b ≤ M₂)
    (x y : FordLemma51BTuple s B) :
    fordLemma51DifferenceVector k s B x y ∈
      fordVinogradovDisplacementBox s k M₂ := by
  rw [fordLemma51DifferenceVector_eq_vinogradovSub hBpos hBtop]
  exact fordVinogradovPowerVector_sub_mem_box hM₂ _ _

/-- The strict source cutoff used in the definition of `D_j`.  The strictness
costs the source hypothesis `s ≥ 2`; the underlying complete-box radius is
`s(M₂^(j+1)-1)`. -/
theorem fordLemma51DifferenceVector_abs_lt_sourceRadius
    {k s M₂ : ℕ} {B : Finset ℕ} (hs : 2 ≤ s) (hM₂ : 1 ≤ M₂)
    (hBpos : ∀ b ∈ B, 0 < b) (hBtop : ∀ b ∈ B, b ≤ M₂)
    (x y : FordLemma51BTuple s B) (j : Fin k) :
    |((fordLemma51DifferenceVector k s B x y j : ℤ) : ℝ)| <
      (s * M₂ ^ ((j : ℕ) + 1) : ℕ) - 1 := by
  have hmem := fordLemma51DifferenceVector_mem_vinogradovBox
    (k := k) hM₂ hBpos hBtop x y
  rw [fordVinogradovDisplacementBox, Fintype.mem_piFinset] at hmem
  have hj := hmem j
  simp only [Finset.mem_Icc] at hj
  have habsInt :
      |fordLemma51DifferenceVector k s B x y j| ≤
        (fordVinogradovDisplacementRadius s M₂ j : ℤ) :=
    abs_le.mpr hj
  have hpow : 1 ≤ M₂ ^ ((j : ℕ) + 1) :=
    Nat.one_le_pow _ _ hM₂
  have hstrictNat :
      fordVinogradovDisplacementRadius s M₂ j <
        s * M₂ ^ ((j : ℕ) + 1) - 1 := by
    unfold fordVinogradovDisplacementRadius
    have hle : s ≤ s * M₂ ^ ((j : ℕ) + 1) := by
      simpa using Nat.mul_le_mul_left s hpow
    rw [Nat.mul_sub_left_distrib]
    simp only [mul_one]
    omega
  have habsReal :
      |((fordLemma51DifferenceVector k s B x y j : ℤ) : ℝ)| ≤
        (fordVinogradovDisplacementRadius s M₂ j : ℝ) := by
    exact_mod_cast habsInt
  have hstrictReal :
      (fordVinogradovDisplacementRadius s M₂ j : ℝ) <
        (s * M₂ ^ ((j : ℕ) + 1) : ℕ) - 1 := by
    calc
      (fordVinogradovDisplacementRadius s M₂ j : ℝ) <
          (s * M₂ ^ ((j : ℕ) + 1) - 1 : ℕ) := by
        exact_mod_cast hstrictNat
      _ = (s * M₂ ^ ((j : ℕ) + 1) : ℕ) - 1 := by
        rw [Nat.cast_sub]
        · norm_num
        · exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  exact habsReal.trans_lt hstrictReal

/-- Ford's literal real cutoff `s M₂^(j+1) - 1`. -/
def fordLemma51SourceRadius
    {k : ℕ} (s M₂ : ℕ) (j : Fin k) : ℝ :=
  (s * M₂ ^ ((j : ℕ) + 1) : ℕ) - 1

/-- The width of the degree-`j+1` periodic tent. -/
def fordLemma51TentWidth
    {k : ℕ} (r M : ℕ) (j : Fin k) : ℝ :=
  1 / (2 * ((r * M ^ ((j : ℕ) + 1) : ℕ) : ℝ))

/-- Ford's finite resonant set `D_j`, expressed using the exact spacing set
already used in equation (5.6).  Absolute value removes the alternating sign
of `gamma_j` without changing distance to an integer. -/
def fordLemma51ResonantSet
    {k : ℕ} (s M₂ r M : ℕ) (t z : ℝ) (j : Fin k) : Finset ℤ :=
  (fordSpacingSet (fordLemma51SourceRadius s M₂ j)
    |fordTaylorGamma t z (j : ℕ)| (fordLemma51TentWidth r M j)).filter fun d =>
      |(d : ℝ)| < fordLemma51SourceRadius s M₂ j

theorem mem_fordLemma51ResonantSet
    {k s M₂ r M : ℕ} {t z : ℝ} {j : Fin k} {d : ℤ} :
    d ∈ fordLemma51ResonantSet s M₂ r M t z j ↔
      |(d : ℝ)| < fordLemma51SourceRadius s M₂ j ∧
        ∃ m : ℤ,
          |(d : ℝ) * |fordTaylorGamma t z (j : ℕ)| - m| <
            fordLemma51TentWidth r M j := by
  rw [fordLemma51ResonantSet, Finset.mem_filter, mem_fordSpacingSet]
  constructor
  · rintro ⟨⟨_hle, hm⟩, hlt⟩
    exact ⟨hlt, hm⟩
  · rintro ⟨hlt, hm⟩
    exact ⟨⟨hlt.le, hm⟩, hlt⟩

theorem fordLemma51TentWidth_pos
    {k r M : ℕ} (hr : 0 < r) (hM : 0 < M) (j : Fin k) :
    0 < fordLemma51TentWidth r M j := by
  unfold fordLemma51TentWidth
  positivity

theorem exists_int_abs_mul_abs_lt_of_unit_norm_lt
    {d : ℤ} {gamma delta : ℝ}
    (h : ‖(((d : ℝ) * gamma : ℝ) : UnitAddCircle)‖ < delta) :
    ∃ m : ℤ, |(d : ℝ) * |gamma| - m| < delta := by
  rw [UnitAddCircle.norm_eq] at h
  by_cases hgamma : 0 ≤ gamma
  · refine ⟨round ((d : ℝ) * gamma), ?_⟩
    simpa [abs_of_nonneg hgamma] using h
  · have hgammaNeg : gamma < 0 := lt_of_not_ge hgamma
    refine ⟨-round ((d : ℝ) * gamma), ?_⟩
    rw [abs_of_neg hgammaNeg]
    push_cast
    rw [show (d : ℝ) * -gamma - -↑(round ((d : ℝ) * gamma)) =
        -((d : ℝ) * gamma - ↑(round ((d : ℝ) * gamma))) by ring,
      abs_neg]
    exact h

theorem fordLemma51_difference_mem_resonantSet_of_tent_ne_zero
    {k s M₂ r M : ℕ} (hs : 2 ≤ s) (hM₂ : 1 ≤ M₂)
    (hr : 0 < r) (hM : 0 < M) {B : Finset ℕ}
    (hBpos : ∀ b ∈ B, 0 < b) (hBtop : ∀ b ∈ B, b ≤ M₂)
    (t z : ℝ) (x y : FordLemma51BTuple s B) (j : Fin k)
    (htent : fordTent
      (fordLemma51DifferenceCoordinate k t z
        (fordLemma51DifferenceVector k s B x y) j)
      (fordLemma51TentWidth r M j) ≠ 0) :
    fordLemma51DifferenceVector k s B x y j ∈
      fordLemma51ResonantSet s M₂ r M t z j := by
  let d := fordLemma51DifferenceVector k s B x y j
  let gamma := fordTaylorGamma t z (j : ℕ)
  let delta := fordLemma51TentWidth r M j
  have hdelta : 0 < delta := fordLemma51TentWidth_pos hr hM j
  have hnorm :
      ‖(((d : ℝ) * gamma : ℝ) : UnitAddCircle)‖ < delta := by
    by_contra hnot
    have hle : delta ≤ ‖(((d : ℝ) * gamma : ℝ) : UnitAddCircle)‖ :=
      le_of_not_gt hnot
    apply htent
    simpa [fordLemma51DifferenceCoordinate, d, gamma, delta, mul_comm] using
      (fordTent_eq_zero_of_le_norm hdelta hle)
  have hm := exists_int_abs_mul_abs_lt_of_unit_norm_lt hnorm
  apply Finset.mem_filter.mpr
  constructor
  · apply mem_fordSpacingSet.mpr
    exact ⟨(fordLemma51DifferenceVector_abs_lt_sourceRadius
      hs hM₂ hBpos hBtop x y j).le, hm⟩
  · exact fordLemma51DifferenceVector_abs_lt_sourceRadius
      hs hM₂ hBpos hBtop x y j

theorem fordLemma51_tent_eq_zero_of_difference_not_mem_resonantSet
    {k s M₂ r M : ℕ} (hs : 2 ≤ s) (hM₂ : 1 ≤ M₂)
    (hr : 0 < r) (hM : 0 < M) {B : Finset ℕ}
    (hBpos : ∀ b ∈ B, 0 < b) (hBtop : ∀ b ∈ B, b ≤ M₂)
    (t z : ℝ) (x y : FordLemma51BTuple s B) (j : Fin k)
    (hnot : fordLemma51DifferenceVector k s B x y j ∉
      fordLemma51ResonantSet s M₂ r M t z j) :
    fordTent
      (fordLemma51DifferenceCoordinate k t z
        (fordLemma51DifferenceVector k s B x y) j)
      (fordLemma51TentWidth r M j) = 0 := by
  by_contra hzero
  exact hnot (fordLemma51_difference_mem_resonantSet_of_tent_ne_zero
    hs hM₂ hr hM hBpos hBtop t z x y j hzero)

/-- The exact finite set of ordered tuple pairs whose displacement lies in
every source resonant set `D_j`. -/
def fordLemma51ResonantTuplePairs
    {k : ℕ} (s M₂ r M : ℕ) (B : Finset ℕ) (t z : ℝ) :
    Finset (FordLemma51BTuple s B × FordLemma51BTuple s B) :=
  Finset.univ.filter fun p => ∀ j : Fin k,
    fordLemma51DifferenceVector k s B p.1 p.2 j ∈
      fordLemma51ResonantSet s M₂ r M t z j

theorem fordLemma51TuplePairTentProduct_eq_zero_of_not_resonant
    {k s M₂ r M : ℕ} (hs : 2 ≤ s) (hM₂ : 1 ≤ M₂)
    (hr : 0 < r) (hM : 0 < M) {B : Finset ℕ}
    (hBpos : ∀ b ∈ B, 0 < b) (hBtop : ∀ b ∈ B, b ≤ M₂)
    (t z : ℝ) (x y : FordLemma51BTuple s B)
    (hnot : ¬ ∀ j : Fin k,
      fordLemma51DifferenceVector k s B x y j ∈
        fordLemma51ResonantSet s M₂ r M t z j) :
    fordLemma51TuplePairTentProduct k M r s B t z x y = 0 := by
  rw [not_forall] at hnot
  obtain ⟨j, hj⟩ := hnot
  unfold fordLemma51TuplePairTentProduct
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  exact fordLemma51_tent_eq_zero_of_difference_not_mem_resonantSet
    hs hM₂ hr hM hBpos hBtop t z x y j hj

/-- The complete tuple-pair tent sum is supported on Ford's exact resonant
pair set.  Each surviving product is at most one, so the sum is bounded by
the literal cardinality of that set. -/
theorem fordLemma51TuplePairTentSum_le_card_resonantPairs
    {k s M₂ r M : ℕ} (hs : 2 ≤ s) (hM₂ : 1 ≤ M₂)
    (hr : 0 < r) (hM : 0 < M) {B : Finset ℕ}
    (hBpos : ∀ b ∈ B, 0 < b) (hBtop : ∀ b ∈ B, b ≤ M₂)
    (t z : ℝ) :
    (∑ x : FordLemma51BTuple s B, ∑ y : FordLemma51BTuple s B,
        fordLemma51TuplePairTentProduct k M r s B t z x y) ≤
      (fordLemma51ResonantTuplePairs (k := k) s M₂ r M B t z).card := by
  rw [← Finset.sum_product']
  calc
    (∑ p ∈ (Finset.univ ×ˢ Finset.univ),
        fordLemma51TuplePairTentProduct k M r s B t z p.1 p.2) ≤
        ∑ p ∈ (Finset.univ ×ˢ Finset.univ),
          if p ∈ fordLemma51ResonantTuplePairs (k := k) s M₂ r M B t z
          then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro p hp
      by_cases hres : p ∈ fordLemma51ResonantTuplePairs (k := k) s M₂ r M B t z
      · simp only [hres, if_true]
        exact fordLemma51TuplePairTentProduct_le_one hr hM B t z p.1 p.2
      · simp only [hres, if_false]
        have hnot : ¬ ∀ j : Fin k,
            fordLemma51DifferenceVector k s B p.1 p.2 j ∈
              fordLemma51ResonantSet s M₂ r M t z j := by
          simpa [fordLemma51ResonantTuplePairs] using hres
        rw [fordLemma51TuplePairTentProduct_eq_zero_of_not_resonant
          hs hM₂ hr hM hBpos hBtop t z p.1 p.2 hnot]
    _ = (fordLemma51ResonantTuplePairs (k := k) s M₂ r M B t z).card := by
      simp [fordLemma51ResonantTuplePairs]

#print axioms exists_int_abs_mul_abs_lt_of_unit_norm_lt
#print axioms mem_fordLemma51ResonantSet
#print axioms fordLemma51_difference_mem_resonantSet_of_tent_ne_zero
#print axioms fordLemma51_tent_eq_zero_of_difference_not_mem_resonantSet
#print axioms fordLemma51TuplePairTentProduct_eq_zero_of_not_resonant
#print axioms fordLemma51TuplePairTentSum_le_card_resonantPairs

#print axioms fordLemma51TupleToVinogradov_value
#print axioms fordLemma51DifferenceVector_eq_vinogradovSub
#print axioms fordLemma51DifferenceVector_mem_vinogradovBox
#print axioms fordLemma51DifferenceVector_abs_lt_sourceRadius

end

end GafniTao
