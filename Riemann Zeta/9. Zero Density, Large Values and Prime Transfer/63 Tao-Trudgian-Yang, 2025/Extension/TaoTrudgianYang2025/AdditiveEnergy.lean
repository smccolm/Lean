import Mathlib

/-!
# Approximate additive energy

The paper's finite multiset is represented by an indexed family. Consequently,
equal real values at different indices remain distinct in every count. The
unit-scale specialization is the source definition `energy-def`.
-/

namespace TaoTrudgianYang2025

theorem card_le_three_of_oneSeparated_of_mem_interval
    (W : Finset ℝ)
    (hsep : ∀ x ∈ W, ∀ y ∈ W, x ≠ y → 1 ≤ |x - y|)
    {a b : ℝ} (hab : b - a ≤ 2)
    (hmem : ∀ x ∈ W, a ≤ x ∧ x ≤ b) :
    W.card ≤ 3 := by
  by_contra hcard
  have hfour : 4 ≤ W.card := by omega
  let L : List ℝ := W.sort
  have hlen : 4 ≤ L.length := by simpa [L] using hfour
  let i0 : Fin L.length := ⟨0, by omega⟩
  let i1 : Fin L.length := ⟨1, by omega⟩
  let i2 : Fin L.length := ⟨2, by omega⟩
  let i3 : Fin L.length := ⟨3, by omega⟩
  let x0 := L.get i0
  let x1 := L.get i1
  let x2 := L.get i2
  let x3 := L.get i3
  have hsorted : L.SortedLT := by
    simpa [L] using Finset.sortedLT_sort W
  have hx01 : x0 < x1 := by
    exact hsorted (by simp [i0, i1])
  have hx12 : x1 < x2 := by
    exact hsorted (by simp [i1, i2])
  have hx23 : x2 < x3 := by
    exact hsorted (by simp [i2, i3])
  have hx0mem : x0 ∈ W := by
    have hm : x0 ∈ L := L.get_mem i0
    change x0 ∈ W.sort at hm
    exact (Finset.mem_sort (· ≤ ·)).mp hm
  have hx1mem : x1 ∈ W := by
    have hm : x1 ∈ L := L.get_mem i1
    change x1 ∈ W.sort at hm
    exact (Finset.mem_sort (· ≤ ·)).mp hm
  have hx2mem : x2 ∈ W := by
    have hm : x2 ∈ L := L.get_mem i2
    change x2 ∈ W.sort at hm
    exact (Finset.mem_sort (· ≤ ·)).mp hm
  have hx3mem : x3 ∈ W := by
    have hm : x3 ∈ L := L.get_mem i3
    change x3 ∈ W.sort at hm
    exact (Finset.mem_sort (· ≤ ·)).mp hm
  have hgap01 := hsep x1 hx1mem x0 hx0mem (ne_of_gt hx01)
  have hgap12 := hsep x2 hx2mem x1 hx1mem (ne_of_gt hx12)
  have hgap23 := hsep x3 hx3mem x2 hx2mem (ne_of_gt hx23)
  rw [abs_of_nonneg (sub_nonneg.mpr hx01.le)] at hgap01
  rw [abs_of_nonneg (sub_nonneg.mpr hx12.le)] at hgap12
  rw [abs_of_nonneg (sub_nonneg.mpr hx23.le)] at hgap23
  have hx0 := (hmem x0 hx0mem).1
  have hx3 := (hmem x3 hx3mem).2
  linarith

private theorem sortedList_length_le_interval
    (W : Finset ℝ)
    (hsep : ∀ x ∈ W, ∀ y ∈ W, x ≠ y → 1 ≤ |x - y|) :
    ∀ (L : List ℝ), L.Pairwise (· < ·) →
      (∀ x ∈ L, x ∈ W) →
      ∀ a b : ℝ, (∀ x ∈ L, a ≤ x ∧ x ≤ b) →
        0 ≤ b - a → (L.length : ℝ) ≤ b - a + 1 := by
  intro L hsorted hsub
  induction L with
  | nil =>
      intro a b _ hab
      simp
      linarith
  | cons x xs ih =>
      cases xs with
      | nil =>
          intro a b hmem _
          have hx := hmem x (by simp)
          simp
          linarith
      | cons y ys =>
          intro a b hmem hab
          have hxmem : x ∈ W := hsub x (by simp)
          have hymem : y ∈ W := hsub y (by simp)
          have hxy : x < y :=
            (List.pairwise_cons_cons_iff_of_trans.mp hsorted).1
          have hgap := hsep y hymem x hxmem (ne_of_gt hxy)
          rw [abs_of_nonneg (sub_nonneg.mpr hxy.le)] at hgap
          have htailSub : ∀ z ∈ y :: ys, z ∈ W := by
            intro z hz
            exact hsub z (by simp [hz])
          have htailMem : ∀ z ∈ y :: ys, y ≤ z ∧ z ≤ b := by
            intro z hz
            have hyz : y ≤ z := by
              rcases List.mem_cons.mp hz with hzy | hzys
              · subst z
                exact le_rfl
              · have hyz' := hsorted.tail.rel_head_tail (by simpa using hzys)
                simpa using hyz'.le
            exact ⟨hyz, (hmem z (by simp [hz])).2⟩
          have htail := ih hsorted.tail htailSub y b htailMem (by
            have hyb := (hmem y (by simp)).2
            linarith)
          have hax := (hmem x (by simp)).1
          simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
          norm_num at htail ⊢
          linarith

theorem oneSeparated_card_cast_le_interval_length_add_one
    (W : Finset ℝ)
    (hsep : ∀ x ∈ W, ∀ y ∈ W, x ≠ y → 1 ≤ |x - y|)
    {a b : ℝ} (hab : 0 ≤ b - a)
    (hmem : ∀ x ∈ W, a ≤ x ∧ x ≤ b) :
    (W.card : ℝ) ≤ b - a + 1 := by
  let L : List ℝ := W.sort
  have hsorted : L.Pairwise (· < ·) := by
    exact List.sortedLT_iff_pairwise.mp (by
      simpa [L] using Finset.sortedLT_sort W)
  have hsub : ∀ x ∈ L, x ∈ W := by
    intro x hx
    change x ∈ W.sort at hx
    exact (Finset.mem_sort (· ≤ ·)).mp hx
  have hmemL : ∀ x ∈ L, a ≤ x ∧ x ≤ b := by
    intro x hx
    exact hmem x (hsub x hx)
  simpa [L] using
    sortedList_length_le_interval W hsep L hsorted hsub a b hmemL hab

/-- Ordered quadruples over an arbitrary finite index type. -/
abbrev AdditiveQuadrupleOf (ι : Type*) := Fin 4 → ι

/-- Ordered quadruples of indices, retaining multiplicity. -/
abbrev AdditiveQuadruple (n : ℕ) := AdditiveQuadrupleOf (Fin n)

/-- Approximate additive energy of an arbitrary finite indexed family. -/
noncomputable def approximateAdditiveEnergyOf
    {ι : Type*} [Fintype ι] (r : ℝ) (W : ι → ℝ) : ℕ :=
  (Finset.univ.filter fun q : AdditiveQuadrupleOf ι ↦
    |W (q 0) + W (q 1) - W (q 2) - W (q 3)| ≤ r).card

/-- Approximate additive energy at tolerance `r`: the number of ordered
indexed quadruples satisfying `|t₁+t₂-t₃-t₄| ≤ r`. -/
noncomputable def approximateAdditiveEnergy
    {n : ℕ} (r : ℝ) (W : Fin n → ℝ) : ℕ :=
  approximateAdditiveEnergyOf r W

/-- The unit-tolerance additive energy used throughout the source paper. -/
noncomputable def additiveEnergy {n : ℕ} (W : Fin n → ℝ) : ℕ :=
  approximateAdditiveEnergy 1 W

/-- Unit-tolerance energy of a finite set.  The subtype is used as the index,
so this definition is compatible with the indexed-multiset definition while
not introducing an arbitrary enumeration. -/
noncomputable def finsetAdditiveEnergy (W : Finset ℝ) : ℕ :=
  approximateAdditiveEnergyOf 1 (fun t : ↥W ↦ (t : ℝ))

theorem approximateAdditiveEnergyOf_le_fourthPower
    {ι : Type*} [Fintype ι] (r : ℝ) (W : ι → ℝ) :
    approximateAdditiveEnergyOf r W ≤ Fintype.card ι ^ 4 := by
  calc
    approximateAdditiveEnergyOf r W ≤
        (Finset.univ : Finset (AdditiveQuadrupleOf ι)).card := by
      exact Finset.card_filter_le _ _
    _ = Fintype.card ι ^ 4 := by simp [AdditiveQuadrupleOf]

theorem square_le_approximateAdditiveEnergyOf
    {ι : Type*} [Fintype ι] {r : ℝ} (hr : 0 ≤ r) (W : ι → ℝ) :
    Fintype.card ι ^ 2 ≤ approximateAdditiveEnergyOf r W := by
  let diagonal : (ι × ι) ↪ AdditiveQuadrupleOf ι :=
    { toFun := fun p : ι × ι ↦ ![p.1, p.2, p.1, p.2]
      inj' := by
        intro p q hpq
        apply Prod.ext
        · exact congrFun hpq 0
        · exact congrFun hpq 1 }
  let diagonals : Finset (AdditiveQuadrupleOf ι) := Finset.univ.map diagonal
  have hsubset : diagonals ⊆
      Finset.univ.filter (fun q : AdditiveQuadrupleOf ι ↦
        |W (q 0) + W (q 1) - W (q 2) - W (q 3)| ≤ r) := by
    intro q hq
    simp only [diagonals, Finset.mem_map] at hq
    obtain ⟨p, _, rfl⟩ := hq
    simp [diagonal, hr]
  calc
    Fintype.card ι ^ 2 = diagonals.card := by
      simp [diagonals, diagonal, pow_two]
    _ ≤ (Finset.univ.filter (fun q : AdditiveQuadrupleOf ι ↦
        |W (q 0) + W (q 1) - W (q 2) - W (q 3)| ≤ r)).card :=
      Finset.card_le_card hsubset
    _ = approximateAdditiveEnergyOf r W := rfl

theorem finset_card_square_le_additiveEnergy (W : Finset ℝ) :
    W.card ^ 2 ≤ finsetAdditiveEnergy W := by
  simpa [finsetAdditiveEnergy] using
    (square_le_approximateAdditiveEnergyOf (ι := ↥W) (r := (1 : ℝ))
      (by norm_num) (fun t : ↥W ↦ (t : ℝ)))

theorem finset_additiveEnergy_le_fourthPower (W : Finset ℝ) :
    finsetAdditiveEnergy W ≤ W.card ^ 4 := by
  simpa [finsetAdditiveEnergy] using
    (approximateAdditiveEnergyOf_le_fourthPower (ι := ↥W) (1 : ℝ)
      (fun t : ↥W ↦ (t : ℝ)))

/-- For a one-separated set, fixing the first three entries leaves at most
three choices for the fourth.  This gives the paper's cubic upper bound up to
an absolute constant. -/
theorem finset_additiveEnergy_le_three_mul_cube
    (W : Finset ℝ)
    (hsep : ∀ x ∈ W, ∀ y ∈ W, x ≠ y → 1 ≤ |x - y|) :
    finsetAdditiveEnergy W ≤ 3 * W.card ^ 3 := by
  let good : Finset (AdditiveQuadrupleOf ↥W) :=
    Finset.univ.filter fun q ↦
      |(q 0 : ℝ) + (q 1 : ℝ) - (q 2 : ℝ) - (q 3 : ℝ)| ≤ 1
  let project : AdditiveQuadrupleOf ↥W → ↥W × ↥W × ↥W :=
    fun q ↦ (q 0, q 1, q 2)
  have hfiber : ∀ p ∈ good.image project,
      (good.filter fun q ↦ project q = p).card ≤ 3 := by
    intro p hp
    let fiber := good.filter fun q ↦ project q = p
    let lastValue : AdditiveQuadrupleOf ↥W → ℝ := fun q ↦ (q 3 : ℝ)
    let values : Finset ℝ := fiber.image lastValue
    have hvaluesSep : ∀ x ∈ values, ∀ y ∈ values,
        x ≠ y → 1 ≤ |x - y| := by
      intro x hx y hy hxy
      obtain ⟨qx, hqx, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨qy, hqy, rfl⟩ := Finset.mem_image.mp hy
      exact hsep (qx 3) (qx 3).property (qy 3) (qy 3).property hxy
    let center : ℝ := (p.1 : ℝ) + (p.2.1 : ℝ) - (p.2.2 : ℝ)
    have hvaluesInterval : ∀ x ∈ values,
        center - 1 ≤ x ∧ x ≤ center + 1 := by
      intro x hx
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
      have hqGood := (Finset.mem_filter.mp
        (Finset.mem_filter.mp hq).1).2
      have hqProject := (Finset.mem_filter.mp hq).2
      have h0 : q 0 = p.1 := congrArg Prod.fst hqProject
      have h1 : q 1 = p.2.1 := congrArg (fun z ↦ z.2.1) hqProject
      have h2 : q 2 = p.2.2 := congrArg (fun z ↦ z.2.2) hqProject
      rw [h0, h1, h2, abs_le] at hqGood
      dsimp [center]
      constructor <;> linarith
    have hlastInj : Set.InjOn lastValue (↑fiber : Set (AdditiveQuadrupleOf ↥W)) := by
      intro q hq r hr hlast
      have hqProject := (Finset.mem_filter.mp hq).2
      have hrProject := (Finset.mem_filter.mp hr).2
      have hproject : project q = project r := hqProject.trans hrProject.symm
      funext j
      fin_cases j
      · exact congrArg Prod.fst hproject
      · exact congrArg (fun z ↦ z.2.1) hproject
      · exact congrArg (fun z ↦ z.2.2) hproject
      · apply Subtype.ext
        exact hlast
    calc
      fiber.card = values.card :=
        (Finset.card_image_iff.mpr hlastInj).symm
      _ ≤ 3 := card_le_three_of_oneSeparated_of_mem_interval values
        hvaluesSep (by dsimp [center]; linarith) hvaluesInterval
  have hmain := Finset.card_le_mul_card_image good 3 hfiber
  change good.card ≤ 3 * W.card ^ 3
  calc
    good.card ≤ 3 * (good.image project).card := hmain
    _ ≤ 3 * Fintype.card (↥W × ↥W × ↥W) := by
      gcongr
      exact Finset.card_le_univ _
    _ = 3 * W.card ^ 3 := by
      simp only [Fintype.card_prod, Fintype.card_coe]
      ring

/-- Approximate energy never exceeds the number `n⁴` of ordered indexed
quadruples. -/
theorem approximateAdditiveEnergy_le_fourthPower
    {n : ℕ} (r : ℝ) (W : Fin n → ℝ) :
    approximateAdditiveEnergy r W ≤ n ^ 4 := by
  calc
    approximateAdditiveEnergy r W ≤
        (Finset.univ : Finset (AdditiveQuadruple n)).card := by
      exact Finset.card_filter_le _ _
    _ = n ^ 4 := by simp [AdditiveQuadruple]

/-- The diagonal quadruples `(i,j,i,j)` give the elementary lower bound
`n² ≤ E_r(W)` whenever the tolerance is nonnegative. -/
theorem square_le_approximateAdditiveEnergy
    {n : ℕ} {r : ℝ} (hr : 0 ≤ r) (W : Fin n → ℝ) :
    n ^ 2 ≤ approximateAdditiveEnergy r W := by
  let diagonal : (Fin n × Fin n) ↪ AdditiveQuadruple n :=
    { toFun := fun p : Fin n × Fin n ↦ ![p.1, p.2, p.1, p.2]
      inj' := by
        intro p q hpq
        apply Prod.ext
        · exact congrFun hpq 0
        · exact congrFun hpq 1 }
  let diagonals : Finset (AdditiveQuadruple n) := Finset.univ.map diagonal
  have hsubset : diagonals ⊆
      Finset.univ.filter (fun q : AdditiveQuadruple n ↦
        |W (q 0) + W (q 1) - W (q 2) - W (q 3)| ≤ r) := by
    intro q hq
    simp only [diagonals, Finset.mem_map] at hq
    obtain ⟨p, _, rfl⟩ := hq
    simp [diagonal, hr]
  calc
    n ^ 2 = diagonals.card := by
      simp [diagonals, diagonal, pow_two]
    _ ≤ (Finset.univ.filter (fun q : AdditiveQuadruple n ↦
        |W (q 0) + W (q 1) - W (q 2) - W (q 3)| ≤ r)).card :=
      Finset.card_le_card hsubset
    _ = approximateAdditiveEnergy r W := rfl

theorem square_le_additiveEnergy {n : ℕ} (W : Fin n → ℝ) :
    n ^ 2 ≤ additiveEnergy W := by
  exact square_le_approximateAdditiveEnergy (by norm_num) W

theorem additiveEnergy_le_fourthPower {n : ℕ} (W : Fin n → ℝ) :
    additiveEnergy W ≤ n ^ 4 :=
  approximateAdditiveEnergy_le_fourthPower 1 W

end TaoTrudgianYang2025
