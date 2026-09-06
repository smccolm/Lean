import GafniTao.MixedEnergyExtraction
import Mathlib.Combinatorics.Additive.Energy

/-!
# Exact mixed-energy Cauchy--Schwarz infrastructure

The four detector coordinates need not select the same dyadic polynomial.
This file begins the finite additive-combinatorial reduction which bounds a
mixed energy by the four corresponding self energies.  It works with literal
difference fibres, so no same-scale assumption is introduced.
-/

open scoped BigOperators Combinatorics.Additive

namespace GafniTao

noncomputable section

private theorem sum_sq_card_fibers
    {Alpha Beta : Type*} [DecidableEq Alpha] [DecidableEq Beta]
    (S : Finset Alpha) (key : Alpha -> Beta) :
    (∑ z ∈ S.image key,
        ((S.filter fun x => key x = z).card : Nat) ^ 2) =
      ∑ p ∈ S, ∑ q ∈ S, if key p = key q then 1 else 0 := by
  classical
  simpa only [Finset.card_eq_sum_ones, Nat.mul_one, Nat.one_mul] using
    (show
      (∑ z ∈ S.image key,
          (∑ x ∈ S.filter (fun y => key y = z), (1 : Nat)) ^ 2) =
        ∑ p ∈ S, ∑ q ∈ S,
          if key p = key q then (1 : Nat) * 1 else 0 by
      simp only [pow_two, Finset.sum_mul_sum, Finset.sum_filter]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q hq
      by_cases hkey : key p = key q
      · rw [Finset.sum_eq_single (key p)]
        · simp [hkey]
        · intro z hz hzne
          have hpne : key p ≠ z := fun hpz => hzne hpz.symm
          simp [hpne]
        · intro hnot
          exact (hnot (Finset.mem_image.mpr ⟨p, hp, rfl⟩)).elim
      · simp [hkey])

/-- Ordered differences represented by `A × B`. -/
def differenceValue (p : Int × Int) : Int := p.1 - p.2

noncomputable def differenceBins (A B : Finset Int) : Finset Int :=
  (A ×ˢ B).image differenceValue

noncomputable def differenceCount (A B : Finset Int) (z : Int) : Nat :=
  ((A ×ˢ B).filter fun p => differenceValue p = z).card

noncomputable def differenceSquareSum (A B : Finset Int) : Nat :=
  ∑ z ∈ differenceBins A B, differenceCount A B z ^ 2

/-- The squared mass of the literal difference fibres is Mathlib's exact
cross additive energy. -/
theorem differenceSquareSum_eq_addEnergy (A B : Finset Int) :
    differenceSquareSum A B = Finset.addEnergy A B := by
  classical
  unfold differenceSquareSum differenceBins differenceCount
  rw [sum_sq_card_fibers (A ×ˢ B) differenceValue]
  let swapMiddle : ((Int × Int) × (Int × Int)) ≃
      ((Int × Int) × (Int × Int)) :=
    { toFun := fun q => ((q.1.1, q.2.2), (q.2.1, q.1.2))
      invFun := fun q => ((q.1.1, q.2.2), (q.2.1, q.1.2))
      left_inv := by rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩; rfl
      right_inv := by rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩; rfl }
  let D := ((A ×ˢ B) ×ˢ (A ×ˢ B)).filter fun q =>
    differenceValue q.1 = differenceValue q.2
  have hDiffCard :
      (∑ p ∈ A ×ˢ B, ∑ q ∈ A ×ˢ B,
        if differenceValue p = differenceValue q then 1 else 0) = D.card := by
    simp only [D, Finset.card_eq_sum_ones, Finset.sum_filter,
      Finset.sum_product]
  rw [hDiffCard, Finset.addEnergy_eq_card_filter]
  apply Finset.card_equiv swapMiddle
  intro q
  rcases q with ⟨⟨a, b⟩, ⟨c, d⟩⟩
  constructor
  · intro h
    have hmem := (Finset.mem_filter.mp h).1
    have hdiff := (Finset.mem_filter.mp h).2
    apply Finset.mem_filter.mpr
    constructor
    · rcases Finset.mem_product.mp hmem with ⟨hab, hcd⟩
      rcases Finset.mem_product.mp hab with ⟨ha, hb⟩
      rcases Finset.mem_product.mp hcd with ⟨hc, hd⟩
      exact Finset.mem_product.mpr
        ⟨Finset.mem_product.mpr ⟨ha, hd⟩,
          Finset.mem_product.mpr ⟨hc, hb⟩⟩
    · change a + d = c + b
      change a - b = c - d at hdiff
      omega
  · intro h
    have hmem := (Finset.mem_filter.mp h).1
    have hadd := (Finset.mem_filter.mp h).2
    apply Finset.mem_filter.mpr
    constructor
    · dsimp only [swapMiddle] at hmem
      rcases Finset.mem_product.mp hmem with ⟨had, hcb⟩
      rcases Finset.mem_product.mp had with ⟨ha, hd⟩
      rcases Finset.mem_product.mp hcb with ⟨hc, hb⟩
      exact Finset.mem_product.mpr
        ⟨Finset.mem_product.mpr ⟨ha, hb⟩,
          Finset.mem_product.mpr ⟨hc, hd⟩⟩
    · change a + d = c + b at hadd
      change a - b = c - d
      omega

/-- Correlation of the two self-difference representation functions. -/
noncomputable def selfDifferenceCorrelation (A B : Finset Int) : Nat :=
  ∑ p ∈ A ×ˢ A, differenceCount B B (-differenceValue p)

/-- The self-difference correlation counts exactly the cross additive
energy. -/
theorem selfDifferenceCorrelation_eq_addEnergy (A B : Finset Int) :
    selfDifferenceCorrelation A B = Finset.addEnergy A B := by
  classical
  unfold selfDifferenceCorrelation differenceCount differenceValue
  rw [Finset.addEnergy]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter,
    Finset.sum_product]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro d hd
  congr 1
  apply propext
  constructor <;> intro h <;> omega

/-- Regrouping the same correlation by the difference represented in
`A × A`. -/
theorem selfDifferenceCorrelation_eq_sum_counts (A B : Finset Int) :
    selfDifferenceCorrelation A B =
      ∑ z ∈ differenceBins A A,
        differenceCount A A z * differenceCount B B (-z) := by
  classical
  unfold selfDifferenceCorrelation differenceBins differenceCount
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := A ×ˢ A) (t := (A ×ˢ A).image differenceValue)
    (g := differenceValue)
    (fun p hp => Finset.mem_image.mpr ⟨p, hp, rfl⟩)]
  apply Finset.sum_congr rfl
  intro z hz
  calc
    (∑ i ∈ A ×ˢ A with differenceValue i = z,
        ((B ×ˢ B).filter fun p => differenceValue p = -differenceValue i).card) =
        ∑ i ∈ A ×ˢ A, if differenceValue i = z then
          ((B ×ˢ B).filter fun p => differenceValue p = -z).card else 0 := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hiz : differenceValue i = z
      · simp only [hiz, ↓reduceIte]
      · simp only [hiz, ↓reduceIte]
    _ = ((A ×ˢ A).filter (fun p => differenceValue p = z)).card *
        ((B ×ˢ B).filter fun p => differenceValue p = -z).card := by
      rw [← Finset.sum_filter]
      rw [Finset.sum_const, Nat.nsmul_eq_mul]

theorem differenceCount_eq_zero_of_not_mem_bins
    {A B : Finset Int} {z : Int} (hz : z ∉ differenceBins A B) :
    differenceCount A B z = 0 := by
  unfold differenceBins at hz
  unfold differenceCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro p hp
  exact fun hkey => hz (Finset.mem_image.mpr ⟨p, hp, hkey⟩)

/-- Cauchy--Schwarz for exact cross additive energy.  This is the finite
form of `E(A,B)^2 ≤ E(A) E(B)`. -/
theorem sq_addEnergy_le_mul_self (A B : Finset Int) :
    (Finset.addEnergy A B : Real) ^ 2 ≤
      (Finset.addEnergy A A : Real) * (Finset.addEnergy B B : Real) := by
  classical
  let SA := differenceBins A A
  let SB := (differenceBins B B).image fun z => -z
  let U := SA ∪ SB
  let F : Int -> Real := fun z => differenceCount A A z
  let G : Int -> Real := fun z => differenceCount B B (-z)
  have hCorr :
      (Finset.addEnergy A B : Real) = ∑ z ∈ U, F z * G z := by
    rw [← selfDifferenceCorrelation_eq_addEnergy A B,
      selfDifferenceCorrelation_eq_sum_counts]
    simp only [Nat.cast_sum, Nat.cast_mul]
    change (∑ z ∈ SA, F z * G z) = ∑ z ∈ U, F z * G z
    apply Finset.sum_subset Finset.subset_union_left
    intro z hzU hzSA
    have hz0 : differenceCount A A z = 0 :=
      differenceCount_eq_zero_of_not_mem_bins hzSA
    simp only [F, hz0, Nat.cast_zero, zero_mul]
  have hFSq : ∑ z ∈ U, F z ^ 2 = (Finset.addEnergy A A : Real) := by
    rw [← differenceSquareSum_eq_addEnergy A A]
    simp only [differenceSquareSum, Nat.cast_sum, Nat.cast_pow]
    change (∑ z ∈ U, F z ^ 2) = ∑ z ∈ SA, F z ^ 2
    symm
    apply Finset.sum_subset Finset.subset_union_left
    intro z hzU hzSA
    have hz0 : differenceCount A A z = 0 :=
      differenceCount_eq_zero_of_not_mem_bins hzSA
    norm_num [F, hz0]
  have hGSq : ∑ z ∈ U, G z ^ 2 = (Finset.addEnergy B B : Real) := by
    have hImage :
        ∑ z ∈ SB, G z ^ 2 =
          ∑ z ∈ differenceBins B B,
            (differenceCount B B z : Real) ^ 2 := by
      dsimp only [SB]
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro z hz
        simp only [G, neg_neg]
      · intro x hx y hy hxy
        exact neg_injective hxy
    calc
      ∑ z ∈ U, G z ^ 2 = ∑ z ∈ SB, G z ^ 2 := by
        symm
        apply Finset.sum_subset Finset.subset_union_right
        intro z hzU hzSB
        have hzNot : -z ∉ differenceBins B B := by
          intro hz
          apply hzSB
          exact Finset.mem_image.mpr ⟨-z, hz, by simp⟩
        have hz0 : differenceCount B B (-z) = 0 :=
          differenceCount_eq_zero_of_not_mem_bins hzNot
        norm_num [G, hz0]
      _ = ∑ z ∈ differenceBins B B,
          (differenceCount B B z : Real) ^ 2 := hImage
      _ = (differenceSquareSum B B : Real) := by
        simp only [differenceSquareSum, Nat.cast_sum, Nat.cast_pow]
      _ = (Finset.addEnergy B B : Real) := by
        rw [differenceSquareSum_eq_addEnergy]
  rw [hCorr]
  calc
    (∑ z ∈ U, F z * G z) ^ 2 ≤
        (∑ z ∈ U, F z ^ 2) * (∑ z ∈ U, G z ^ 2) :=
      Finset.sum_mul_sq_le_sq_mul_sq U F G
    _ = (Finset.addEnergy A A : Real) *
        (Finset.addEnergy B B : Real) := by rw [hFSq, hGSq]

/-- Exact integer mixed additive quadruples with prescribed defect. -/
noncomputable def exactMixedShiftQuadruples
    (j : Int) (A B C D : Finset Int) :
    Finset ((Int × Int) × (Int × Int)) :=
  (quadrupleProductOf A B C D).filter fun q =>
    q.1.1 + q.1.2 - q.2.1 - q.2.2 = j

noncomputable def ExactMixedShiftCount
    (j : Int) (A B C D : Finset Int) : Nat :=
  (exactMixedShiftQuadruples j A B C D).card

/-- Difference-fibre expression for one exact mixed defect. -/
noncomputable def shiftedMixedDifferenceCorrelation
    (j : Int) (A B C D : Finset Int) : Nat :=
  ∑ p ∈ A ×ˢ C, differenceCount D B (differenceValue p - j)

theorem shiftedMixedDifferenceCorrelation_eq_count
    (j : Int) (A B C D : Finset Int) :
    shiftedMixedDifferenceCorrelation j A B C D =
      ExactMixedShiftCount j A B C D := by
  classical
  let reorder : ((Int × Int) × (Int × Int)) ≃
      ((Int × Int) × (Int × Int)) :=
    { toFun := fun q => ((q.1.1, q.2.2), (q.1.2, q.2.1))
      invFun := fun q => ((q.1.1, q.2.1), (q.2.2, q.1.2))
      left_inv := by rintro ⟨⟨a, c⟩, ⟨d, b⟩⟩; rfl
      right_inv := by rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩; rfl }
  let L := ((A ×ˢ C) ×ˢ (D ×ˢ B)).filter fun q =>
    differenceValue q.2 = differenceValue q.1 - j
  have hLeft : shiftedMixedDifferenceCorrelation j A B C D = L.card := by
    unfold shiftedMixedDifferenceCorrelation differenceCount
    simp only [L, Finset.card_eq_sum_ones, Finset.sum_filter,
      Finset.sum_product]
  rw [hLeft]
  unfold ExactMixedShiftCount exactMixedShiftQuadruples quadrupleProductOf
  apply Finset.card_equiv reorder
  intro q
  rcases q with ⟨⟨a, c⟩, ⟨d, b⟩⟩
  constructor
  · intro h
    have hmem := (Finset.mem_filter.mp h).1
    have hdiff := (Finset.mem_filter.mp h).2
    apply Finset.mem_filter.mpr
    constructor
    · rcases Finset.mem_product.mp hmem with ⟨hac, hdb⟩
      rcases Finset.mem_product.mp hac with ⟨ha, hc⟩
      rcases Finset.mem_product.mp hdb with ⟨hd, hb⟩
      exact Finset.mem_product.mpr
        ⟨Finset.mem_product.mpr ⟨ha, hb⟩,
          Finset.mem_product.mpr ⟨hc, hd⟩⟩
    · change a + b - c - d = j
      change d - b = a - c - j at hdiff
      omega
  · intro h
    have hmem := (Finset.mem_filter.mp h).1
    have hsum := (Finset.mem_filter.mp h).2
    apply Finset.mem_filter.mpr
    constructor
    · dsimp only [reorder] at hmem
      rcases Finset.mem_product.mp hmem with ⟨hab, hcd⟩
      rcases Finset.mem_product.mp hab with ⟨ha, hb⟩
      rcases Finset.mem_product.mp hcd with ⟨hc, hd⟩
      exact Finset.mem_product.mpr
        ⟨Finset.mem_product.mpr ⟨ha, hc⟩,
          Finset.mem_product.mpr ⟨hd, hb⟩⟩
    · change a + b - c - d = j at hsum
      change d - b = a - c - j
      omega

theorem shiftedMixedDifferenceCorrelation_eq_sum_counts
    (j : Int) (A B C D : Finset Int) :
    shiftedMixedDifferenceCorrelation j A B C D =
      ∑ z ∈ differenceBins A C,
        differenceCount A C z * differenceCount D B (z - j) := by
  classical
  unfold shiftedMixedDifferenceCorrelation differenceBins differenceCount
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := A ×ˢ C) (t := (A ×ˢ C).image differenceValue)
    (g := differenceValue)
    (fun p hp => Finset.mem_image.mpr ⟨p, hp, rfl⟩)]
  apply Finset.sum_congr rfl
  intro z hz
  calc
    (∑ i ∈ A ×ˢ C with differenceValue i = z,
        ((D ×ˢ B).filter fun p =>
          differenceValue p = differenceValue i - j).card) =
        ∑ i ∈ A ×ˢ C, if differenceValue i = z then
          ((D ×ˢ B).filter fun p => differenceValue p = z - j).card else 0 := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hiz : differenceValue i = z
      · simp only [hiz, ↓reduceIte]
      · simp only [hiz, ↓reduceIte]
    _ = ((A ×ˢ C).filter (fun p => differenceValue p = z)).card *
        ((D ×ˢ B).filter fun p => differenceValue p = z - j).card := by
      rw [← Finset.sum_filter, Finset.sum_const, Nat.nsmul_eq_mul]

/-- Cauchy--Schwarz for a prescribed mixed integer defect. -/
theorem sq_exactMixedShiftCount_le_cross_energies
    (j : Int) (A B C D : Finset Int) :
    (ExactMixedShiftCount j A B C D : Real) ^ 2 ≤
      (Finset.addEnergy A C : Real) * (Finset.addEnergy B D : Real) := by
  classical
  let SAC := differenceBins A C
  let SDB := (differenceBins D B).image fun z => z + j
  let U := SAC ∪ SDB
  let F : Int -> Real := fun z => differenceCount A C z
  let G : Int -> Real := fun z => differenceCount D B (z - j)
  have hCorr :
      (ExactMixedShiftCount j A B C D : Real) =
        ∑ z ∈ U, F z * G z := by
    rw [← shiftedMixedDifferenceCorrelation_eq_count,
      shiftedMixedDifferenceCorrelation_eq_sum_counts]
    simp only [Nat.cast_sum, Nat.cast_mul]
    change (∑ z ∈ SAC, F z * G z) = ∑ z ∈ U, F z * G z
    apply Finset.sum_subset Finset.subset_union_left
    intro z hzU hzSAC
    have hz0 : differenceCount A C z = 0 :=
      differenceCount_eq_zero_of_not_mem_bins hzSAC
    simp only [F, hz0, Nat.cast_zero, zero_mul]
  have hFSq : ∑ z ∈ U, F z ^ 2 = (Finset.addEnergy A C : Real) := by
    rw [← differenceSquareSum_eq_addEnergy A C]
    simp only [differenceSquareSum, Nat.cast_sum, Nat.cast_pow]
    change (∑ z ∈ U, F z ^ 2) = ∑ z ∈ SAC, F z ^ 2
    symm
    apply Finset.sum_subset Finset.subset_union_left
    intro z hzU hzSAC
    have hz0 : differenceCount A C z = 0 :=
      differenceCount_eq_zero_of_not_mem_bins hzSAC
    norm_num [F, hz0]
  have hGSq : ∑ z ∈ U, G z ^ 2 = (Finset.addEnergy D B : Real) := by
    have hImage :
        ∑ z ∈ SDB, G z ^ 2 =
          ∑ z ∈ differenceBins D B,
            (differenceCount D B z : Real) ^ 2 := by
      dsimp only [SDB]
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro z hz
        simp only [G]
        rw [add_sub_cancel_right]
      · intro x hx y hy hxy
        exact add_right_cancel hxy
    calc
      ∑ z ∈ U, G z ^ 2 = ∑ z ∈ SDB, G z ^ 2 := by
        symm
        apply Finset.sum_subset Finset.subset_union_right
        intro z hzU hzSDB
        have hzNot : z - j ∉ differenceBins D B := by
          intro hz
          apply hzSDB
          exact Finset.mem_image.mpr ⟨z - j, hz, by omega⟩
        have hz0 : differenceCount D B (z - j) = 0 :=
          differenceCount_eq_zero_of_not_mem_bins hzNot
        norm_num [G, hz0]
      _ = ∑ z ∈ differenceBins D B,
          (differenceCount D B z : Real) ^ 2 := hImage
      _ = (differenceSquareSum D B : Real) := by
        simp only [differenceSquareSum, Nat.cast_sum, Nat.cast_pow]
      _ = (Finset.addEnergy D B : Real) := by
        rw [differenceSquareSum_eq_addEnergy]
  rw [hCorr]
  calc
    (∑ z ∈ U, F z * G z) ^ 2 ≤
        (∑ z ∈ U, F z ^ 2) * (∑ z ∈ U, G z ^ 2) :=
      Finset.sum_mul_sq_le_sq_mul_sq U F G
    _ = (Finset.addEnergy A C : Real) *
        (Finset.addEnergy D B : Real) := by rw [hFSq, hGSq]
    _ = (Finset.addEnergy A C : Real) *
        (Finset.addEnergy B D : Real) := by
      rw [Finset.addEnergy_comm B D]

private theorem two_mul_le_add_of_sq_le_mul
    {x a b : Real} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : x ^ 2 ≤ a * b) : 2 * x ≤ a + b := by
  nlinarith [sq_nonneg (a - b)]

/-- One exact mixed defect is controlled by the arithmetic mean of the four
self energies.  This is the no-square-root form used in exponent ledgers. -/
theorem four_mul_exactMixedShiftCount_le_sum_self_energies
    (j : Int) (A B C D : Finset Int) :
    4 * (ExactMixedShiftCount j A B C D : Real) ≤
      (Finset.addEnergy A A : Real) + (Finset.addEnergy B B : Real) +
        (Finset.addEnergy C C : Real) + (Finset.addEnergy D D : Real) := by
  have hMixed := sq_exactMixedShiftCount_le_cross_energies j A B C D
  have hAC := sq_addEnergy_le_mul_self A C
  have hBD := sq_addEnergy_le_mul_self B D
  have hMixedLinear :
      2 * (ExactMixedShiftCount j A B C D : Real) ≤
        (Finset.addEnergy A C : Real) + (Finset.addEnergy B D : Real) :=
    two_mul_le_add_of_sq_le_mul (Nat.cast_nonneg _) (Nat.cast_nonneg _) hMixed
  have hACLinear :
      2 * (Finset.addEnergy A C : Real) ≤
        (Finset.addEnergy A A : Real) + (Finset.addEnergy C C : Real) :=
    two_mul_le_add_of_sq_le_mul (Nat.cast_nonneg _) (Nat.cast_nonneg _) hAC
  have hBDLinear :
      2 * (Finset.addEnergy B D : Real) ≤
        (Finset.addEnergy B B : Real) + (Finset.addEnergy D D : Real) :=
    two_mul_le_add_of_sq_le_mul (Nat.cast_nonneg _) (Nat.cast_nonneg _) hBD
  linarith

#print axioms selfDifferenceCorrelation_eq_addEnergy
#print axioms selfDifferenceCorrelation_eq_sum_counts
#print axioms sq_addEnergy_le_mul_self
#print axioms sq_exactMixedShiftCount_le_cross_energies
#print axioms four_mul_exactMixedShiftCount_le_sum_self_energies

#print axioms differenceSquareSum_eq_addEnergy

end

end GafniTao
