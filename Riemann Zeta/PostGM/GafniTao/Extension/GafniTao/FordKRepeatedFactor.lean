import GafniTao.FordKRepeatedCover

/-!
# Ford Lemma 3.2: factorization at a fixed repeated pair

For `i<j`, a polynomial tuple with `z_i=z_j` is parameterized by its common
value and the remaining `k-2` coordinates.  This is the exact finite origin
of Ford's factor `F(2α)F(α)^(k-2)`.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

def fordAwayFinset {k : ℕ} (ij : FordIndexPair k) : Finset (Fin k) :=
  (Finset.univ.erase ij.1.1).erase ij.1.2

abbrev FordAwayIndex {k : ℕ} (ij : FordIndexPair k) :=
  {l : Fin k // l ∈ fordAwayFinset ij}

abbrev FordAwayBox {k P : ℕ} (ij : FordIndexPair k) :=
  FordAwayIndex ij → Fin P

abbrev FordRepeatedPolynomialBoxAt (P : ℕ) {k : ℕ}
    (ij : FordIndexPair k) :=
  {z : FordBox k P // z ij.1.1 = z ij.1.2}

theorem card_fordAwayIndex {k : ℕ} (ij : FordIndexPair k) :
    Fintype.card (FordAwayIndex ij) = k - 2 := by
  rw [Fintype.card_coe]
  unfold fordAwayFinset
  have hji : ij.1.2 ∈ (Finset.univ.erase ij.1.1) := by
    simp [ne_of_gt ij.2]
  rw [Finset.card_erase_of_mem hji]
  simp
  omega

def fordAssembleRepeatedBox
    {k P : ℕ} (ij : FordIndexPair k)
    (a : Fin P) (r : FordAwayBox (P := P) ij) : FordBox k P :=
  fun l ↦ if h : l ∈ fordAwayFinset ij then r ⟨l, h⟩ else a

theorem fordAssembleRepeatedBox_first
    {k P : ℕ} (ij : FordIndexPair k)
    (a : Fin P) (r : FordAwayBox (P := P) ij) :
    fordAssembleRepeatedBox ij a r ij.1.1 = a := by
  simp [fordAssembleRepeatedBox, fordAwayFinset]

theorem fordAssembleRepeatedBox_second
    {k P : ℕ} (ij : FordIndexPair k)
    (a : Fin P) (r : FordAwayBox (P := P) ij) :
    fordAssembleRepeatedBox ij a r ij.1.2 = a := by
  simp [fordAssembleRepeatedBox, fordAwayFinset]

def fordRepeatedBoxParamEquiv
    {k P : ℕ} (ij : FordIndexPair k) :
    (Fin P × FordAwayBox (P := P) ij) ≃ FordRepeatedPolynomialBoxAt P ij where
  toFun u := ⟨fordAssembleRepeatedBox ij u.1 u.2, by
    rw [fordAssembleRepeatedBox_first, fordAssembleRepeatedBox_second]⟩
  invFun z := (z.1 ij.1.1, fun l ↦ z.1 l.1)
  left_inv u := by
    apply Prod.ext
    · simp [fordAssembleRepeatedBox_first]
    · funext l
      simp [fordAssembleRepeatedBox, l.2]
  right_inv z := by
    apply Subtype.ext
    funext l
    by_cases hl : l ∈ fordAwayFinset ij
    · simp [fordAssembleRepeatedBox, hl]
    · have hor : l = ij.1.1 ∨ l = ij.1.2 := by
        simp only [fordAwayFinset, Finset.mem_erase, Finset.mem_univ,
          and_true, not_and_or, not_not] at hl
        exact hl.elim Or.inr Or.inl
      rcases hor with rfl | rfl
      · simp [fordAssembleRepeatedBox_first]
      · change fordAssembleRepeatedBox ij (z.1 ij.1.1)
          (fun l ↦ z.1 l.1) ij.1.2 = z.1 ij.1.2
        rw [fordAssembleRepeatedBox_second, z.2]

def fordRepeatedPolynomialMoment
    {k d T P : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (ij : FordIndexPair k) (u : Fin P × FordAwayBox (P := P) ij) :
    Fin k → ℤ :=
  (2 : ℤ) • fordPolynomialSingleMoment Ψ u.1 +
    fordFamilyMoment (fordPolynomialSingleMoment Ψ) u.2

theorem fordPolynomialMoment_assemble_eq
    {k d T P : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (ij : FordIndexPair k) (a : Fin P) (r : FordAwayBox (P := P) ij) :
    fordPolynomialMoment Ψ (fordAssembleRepeatedBox ij a r) =
      fordRepeatedPolynomialMoment Ψ ij (a, r) := by
  funext t
  unfold fordPolynomialMoment fordPolynomialSumInt
    fordRepeatedPolynomialMoment fordFamilyMoment fordPolynomialSingleMoment
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hi : ij.1.1 ∈ (Finset.univ : Finset (Fin k)) := Finset.mem_univ _
  have hj : ij.1.2 ∈ (Finset.univ.erase ij.1.1) := by
    simp [ne_of_gt ij.2]
  have hiAway : ij.1.1 ∉ fordAwayFinset ij := by
    simp [fordAwayFinset]
  have hjAway : ij.1.2 ∉ fordAwayFinset ij := by
    simp [fordAwayFinset]
  calc
    ∑ l : Fin k,
        (Ψ.poly t).eval
          (fordBoxValue (fordAssembleRepeatedBox ij a r) l : ℤ) =
        (∑ l ∈ fordAwayFinset ij,
          (Ψ.poly t).eval
            (fordBoxValue (fordAssembleRepeatedBox ij a r) l : ℤ)) +
          (Ψ.poly t).eval
            (fordBoxValue (fordAssembleRepeatedBox ij a r) ij.1.2 : ℤ) +
          (Ψ.poly t).eval
            (fordBoxValue (fordAssembleRepeatedBox ij a r) ij.1.1 : ℤ) := by
      rw [← Finset.sum_erase_add _ _ hi, ← Finset.sum_erase_add _ _ hj]
      rfl
    _ = ∑ l : FordAwayIndex ij,
          (Ψ.poly t).eval (((r l : ℕ) + 1 : ℕ) : ℤ) +
        (Ψ.poly t).eval (((a : ℕ) + 1 : ℕ) : ℤ) +
        (Ψ.poly t).eval (((a : ℕ) + 1 : ℕ) : ℤ) := by
      rw [← Finset.sum_attach]
      simp [fordAssembleRepeatedBox, fordBoxValue, hiAway, hjAway]
    _ = 2 * (Ψ.poly t).eval (((a : ℕ) + 1 : ℕ) : ℤ) +
        ∑ l : FordAwayIndex ij,
          (Ψ.poly t).eval (((r l : ℕ) + 1 : ℕ) : ℤ) := by ring

def fordPolynomialDoubleWeylSum
    {k d T P : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (a : UnitAddTorus (Fin k)) : ℂ :=
  fordCharacterSum
    (fun x : Fin P ↦ (2 : ℤ) • fordPolynomialSingleMoment Ψ x) a

theorem fordRepeatedPolynomialCharacterSum_eq
    {k d T P : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (ij : FordIndexPair k) (a : UnitAddTorus (Fin k)) :
    fordCharacterSum
        (fordRepeatedPolynomialMoment (P := P) Ψ ij :
          (Fin P × FordAwayBox (P := P) ij) → Fin k → ℤ) a =
      fordPolynomialDoubleWeylSum (P := P) Ψ a *
        fordPolynomialFullWeylSum (P := P) Ψ a ^ (k - 2) := by
  classical
  unfold fordCharacterSum fordRepeatedPolynomialMoment
  simp_rw [UnitAddTorus.mFourier_add]
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]
  unfold fordPolynomialDoubleWeylSum fordPolynomialFullWeylSum
  congr 1
  rw [← card_fordAwayIndex ij]
  exact fordCharacterSum_familyMoment_eq_pow_card
    (fordPolynomialSingleMoment (P := P) Ψ) a

#print axioms fordRepeatedBoxParamEquiv
#print axioms fordPolynomialMoment_assemble_eq
#print axioms fordRepeatedPolynomialCharacterSum_eq

end

end GafniTao
