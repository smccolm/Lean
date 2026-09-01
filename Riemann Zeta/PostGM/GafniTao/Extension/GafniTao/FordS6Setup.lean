import GafniTao.FordBStarCollision

/-!
# Ford Lemma 3.2: the finite `S_6` configuration

This file introduces the two halves of equation (3.6), their integral moment
map, and the exact split residue vector used in the `B*(m)` argument.  The
index equivalence records that the first `k-d` coordinates form the Jacobian
block and the last `d` coordinates are the freely fixed tail.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

def fordSplitFinEquiv {k d : ℕ} (hdk : d ≤ k) :
    Fin (k - d) ⊕ Fin d ≃ Fin k :=
  finSumFinEquiv.trans (finCongr (Nat.sub_add_cancel hdk))

def fordHeadIndex {k d : ℕ} (hdk : d ≤ k) (i : Fin (k - d)) : Fin k :=
  fordSplitFinEquiv hdk (Sum.inl i)

def fordTailIndex {k d : ℕ} (hdk : d ≤ k) (i : Fin d) : Fin k :=
  fordSplitFinEquiv hdk (Sum.inr i)

def fordSplitResidue {k d P p r : ℕ} (hdk : d ≤ k)
    (z : FordBox k P) :
    (Fin d → ZMod (p ^ r)) × (Fin (k - d) → ZMod (p ^ r)) :=
  (fun i => (fordBoxValue z (fordTailIndex hdk i) : ZMod (p ^ r)),
   fun i => (fordBoxValue z (fordHeadIndex hdk i) : ZMod (p ^ r)))

def fordJoinSplitResidue {k d p r : ℕ} (hdk : d ≤ k)
    (z : (Fin d → ZMod (p ^ r)) ×
      (Fin (k - d) → ZMod (p ^ r))) : Fin k → ZMod (p ^ r) :=
  fun i => Sum.elim z.2 z.1 ((fordSplitFinEquiv hdk).symm i)

theorem fordJoinSplitResidue_split
    {k d P p r : ℕ} (hdk : d ≤ k) (z : FordBox k P) :
    fordJoinSplitResidue hdk (fordSplitResidue (p := p) (r := r) hdk z) =
      fun i => (fordBoxValue z i : ZMod (p ^ r)) := by
  funext i
  change Sum.elim _ _ ((fordSplitFinEquiv hdk).symm i) = _
  conv_rhs =>
    rw [← (fordSplitFinEquiv hdk).apply_symm_apply i]
  generalize (fordSplitFinEquiv hdk).symm i = u
  cases u <;> rfl

def fordPolynomialSumInt
    {k d T n P : ℕ} (Φ : FordIntegerPolynomialSystem k d T)
    (z : FordBox n P) (j : Fin k) : ℤ :=
  ∑ i : Fin n, (Φ.poly j).eval (fordBoxValue z i : ℤ)

def fordPowerSumInt {n P : ℕ} (u : FordBox n P) (J : ℕ) : ℤ :=
  ∑ i : Fin n, (fordBoxValue u i : ℤ) ^ J

def fordS6Moment
    {k d T s P Q p q : ℕ} (Φ : FordIntegerPolynomialSystem k d T)
    (z : FordBox k P × FordBox s Q) : Fin k → ℤ :=
  fun j => fordPolynomialSumInt Φ z.1 j +
    ((p * q : ℕ) : ℤ) ^ ((j : ℕ) + 1) *
      fordPowerSumInt z.2 ((j : ℕ) + 1)

def FordS6Half
    (k d s P Q p r : ℕ) (hdk : d ≤ k) :=
  {z : FordBox k P × FordBox s Q //
    Function.Injective (fun i : Fin (k - d) =>
      fordPrimeReduction
        ((fordBoxValue z.1 (fordHeadIndex hdk i) : ℕ) : ZMod (p ^ r)))}

def fordS6HalfResidue
    {k d s P Q p r : ℕ} {hdk : d ≤ k}
    (z : FordS6Half k d s P Q p r hdk) :
    FordSourceBStarResidue k d p r :=
  ⟨(fordSplitResidue (p := p) (r := r) hdk z.1.1).1,
    ⟨(fordSplitResidue (p := p) (r := r) hdk z.1.1).2, z.2⟩⟩

def fordS6FineMap
    {k d T s P Q p q r : ℕ} (Φ : FordIntegerPolynomialSystem k d T)
    {hdk : d ≤ k} :
    FordS6Half k d s P Q p r hdk →
      (Fin k → ℤ) × FordSourceBStarResidue k d p r :=
  fun z => (fordS6Moment (p := p) (q := q) Φ z.1, fordS6HalfResidue z)

@[simp] theorem fordS6FineMap_moment
    {k d T s P Q p q r : ℕ} (Φ : FordIntegerPolynomialSystem k d T)
    {hdk : d ≤ k} (z : FordS6Half k d s P Q p r hdk) :
    (fordS6FineMap (p := p) (q := q) Φ z).1 =
      fordS6Moment (p := p) (q := q) Φ z.1 := rfl

@[simp] theorem fordS6FineMap_residue
    {k d T s P Q p q r : ℕ} (Φ : FordIntegerPolynomialSystem k d T)
    {hdk : d ≤ k} (z : FordS6Half k d s P Q p r hdk) :
    (fordS6FineMap (p := p) (q := q) Φ z).2 =
      fordS6HalfResidue z := rfl

#print axioms fordJoinSplitResidue_split
#print axioms fordS6FineMap_moment
#print axioms fordS6FineMap_residue

end

end GafniTao
