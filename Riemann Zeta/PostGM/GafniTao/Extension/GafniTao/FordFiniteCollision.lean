import GafniTao.FordBStarCongruence
import Mathlib.Algebra.Order.Chebyshev

/-!
# Finite collision energy under a bounded coarsening

This is the exact finite Cauchy--Schwarz mechanism used after Ford (3.6).
If every fibre of a residue signature has at most `B` elements, then the
number of equal-signature pairs is at most `B` times the number of
equal-residue pairs.  The theorem is stated for arbitrary finite maps so its
later source specialization has no analytic or cardinality assumptions hidden
inside it.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

def FordMapFiber {A B : Type*} (f : A → B) (b : B) :=
  {a : A // f a = b}

noncomputable instance fordMapFiberFintype
    {A B : Type*} [Fintype A] (f : A → B) (b : B) :
    Fintype (FordMapFiber f b) := by
  letI : Finite (FordMapFiber f b) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

def FordCollisionPairs {A B : Type*} (f : A → B) :=
  {z : A × A // f z.1 = f z.2}

def fordCollisionPairsEquivSigma
    {A B : Type*} (f : A → B) :
    FordCollisionPairs f ≃ Σ b : B, FordMapFiber f b × FordMapFiber f b where
  toFun z := ⟨f z.1.1, ⟨z.1.1, rfl⟩, ⟨z.1.2, z.2.symm⟩⟩
  invFun z := ⟨(z.2.1.1, z.2.2.1), z.2.1.2.trans z.2.2.2.symm⟩
  left_inv z := by
    rcases z with ⟨⟨x, y⟩, h⟩
    rfl
  right_inv z := by
    rcases z with ⟨b, ⟨x, hx⟩, ⟨y, hy⟩⟩
    subst b
    rfl

def fordCompFiberEquivSigma
    {X A M : Type*} (g : X → A) (h : A → M) (m : M) :
    FordMapFiber (h ∘ g) m ≃
      Σ a : FordMapFiber h m, FordMapFiber g a.1 where
  toFun x := ⟨⟨g x.1, x.2⟩, x.1, rfl⟩
  invFun x := ⟨x.2.1, by
    change h (g x.2.1) = m
    rw [x.2.2]
    exact x.1.2⟩
  left_inv x := by
    rcases x with ⟨x, hx⟩
    rfl
  right_inv x := by
    rcases x with ⟨⟨a, ha⟩, x, hx⟩
    exact Sigma.ext (Subtype.ext hx) (by cases hx; rfl)

theorem fordCollisionPairs_card_eq_sum_sq
    {A B : Type*} [Fintype A] [Fintype B] (f : A → B) :
    Nat.card (FordCollisionPairs f) =
      ∑ b : B, Nat.card (FordMapFiber f b) ^ 2 := by
  classical
  letI := Classical.decEq B
  letI (b : B) : Finite (FordMapFiber f b) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  rw [Nat.card_congr (fordCollisionPairsEquivSigma f), Nat.card_sigma]
  apply Finset.sum_congr rfl
  intro b _
  rw [Nat.card_prod, pow_two]

theorem fordCompFiber_card_eq_sum
    {X A M : Type*} [Fintype X] [Fintype A] [Fintype M]
    (g : X → A) (h : A → M) (m : M) :
    Nat.card (FordMapFiber (h ∘ g) m) =
      ∑ a : FordMapFiber h m, Nat.card (FordMapFiber g a.1) := by
  classical
  letI := Classical.decEq A
  letI := Classical.decEq M
  rw [Nat.card_congr (fordCompFiberEquivSigma g h m), Nat.card_sigma]

/-- Finite Cauchy--Schwarz for a map `g` followed by a coarsening `h`. -/
theorem ford_collision_comp_le
    {X A M : Type*} [Fintype X] [Fintype A] [Fintype M]
    (g : X → A) (h : A → M) (B : ℕ)
    (hB : ∀ m : M, Nat.card (FordMapFiber h m) ≤ B) :
    Nat.card (FordCollisionPairs (h ∘ g)) ≤
      B * Nat.card (FordCollisionPairs g) := by
  classical
  letI := Classical.decEq A
  letI := Classical.decEq M
  rw [fordCollisionPairs_card_eq_sum_sq,
    fordCollisionPairs_card_eq_sum_sq]
  simp_rw [fordCompFiber_card_eq_sum]
  calc
    (∑ m : M, (∑ a : FordMapFiber h m,
        Nat.card (FordMapFiber g a.1)) ^ 2) ≤
        ∑ m : M, B * ∑ a : FordMapFiber h m,
          Nat.card (FordMapFiber g a.1) ^ 2 := by
      apply Finset.sum_le_sum
      intro m _
      have hcard : (Finset.univ : Finset (FordMapFiber h m)).card ≤ B := by
        rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
        exact hB m
      exact (sq_sum_le_card_mul_sum_sq
          (s := Finset.univ)
          (f := fun a : FordMapFiber h m =>
            Nat.card (FordMapFiber g a.1))).trans
        (Nat.mul_le_mul_right _ hcard)
    _ = B * ∑ a : A, Nat.card (FordMapFiber g a) ^ 2 := by
      rw [← Finset.mul_sum]
      congr 1
      symm
      rw [← Fintype.sum_sigma
        (fun z : Σ m : M, FordMapFiber h m =>
          Nat.card (FordMapFiber g z.2.1) ^ 2)]
      exact @Fintype.sum_equiv A (Σ m : M, FordMapFiber h m) ℕ
        inferInstance
        (@Sigma.instFintype M (fun m => FordMapFiber h m)
          (fun m => fordMapFiberFintype h m) inferInstance)
        inferInstance
        (fordTypeEquivSigmaFiber h)
        (fun a : A => Nat.card (FordMapFiber g a) ^ 2)
        (fun z : Σ m : M, FordMapFiber h m =>
          Nat.card (FordMapFiber g z.2.1) ^ 2)
        (fun a => rfl)

#print axioms fordCollisionPairs_card_eq_sum_sq
#print axioms fordCompFiber_card_eq_sum
#print axioms ford_collision_comp_le

end

end GafniTao
