import GafniTao.FordIntegerPolynomialSystem

/-!
# Ford equations (3.1) and (3.2)

These are finite, source-facing solution counts.  A coordinate in `Fin P` is
interpreted as the integer in `[1,P]` obtained by adding one.
-/

open Finset Polynomial
open scoped BigOperators

namespace GafniTao

noncomputable section

abbrev FordBox (n P : ℕ) := Fin n → Fin P

@[simp] def fordBoxValue {n P : ℕ} (x : FordBox n P) (i : Fin n) : ℕ :=
  (x i : ℕ) + 1

theorem fordBoxValue_mem_Icc {n P : ℕ} (x : FordBox n P) (i : Fin n) :
    fordBoxValue x i ∈ Finset.Icc 1 P := by
  simp [fordBoxValue]

abbrev FordKVariables (k s P Q : ℕ) :=
  (FordBox k P × FordBox k P) × (FordBox s Q × FordBox s Q)

abbrev FordLVariables (k s P Q : ℕ) := FordKVariables k s P Q

def fordPolynomialDifference
    {k d T : ℕ} (ψ : FordIntegerPolynomialSystem k d T)
    {n P : ℕ} (z w : FordBox n P) (j : Fin k) : ℤ :=
  ∑ i : Fin n, (
    (ψ.poly j).eval (fordBoxValue z i : ℤ) -
      (ψ.poly j).eval (fordBoxValue w i : ℤ))

def fordPowerDifference
    {n P : ℕ} (x y : FordBox n P) (J : ℕ) : ℤ :=
  ∑ i : Fin n, ((fordBoxValue x i : ℤ) ^ J -
    (fordBoxValue y i : ℤ) ^ J)

/-- Ford equation (3.1), with source degree `J=j+1`. -/
def FordKEquation
    {k d T : ℕ} (ψ : FordIntegerPolynomialSystem k d T)
    {s P Q : ℕ} (q : ℕ) (v : FordKVariables k s P Q) : Prop :=
  ∀ j : Fin k,
    fordPolynomialDifference ψ v.1.1 v.1.2 j +
      (q : ℤ) ^ ((j : ℕ) + 1) *
        fordPowerDifference v.2.1 v.2.2 ((j : ℕ) + 1) = 0

/-- The exact finite solution count `K_s(P,Q;Ψ;q)` in (3.1). -/
def fordKCount
    {k d T : ℕ} (ψ : FordIntegerPolynomialSystem k d T)
    (s P Q q : ℕ) : ℕ :=
  Fintype.card {v : FordKVariables k s P Q // FordKEquation ψ q v}

def FordLCongruence
    {k s P Q : ℕ} (p r : ℕ) (v : FordLVariables k s P Q) : Prop :=
  ∀ i : Fin k, Nat.ModEq (p ^ r)
    (fordBoxValue v.1.1 i) (fordBoxValue v.1.2 i)

/-- Ford equation (3.2), including `z_i ≡ w_i (mod p^r)`. -/
def FordLEquation
    {k d T : ℕ} (ψ : FordIntegerPolynomialSystem k d T)
    {s P Q : ℕ} (p q r : ℕ) (v : FordLVariables k s P Q) : Prop :=
  FordLCongruence p r v ∧ ∀ j : Fin k,
    fordPolynomialDifference ψ v.1.1 v.1.2 j +
      ((p * q : ℕ) : ℤ) ^ ((j : ℕ) + 1) *
        fordPowerDifference v.2.1 v.2.2 ((j : ℕ) + 1) = 0

/-- The exact finite solution count `L_s(P,Q;Ψ;p,q,r)` in (3.2). -/
def fordLCount
    {k d T : ℕ} (ψ : FordIntegerPolynomialSystem k d T)
    (s P Q p q r : ℕ) : ℕ :=
  Fintype.card {v : FordLVariables k s P Q // FordLEquation ψ p q r v}

@[simp] theorem fintype_card_fordBox (n P : ℕ) :
    Fintype.card (FordBox n P) = P ^ n := by
  simp [FordBox]

@[simp] theorem fintype_card_fordKVariables (k s P Q : ℕ) :
    Fintype.card (FordKVariables k s P Q) = P ^ (2 * k) * Q ^ (2 * s) := by
  simp only [FordKVariables, Fintype.card_prod, fintype_card_fordBox]
  rw [show 2 * k = k + k by omega, show 2 * s = s + s by omega,
    pow_add, pow_add]

/-- The trivial estimate used at the start of Ford Lemma 3.2. -/
theorem fordKCount_le_trivial
    {k d T : ℕ} (ψ : FordIntegerPolynomialSystem k d T)
    (s P Q q : ℕ) :
    fordKCount ψ s P Q q ≤ P ^ (2 * k) * Q ^ (2 * s) := by
  unfold fordKCount
  calc
    Fintype.card {v : FordKVariables k s P Q // FordKEquation ψ q v} ≤
        Fintype.card (FordKVariables k s P Q) :=
      Fintype.card_subtype_le (fun v : FordKVariables k s P Q =>
        FordKEquation ψ q v)
    _ = P ^ (2 * k) * Q ^ (2 * s) := fintype_card_fordKVariables k s P Q

theorem fordLCount_le_trivial
    {k d T : ℕ} (ψ : FordIntegerPolynomialSystem k d T)
    (s P Q p q r : ℕ) :
    fordLCount ψ s P Q p q r ≤ P ^ (2 * k) * Q ^ (2 * s) := by
  unfold fordLCount
  calc
    Fintype.card {v : FordLVariables k s P Q // FordLEquation ψ p q r v} ≤
        Fintype.card (FordLVariables k s P Q) :=
      Fintype.card_subtype_le (fun v : FordLVariables k s P Q =>
        FordLEquation ψ p q r v)
    _ = P ^ (2 * k) * Q ^ (2 * s) := fintype_card_fordKVariables k s P Q

#print axioms fordBoxValue_mem_Icc
#print axioms fordKCount_le_trivial
#print axioms fordLCount_le_trivial

end

end GafniTao
