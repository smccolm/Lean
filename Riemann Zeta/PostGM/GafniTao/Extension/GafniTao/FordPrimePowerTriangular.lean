import GafniTao.FordPrimePowerNewton

/-!
# Ford Lemma 2.4: nonsingular triangular prime-power fibres

For the polynomial systems produced by Ford's Lemma 3.1, the equations are
triangular in the power sums and the Jacobian condition says that the chosen
coordinates remain distinct modulo `p`.  This file combines those two facts
with the prime-power Newton theorem to obtain the exact product-of-degrees
bound `n!` used in equation (3.7).
-/

open Finset Polynomial
open scoped BigOperators

namespace GafniTao

noncomputable section

theorem ford_powerSum_eq_of_evalSum_eq_of_isUnit
    {m n J : ℕ} (f : (ZMod m)[X]) (x y : Fin n → ZMod m)
    (hJ : 0 < J) (hdegree : f.natDegree = J)
    (hlc : IsUnit f.leadingCoeff)
    (heval : fordPolynomialEvalSum f x = fordPolynomialEvalSum f y)
    (hlower : ∀ r, r < J → fordPowerSum x r = fordPowerSum y r) :
    fordPowerSum x J = fordPowerSum y J := by
  have heraseDegree : f.eraseLead.natDegree < J := by
    rw [← hdegree]
    exact f.eraseLead_natDegree_le.trans_lt
      (Nat.sub_lt (by simpa [hdegree] using hJ) zero_lt_one)
  have herase : fordPolynomialEvalSum f.eraseLead x =
      fordPolynomialEvalSum f.eraseLead y :=
    fordPolynomialEvalSum_eq_of_powerSums_eq f.eraseLead x y
      (fun r hr => hlower r (hr.trans_lt heraseDegree))
  have hdecomp := f.eraseLead_add_C_mul_X_pow
  have hsplit (z : Fin n → ZMod m) :
      fordPolynomialEvalSum f z =
        fordPolynomialEvalSum f.eraseLead z +
          f.leadingCoeff * fordPowerSum z J := by
    calc
      fordPolynomialEvalSum f z =
          fordPolynomialEvalSum
            (f.eraseLead + C f.leadingCoeff * X ^ f.natDegree) z :=
        congrArg (fun g => fordPolynomialEvalSum g z) hdecomp.symm
      _ = fordPolynomialEvalSum f.eraseLead z +
          fordPolynomialEvalSum (C f.leadingCoeff * X ^ f.natDegree) z := by
        unfold fordPolynomialEvalSum
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        rw [eval_add]
      _ = fordPolynomialEvalSum f.eraseLead z +
          f.leadingCoeff * fordPowerSum z J := by
        rw [fordPolynomialEvalSum_C_mul_X_pow, hdegree]
  rw [hsplit x, hsplit y, herase] at heval
  exact hlc.mul_left_cancel (add_left_cancel heval)

def FordPrimePowerTriangularPolynomialSystem (p s n : ℕ) :=
  {f : Fin n → (ZMod (p ^ s))[X] //
    ∀ j : Fin n, (f j).natDegree = (j : ℕ) + 1 ∧
      IsUnit (f j).leadingCoeff}

def FordPrimePowerTriangularFiber {p s n : ℕ}
    (f : FordPrimePowerTriangularPolynomialSystem p s n)
    (v : Fin n → ZMod (p ^ s)) :=
  {x : Fin n → ZMod (p ^ s) //
    ∀ j, fordPolynomialEvalSum (f.1 j) x = v j}

def FordPrimePowerNonsingularTriangularFiber {p s n : ℕ}
    (f : FordPrimePowerTriangularPolynomialSystem p s n)
    (v : Fin n → ZMod (p ^ s)) :=
  {x : FordPrimePowerTriangularFiber f v //
    Function.Injective (fun i => fordPrimeReduction (x.1 i))}

theorem fordPrimePowerTriangularFiber_powerSums_eq
    {p s n : ℕ} (f : FordPrimePowerTriangularPolynomialSystem p s n)
    {v : Fin n → ZMod (p ^ s)}
    (x y : FordPrimePowerTriangularFiber f v) :
    ∀ r, 1 ≤ r → r ≤ n →
      fordPowerSum x.1 r = fordPowerSum y.1 r := by
  intro r hr1 hrn
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_one.mpr hr1
  have hjn : j < n := by omega
  have hAll : ∀ j, j < n →
      fordPowerSum x.1 (j + 1) = fordPowerSum y.1 (j + 1) := by
    intro j
    induction j using Nat.strong_induction_on with
    | h j ih =>
      intro hjn'
      let ji : Fin n := ⟨j, hjn'⟩
      apply ford_powerSum_eq_of_evalSum_eq_of_isUnit
        (f.1 ji) x.1 y.1 (by omega)
      · exact (f.2 ji).1
      · exact (f.2 ji).2
      · exact (x.2 ji).trans (y.2 ji).symm
      · intro q hq
        by_cases hq0 : q = 0
        · subst q
          simp [fordPowerSum]
        · obtain ⟨a, rfl⟩ :=
            Nat.exists_eq_add_one.mpr (Nat.pos_of_ne_zero hq0)
          exact ih a (by omega) (by omega)
  exact hAll j hjn

theorem ford_primePowerNonsingularTriangularFiber_card_le_factorial
    {p s n : ℕ} (hp : Nat.Prime p) (hs : 0 < s) (hnp : n < p)
    (f : FordPrimePowerTriangularPolynomialSystem p s n)
    (v : Fin n → ZMod (p ^ s)) :
    Nat.card (FordPrimePowerNonsingularTriangularFiber f v) ≤ n.factorial := by
  classical
  letI : NeZero (p ^ s) := ⟨pow_ne_zero s hp.ne_zero⟩
  by_cases hne : Nonempty (FordPrimePowerNonsingularTriangularFiber f v)
  · let x₀ : FordPrimePowerNonsingularTriangularFiber f v := Classical.choice hne
    let embed : FordPrimePowerNonsingularTriangularFiber f v →
        FordPrimePowerPowerSumFiber p s n x₀.1.1 := fun x =>
      ⟨x.1.1, fordPrimePowerTriangularFiber_powerSums_eq f x.1 x₀.1⟩
    have hinj : Function.Injective embed := by
      intro x y h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg
        (fun z : FordPrimePowerPowerSumFiber p s n x₀.1.1 => z.1) h
    letI : Finite (FordPrimePowerPowerSumFiber p s n x₀.1.1) :=
      Finite.of_injective Subtype.val Subtype.val_injective
    exact (Nat.card_le_card_of_injective embed hinj).trans
      (ford_primePowerPowerSumFiber_card_le_factorial
        hp hs hnp x₀.1.1 x₀.2)
  · haveI : IsEmpty (FordPrimePowerNonsingularTriangularFiber f v) :=
      not_nonempty_iff.mp hne
    rw [Nat.card_eq_zero.mpr (Or.inl inferInstance)]
    exact Nat.zero_le _

#print axioms ford_powerSum_eq_of_evalSum_eq_of_isUnit
#print axioms fordPrimePowerTriangularFiber_powerSums_eq
#print axioms ford_primePowerNonsingularTriangularFiber_card_le_factorial

end

end GafniTao
