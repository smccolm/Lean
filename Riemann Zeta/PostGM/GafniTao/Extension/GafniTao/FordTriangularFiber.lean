import GafniTao.FordBinomialTransform
import Mathlib.Algebra.Polynomial.EraseLead

/-!
# Ford Lemma 2.4, structured residue fibre: triangular reduction

The nonsingular congruence system used in Lemma 3.2 is triangular in the
power sums.  This file proves the residue-field part of that assertion: equal
sums of degree `1,...,n` polynomials with nonzero successive leading
coefficients force equality of all first `n` power sums.  Combined with the
Newton fibre theorem, this gives the exact `n!` residue-class bound.  The
higher-prime-power lifting is kept as the next, separate obligation.
-/

open Finset Polynomial
open scoped BigOperators

namespace GafniTao

noncomputable section

def fordPolynomialEvalSum {p n : ℕ} (f : (ZMod p)[X])
    (x : Fin n → ZMod p) : ZMod p :=
  ∑ i, f.eval (x i)

theorem fordPolynomialEvalSum_eq_coeff_powerSums
    {p n : ℕ} (f : (ZMod p)[X]) (x : Fin n → ZMod p) :
    fordPolynomialEvalSum f x =
      ∑ r ∈ Finset.range (f.natDegree + 1),
        f.coeff r * fordPowerSum x r := by
  unfold fordPolynomialEvalSum fordPowerSum
  simp_rw [Polynomial.eval_eq_sum_range, Finset.mul_sum]
  exact Finset.sum_comm.trans rfl

theorem fordPolynomialEvalSum_eq_of_powerSums_eq
    {p n : ℕ} (f : (ZMod p)[X]) (x y : Fin n → ZMod p)
    (hpow : ∀ r, r ≤ f.natDegree → fordPowerSum x r = fordPowerSum y r) :
    fordPolynomialEvalSum f x = fordPolynomialEvalSum f y := by
  rw [fordPolynomialEvalSum_eq_coeff_powerSums,
    fordPolynomialEvalSum_eq_coeff_powerSums]
  apply Finset.sum_congr rfl
  intro r hr
  rw [hpow r (by simpa using Finset.mem_range.mp hr)]

theorem fordPolynomialEvalSum_C_mul_X_pow
    {p n J : ℕ} (a : ZMod p) (x : Fin n → ZMod p) :
    fordPolynomialEvalSum (C a * X ^ J) x =
      a * fordPowerSum x J := by
  unfold fordPolynomialEvalSum fordPowerSum
  simp [Finset.mul_sum]

theorem ford_powerSum_eq_of_evalSum_eq
    {p n J : ℕ} (hp : Nat.Prime p) (f : (ZMod p)[X])
    (x y : Fin n → ZMod p) (hJ : 0 < J)
    (hdegree : f.natDegree = J) (hlc : f.leadingCoeff ≠ 0)
    (heval : fordPolynomialEvalSum f x = fordPolynomialEvalSum f y)
    (hlower : ∀ r, r < J → fordPowerSum x r = fordPowerSum y r) :
    fordPowerSum x J = fordPowerSum y J := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  have heraseDegree : f.eraseLead.natDegree < J := by
    rw [← hdegree]
    exact f.eraseLead_natDegree_le.trans_lt
      (Nat.sub_lt (by simpa [hdegree] using hJ) zero_lt_one)
  have herase : fordPolynomialEvalSum f.eraseLead x =
      fordPolynomialEvalSum f.eraseLead y :=
    fordPolynomialEvalSum_eq_of_powerSums_eq f.eraseLead x y
      (fun r hr => hlower r (hr.trans_lt heraseDegree))
  have hdecomp := f.eraseLead_add_C_mul_X_pow
  have hx : fordPolynomialEvalSum f x =
      fordPolynomialEvalSum f.eraseLead x +
        f.leadingCoeff * fordPowerSum x J := by
    calc
      fordPolynomialEvalSum f x =
          fordPolynomialEvalSum
            (f.eraseLead + C f.leadingCoeff * X ^ f.natDegree) x :=
        congrArg (fun g => fordPolynomialEvalSum g x) hdecomp.symm
      _ = fordPolynomialEvalSum f.eraseLead x +
          fordPolynomialEvalSum (C f.leadingCoeff * X ^ f.natDegree) x := by
        unfold fordPolynomialEvalSum
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        rw [eval_add]
      _ = fordPolynomialEvalSum f.eraseLead x +
          f.leadingCoeff * fordPowerSum x J := by
        rw [fordPolynomialEvalSum_C_mul_X_pow, hdegree]
  have hy : fordPolynomialEvalSum f y =
      fordPolynomialEvalSum f.eraseLead y +
        f.leadingCoeff * fordPowerSum y J := by
    calc
      fordPolynomialEvalSum f y =
          fordPolynomialEvalSum
            (f.eraseLead + C f.leadingCoeff * X ^ f.natDegree) y :=
        congrArg (fun g => fordPolynomialEvalSum g y) hdecomp.symm
      _ = fordPolynomialEvalSum f.eraseLead y +
          fordPolynomialEvalSum (C f.leadingCoeff * X ^ f.natDegree) y := by
        unfold fordPolynomialEvalSum
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        rw [eval_add]
      _ = fordPolynomialEvalSum f.eraseLead y +
          f.leadingCoeff * fordPowerSum y J := by
        rw [fordPolynomialEvalSum_C_mul_X_pow, hdegree]
  rw [hx, hy, herase] at heval
  exact mul_left_cancel₀ hlc (add_left_cancel heval)

def FordTriangularPolynomialSystem (p n : ℕ) :=
  {f : Fin n → (ZMod p)[X] //
    ∀ j : Fin n, (f j).natDegree = (j : ℕ) + 1 ∧
      (f j).leadingCoeff ≠ 0}

def FordTriangularFiber {p n : ℕ}
    (f : FordTriangularPolynomialSystem p n) (v : Fin n → ZMod p) :=
  {x : Fin n → ZMod p // ∀ j, fordPolynomialEvalSum (f.1 j) x = v j}

theorem fordTriangularFiber_powerSums_eq
    {p n : ℕ} (hp : Nat.Prime p) (f : FordTriangularPolynomialSystem p n)
    {v : Fin n → ZMod p} (x y : FordTriangularFiber f v) :
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
      apply ford_powerSum_eq_of_evalSum_eq hp (f.1 ji) x.1 y.1 (by omega)
      · exact (f.2 ji).1
      · exact (f.2 ji).2
      · exact (x.2 ji).trans (y.2 ji).symm
      · intro q hq
        by_cases hq0 : q = 0
        · subst q
          simp [fordPowerSum]
        · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one.mpr (Nat.pos_of_ne_zero hq0)
          exact ih m (by omega) (by omega)
  exact hAll j hjn

theorem fordTriangularFiber_card_le_factorial
    {p n : ℕ} (hp : Nat.Prime p) (hnp : n < p)
    (f : FordTriangularPolynomialSystem p n) (v : Fin n → ZMod p) :
    Nat.card (FordTriangularFiber f v) ≤ n.factorial := by
  classical
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  by_cases hne : Nonempty (FordTriangularFiber f v)
  · let x₀ : FordTriangularFiber f v := Classical.choice hne
    let embed : FordTriangularFiber f v → FordPowerSumFiber p n x₀.1 :=
      fun x => ⟨x.1, fordTriangularFiber_powerSums_eq hp f x x₀⟩
    have hinj : Function.Injective embed := by
      intro x y h
      apply Subtype.ext
      exact congrArg (fun z : FordPowerSumFiber p n x₀.1 => z.1) h
    letI : Finite (FordPowerSumFiber p n x₀.1) :=
      Finite.of_injective Subtype.val Subtype.val_injective
    exact (Nat.card_le_card_of_injective embed hinj).trans
      (ford_powerSumFiber_card_le_factorial hp hnp x₀.1)
  · haveI : IsEmpty (FordTriangularFiber f v) := not_nonempty_iff.mp hne
    rw [Nat.card_eq_zero.mpr (Or.inl inferInstance)]
    exact Nat.zero_le _

#print axioms fordPolynomialEvalSum_eq_coeff_powerSums
#print axioms ford_powerSum_eq_of_evalSum_eq
#print axioms fordTriangularFiber_powerSums_eq
#print axioms fordTriangularFiber_card_le_factorial

end

end GafniTao
