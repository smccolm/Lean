import GafniTao.FordS4Interior
import GafniTao.FordBinomialTransform

/-!
# Ford equation (3.6): the triangular moment transform

This file isolates the unitriangular transform on moment vectors which is
implicit between Ford's equations (3.5) and (3.6).  Its translation parameter
is an integer; the source application will use the scaled residue translation
`q * a`, not the unscaled residue representative `a`.
-/

open Finset Polynomial
open scoped BigOperators

namespace GafniTao

noncomputable section

def fordMomentBinomialLower {k : ℕ} (a : ℤ) (M : Fin k → ℤ)
    (j : Fin k) : ℤ :=
  ∑ l : Fin (j : ℕ),
    (((j : ℕ) + 1).choose ((l : ℕ) + 1) : ℤ) *
      a ^ ((j : ℕ) + 1 - ((l : ℕ) + 1)) *
      M (Fin.castLE j.isLt.le l)

def fordMomentBinomialTransform {k : ℕ} (a : ℤ)
    (M : Fin k → ℤ) : Fin k → ℤ :=
  fun j ↦ M j + fordMomentBinomialLower a M j

def fordMomentBinomialTransformHom {k : ℕ} (a : ℤ) :
    (Fin k → ℤ) →+ (Fin k → ℤ) where
  toFun := fordMomentBinomialTransform a
  map_zero' := by
    funext j
    simp [fordMomentBinomialTransform, fordMomentBinomialLower]
  map_add' M N := by
    funext j
    simp only [fordMomentBinomialTransform, fordMomentBinomialLower,
      Pi.add_apply, mul_add, Finset.sum_add_distrib]
    ring

@[simp] theorem fordMomentBinomialTransformHom_apply {k : ℕ} (a : ℤ)
    (M : Fin k → ℤ) :
    fordMomentBinomialTransformHom a M = fordMomentBinomialTransform a M := rfl

theorem fordMomentBinomialTransform_injective {k : ℕ} (a : ℤ) :
    Function.Injective (fordMomentBinomialTransform (k := k) a) := by
  intro M N hMN
  funext j
  have hcoord : ∀ n : ℕ, ∀ hn : n < k,
      M ⟨n, hn⟩ = N ⟨n, hn⟩ := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro hn
        have hj := congrFun hMN (⟨n, hn⟩ : Fin k)
        unfold fordMomentBinomialTransform at hj
        have hlower :
            fordMomentBinomialLower a M ⟨n, hn⟩ =
              fordMomentBinomialLower a N ⟨n, hn⟩ := by
          unfold fordMomentBinomialLower
          apply Finset.sum_congr rfl
          intro l _
          apply congrArg (fun x : ℤ ↦
            (((n + 1).choose (l.1 + 1) : ℕ) : ℤ) *
              a ^ (n + 1 - (l.1 + 1)) * x)
          simpa only [Fin.eta] using
            ih l.1 l.2 (lt_trans l.2 hn)
        rw [hlower] at hj
        exact add_right_cancel hj
  simpa only [Fin.eta] using hcoord j.1 j.2

theorem fordPolynomialSumInt_translate
    {k d T n P : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (a : ℤ) (z : FordBox n P) (j : Fin k) :
    fordPolynomialSumInt (fordBinomialTranslateSystem Ψ a) z j =
      fordMomentBinomialTransform a (fun l ↦ fordPolynomialSumInt Ψ z l) j := by
  simp only [fordPolynomialSumInt, fordBinomialTranslateSystem,
    fordBinomialTranslatePoly, fordBinomialLower,
    fordMomentBinomialTransform, fordMomentBinomialLower,
    Polynomial.eval_add, Polynomial.eval_finsetSum,
    Polynomial.eval_C_mul, Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  apply congrArg (fun x : ℤ ↦ _ + x)
  apply Finset.sum_congr rfl
  intro l _
  rw [← Finset.mul_sum]

#print axioms fordMomentBinomialTransform_injective
#print axioms fordMomentBinomialTransformHom
#print axioms fordPolynomialSumInt_translate

end

end GafniTao
