import GafniTao.WooleySection4Dilation
import GafniTao.WooleySection7Congruence
import GafniTao.WooleyTranslationDilation

/-!
# The congruence change in Wooley Lemma 4.1

This file proves the algebraic assertion between equations (4.6) and (4.9).
Starting with a `p^c`-spaced system, translation by the residue `xi`, integral
row reduction modulo `p^B`, and dilation by `p^h` produce a genuinely
`p^(c+h)`-spaced system.  Equal-length tuple congruences for the original
system imply congruences for that new system modulo the common depth
`p^(B-kh)`.
-/

open Finset Polynomial Matrix
open scoped BigOperators

namespace GafniTao

noncomputable section

theorem wooleyIntegerTupleDisplacement_polynomial_C
    {I : Type*} (R : ℕ) (z : ℤ) (point : I → ℤ)
    (xy : WooleyFiniteTuple R I × WooleyFiniteTuple R I) :
    wooleyIntegerTupleDisplacement R
        (fun x => (C z).eval (point x)) xy = 0 := by
  simp [wooleyIntegerTupleDisplacement]

/-- An integral row combination preserves a common tuple congruence. -/
theorem wooleyNormalFormCombination_displacement_dvd
    {I : Type*} {k q R : ℕ}
    (theta : WooleyPolynomialSystem k)
    (G : Matrix (Fin k) (Fin k) (ZMod q)) (i : Fin k)
    (point : I → ℤ)
    (xy : WooleyFiniteTuple R I × WooleyFiniteTuple R I)
    (m : ℤ)
    (hdiv : ∀ j : Fin k, m ∣
      wooleyIntegerTupleDisplacement R
        (fun x => (theta j).eval (point x)) xy) :
    m ∣ wooleyIntegerTupleDisplacement R
      (fun x => (wooleyNormalFormCombination theta q G i).eval (point x)) xy := by
  unfold wooleyNormalFormCombination
  have heval (x : I) :
      (∑ j : Fin k, C (wooleyZModMatrixIntLift G i j) * theta j).eval
          (point x) =
        ∑ j : Fin k,
          wooleyZModMatrixIntLift G i j * (theta j).eval (point x) := by
    simpa only [eval_mul, eval_C] using
      (eval_finsetSum (Finset.univ : Finset (Fin k))
        (fun j => C (wooleyZModMatrixIntLift G i j) * theta j) (point x))
  simp_rw [heval]
  rw [wooleyIntegerTupleDisplacement_sum]
  apply dvd_sum
  intro j hj
  rw [wooleyIntegerTupleDisplacement_smul]
  exact dvd_mul_of_dvd_right (hdiv j) _

/-- Exact source congruence transfer in Lemma 4.1.  The returned `Psi` is
the transformed system in (4.8); its spacing and the common congruence depth
are conclusions, not hypotheses. -/
theorem wooleySection4_exists_dilated_system
    {k p c B h : ℕ}
    (hpPrime : p.Prime) (hc : 1 ≤ c) (hkhB : k * h ≤ B)
    (phi : WooleyPolynomialSystem k) (hphi : phi.Spaced p c)
    (xi : ℤ) :
    ∃ Psi : WooleyPolynomialSystem k,
      Psi.Spaced p (c + h) ∧
      ∀ {I : Type*} {R : ℕ} (point : I → ℤ)
        (xy : WooleyFiniteTuple R I × WooleyFiniteTuple R I),
        (∀ j : Fin k, (p : ℤ) ^ B ∣
          wooleyIntegerTupleDisplacement R
            (fun x => (phi j).eval ((p : ℤ) ^ h * point x + xi)) xy) →
        ∀ i : Fin k, (p : ℤ) ^ (B - k * h) ∣
          wooleyIntegerTupleDisplacement R
            (fun x => (Psi i).eval (point x)) xy := by
  classical
  obtain ⟨G, psi, Error, hchange⟩ :=
    hphi.exists_translated_tail_normal_change hc hpPrime.ne_zero xi
  let Psi := wooleySection4DilatedSystem k p c h psi
  refine ⟨Psi, wooleySection4DilatedSystem_spaced k p c h psi, ?_⟩
  intro I R point xy hsource i
  let theta := wooleyAffinePolynomialSystem phi 1 xi
  let dilatedPoint : I → ℤ := fun x => (p : ℤ) ^ h * point x
  have htheta (j : Fin k) : (p : ℤ) ^ B ∣
      wooleyIntegerTupleDisplacement R
        (fun x => (theta j).eval (dilatedPoint x)) xy := by
    simpa only [theta, dilatedPoint, wooleyAffinePolynomialSystem_eval,
      Nat.cast_one, one_mul] using hsource j
  have hcomb : (p : ℤ) ^ B ∣
      wooleyIntegerTupleDisplacement R
        (fun x =>
          (wooleyNormalFormCombination theta (p ^ B) G i).eval
            (dilatedPoint x)) xy :=
    wooleyNormalFormCombination_displacement_dvd
      theta G i dilatedPoint xy ((p : ℤ) ^ B) htheta
  have hdisp :
      wooleyIntegerTupleDisplacement R
          (fun x =>
            (wooleyNormalFormCombination theta (p ^ B) G i).eval
              (dilatedPoint x)) xy =
        wooleyIntegerTupleDisplacement R
            (fun x =>
              (wooleySection7NormalSystem k p c psi i).eval
                (dilatedPoint x)) xy +
          (p : ℤ) ^ B *
            wooleyIntegerTupleDisplacement R
              (fun x => (Error i).eval (dilatedPoint x)) xy := by
    have hcng := congrArg
      (fun f : Polynomial ℤ =>
        wooleyIntegerTupleDisplacement R
          (fun x => f.eval (dilatedPoint x)) xy) (hchange i)
    dsimp only at hcng
    rw [wooleyIntegerTupleDisplacement_polynomial_add,
      wooleyIntegerTupleDisplacement_polynomial_add,
      wooleyIntegerTupleDisplacement_polynomial_C,
      wooleyIntegerTupleDisplacement_polynomial_C_mul] at hcng
    simpa only [theta, zero_add] using hcng
  have hnormal : (p : ℤ) ^ B ∣
      wooleyIntegerTupleDisplacement R
        (fun x =>
          (wooleySection7NormalSystem k p c psi i).eval
            (dilatedPoint x)) xy := by
    have herr : (p : ℤ) ^ B ∣
        (p : ℤ) ^ B *
          wooleyIntegerTupleDisplacement R
            (fun x => (Error i).eval (dilatedPoint x)) xy := dvd_mul_right _ _
    have hsub := dvd_sub hcomb herr
    rw [hdisp] at hsub
    simpa only [add_sub_cancel_right] using hsub
  have hdilation :
      wooleyIntegerTupleDisplacement R
          (fun x =>
            (wooleySection7NormalSystem k p c psi i).eval
              (dilatedPoint x)) xy =
        (p : ℤ) ^ (h * ((i : ℕ) + 1)) *
          wooleyIntegerTupleDisplacement R
            (fun x => (Psi i).eval (point x)) xy := by
    simp_rw [dilatedPoint, wooleySection7NormalSystem_eval_dilation]
    exact wooleyIntegerTupleDisplacement_smul R
      ((p : ℤ) ^ (h * ((i : ℕ) + 1)))
      (fun x => (Psi i).eval (point x)) xy
  have hi : (i : ℕ) + 1 ≤ k := i.isLt
  have hiB : ((i : ℕ) + 1) * h ≤ B := by
    exact (Nat.mul_le_mul_right h hi).trans hkhB
  have hcancel : (p : ℤ) ^ (B - ((i : ℕ) + 1) * h) ∣
      wooleyIntegerTupleDisplacement R
        (fun x => (Psi i).eval (point x)) xy := by
    apply pow_dvd_of_mul_pow_dvd hpPrime.ne_zero hiB
    have hnormal' : (p : ℤ) ^ B ∣
        (p : ℤ) ^ (h * ((i : ℕ) + 1)) *
          wooleyIntegerTupleDisplacement R
            (fun x => (Psi i).eval (point x)) xy := by
      rwa [hdilation] at hnormal
    simpa only [Nat.mul_comm h ((i : ℕ) + 1)] using hnormal'
  have hexp : B - k * h ≤ B - ((i : ℕ) + 1) * h := by
    have hil : ((i : ℕ) + 1) * h ≤ k * h := Nat.mul_le_mul_right h hi
    omega
  exact (pow_dvd_pow (p : ℤ) hexp).trans hcancel

#print axioms wooleyIntegerTupleDisplacement_polynomial_C
#print axioms wooleyNormalFormCombination_displacement_dvd
#print axioms wooleySection4_exists_dilated_system

end

end GafniTao
