import GafniTao.WooleyTranslationMatrix

/-!
# Normalizing the translated Section 7 equations

After the right residue representative is subtracted in (7.6), the source
polynomials are composed with `X + eta`.  Such a translated system is not
itself `p^c`-spaced under the literal definition (3.1).  Its positive low
coefficient matrix is nevertheless a unit, and its high tail remains
coefficientwise divisible by `p^c`.  These are precisely the two facts needed
for the integral row reduction to (7.7).
-/

open Finset Polynomial Matrix
open scoped BigOperators

namespace GafniTao

noncomputable section

theorem wooleyNormalFormCombination_high_coeff_dvd_of_each
    {k p c q : ℕ} (theta : WooleyPolynomialSystem k)
    (hhigh : ∀ j : Fin k, ∀ n : ℕ, k + 1 ≤ n →
      (p : ℤ) ^ c ∣ (theta j).coeff n)
    (G : Matrix (Fin k) (Fin k) (ZMod q)) (i : Fin k)
    (n : ℕ) (hn : k + 1 ≤ n) :
    (p : ℤ) ^ c ∣ (wooleyNormalFormCombination theta q G i).coeff n := by
  unfold wooleyNormalFormCombination
  rw [← lcoeff_apply, map_sum]
  simp only [lcoeff_apply, coeff_C_mul]
  apply dvd_sum
  intro j hj
  exact dvd_mul_of_dvd_right (hhigh j n hn) _

/-- Generic row normalization from an invertible positive low matrix and a
coefficientwise `p^c`-divisible high tail. -/
theorem wooley_exists_tail_normal_change_of_leftInverse_high
    {k p c B : ℕ} (theta : WooleyPolynomialSystem k)
    (G : Matrix (Fin k) (Fin k) (ZMod (p ^ B)))
    (hG : G * Matrix.transpose
      (wooleyPolynomialSystemLowMatrixMod theta (p ^ B)) = 1)
    (hhigh : ∀ j : Fin k, ∀ n : ℕ, k + 1 ≤ n →
      (p : ℤ) ^ c ∣ (theta j).coeff n)
    (hp : p ≠ 0) :
    ∃ psi Error : WooleyPolynomialSystem k,
      ∀ i : Fin k,
        wooleyNormalFormCombination theta (p ^ B) G i =
          C ((wooleyNormalFormCombination theta (p ^ B) G i).coeff 0) +
            wooleySection7NormalSystem k p c psi i +
            C ((p : ℤ) ^ B) * Error i := by
  choose lowError hlow using fun i : Fin k =>
    wooleyNormalFormPositiveLow_exists_error G hG i
  let f (i : Fin k) := wooleyNormalFormCombination theta (p ^ B) G i -
    C ((wooleyNormalFormCombination theta (p ^ B) G i).coeff 0)
  have hfzero (i : Fin k) : (f i).coeff 0 = 0 := by
    simp [f]
  have hfhigh (i : Fin k) (n : ℕ) (hn : k + 1 ≤ n) :
      (p : ℤ) ^ c ∣ (f i).coeff n := by
    simp only [f, coeff_sub, coeff_C]
    rw [if_neg (by omega : n ≠ 0), sub_zero]
    exact wooleyNormalFormCombination_high_coeff_dvd_of_each
      theta hhigh G i n hn
  choose psi htail using fun i : Fin k =>
    wooleyPolynomial_exists_positiveLow_add_scalar_X_tail
      k (f i) ((p : ℤ) ^ c) (pow_ne_zero c (by exact_mod_cast hp))
        (hfzero i) (hfhigh i)
  refine ⟨psi, lowError, ?_⟩
  intro i
  have hpositive :
      (∑ d : Fin k, C ((f i).coeff ((d : ℕ) + 1)) *
        X ^ ((d : ℕ) + 1)) =
      wooleyNormalFormPositiveLow theta (p ^ B) G i := by
    unfold wooleyNormalFormPositiveLow
    apply Finset.sum_congr rfl
    intro d hd
    congr 2
    simp only [f, coeff_sub, coeff_C]
    rw [if_neg (by omega : (d : ℕ) + 1 ≠ 0), sub_zero]
  have hf := htail i
  rw [hpositive, hlow i] at hf
  dsimp only [f] at hf
  unfold wooleySection7NormalSystem
  calc
    wooleyNormalFormCombination theta (p ^ B) G i =
        C ((wooleyNormalFormCombination theta (p ^ B) G i).coeff 0) +
          (wooleyNormalFormCombination theta (p ^ B) G i -
            C ((wooleyNormalFormCombination theta (p ^ B) G i).coeff 0)) := by
              ring
    _ = _ := by rw [hf]; ring

/-- Exact translated normal-form change used between (7.6) and (7.7). -/
theorem WooleyPolynomialSystem.Spaced.exists_translated_tail_normal_change
    {k p c B : ℕ} {phi : WooleyPolynomialSystem k}
    (hphi : phi.Spaced p c) (hc : 1 ≤ c) (hp : p ≠ 0)
    (eta : ℤ) :
    ∃ G : Matrix (Fin k) (Fin k) (ZMod (p ^ B)),
      ∃ psi Error : WooleyPolynomialSystem k,
      ∀ i : Fin k,
        wooleyNormalFormCombination
            (wooleyAffinePolynomialSystem phi 1 eta) (p ^ B) G i =
          C ((wooleyNormalFormCombination
            (wooleyAffinePolynomialSystem phi 1 eta)
              (p ^ B) G i).coeff 0) +
            wooleySection7NormalSystem k p c psi i +
            C ((p : ℤ) ^ B) * Error i := by
  obtain ⟨G, hG⟩ :=
    wooleyAffinePolynomialSystem_exists_lowMatrix_leftInverse
      (B := B) hphi hc eta
  obtain ⟨psi, Error, hchange⟩ :=
    wooley_exists_tail_normal_change_of_leftInverse_high
      (wooleyAffinePolynomialSystem phi 1 eta) G hG
      (fun j n hn => hphi.affine_one_high_coeff_dvd eta j n hn) hp
  exact ⟨G, psi, Error, hchange⟩

#print axioms wooleyNormalFormCombination_high_coeff_dvd_of_each
#print axioms wooley_exists_tail_normal_change_of_leftInverse_high
#print axioms WooleyPolynomialSystem.Spaced.exists_translated_tail_normal_change

end

end GafniTao
