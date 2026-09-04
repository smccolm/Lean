import GafniTao.WooleyTranslatedNormalChange

/-!
# The exact dilation in Wooley Lemma 4.1

After the integral translation and row normalization, equation `i` has the
form `X^(i+1) + p^c X^(k+1) psi_i`.  Substitution `X = p^h Y`
has the visible factor `p^(h(i+1))`; the remaining tail has a common extra
factor `p^(c+h)`.  This file records that polynomial identity exactly.
-/

open Finset Polynomial
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- The residual tail after extracting `p^(h(i+1))` from the translated and
dilated normal-form equation. -/
def wooleySection4DilatedTail
    (k p h : ℕ) (psi : WooleyPolynomialSystem k) (i : Fin k) :
    Polynomial ℤ :=
  C ((p : ℤ) ^ (h * (k - ((i : ℕ) + 1)))) * X ^ (k + 1) *
    (psi i).comp (C ((p : ℤ) ^ h) * X)

/-- The source system `Phi` in (4.8), after extracting the equationwise
visible dilation factors. -/
def wooleySection4DilatedSystem
    (k p c h : ℕ) (psi : WooleyPolynomialSystem k) :
    WooleyPolynomialSystem k := fun i =>
  X ^ ((i : ℕ) + 1) +
    C ((p : ℤ) ^ (c + h)) * wooleySection4DilatedTail k p h psi i

/-- The system in (4.8) is literally `p^(c+h)`-spaced. -/
theorem wooleySection4DilatedSystem_spaced
    (k p c h : ℕ) (psi : WooleyPolynomialSystem k) :
    (wooleySection4DilatedSystem k p c h psi).Spaced p (c + h) := by
  refine ⟨fun i => wooleySection4DilatedTail k p h psi i, ?_⟩
  intro i
  rfl

/-- Exact polynomial evaluation underlying equations (4.7)--(4.9). -/
theorem wooleySection7NormalSystem_eval_dilation
    {k p c h : ℕ} (psi : WooleyPolynomialSystem k) (i : Fin k)
    (y : ℤ) :
    (wooleySection7NormalSystem k p c psi i).eval
        ((p : ℤ) ^ h * y) =
      (p : ℤ) ^ (h * ((i : ℕ) + 1)) *
        (wooleySection4DilatedSystem k p c h psi i).eval y := by
  have hid :
      h * ((i : ℕ) + 1) + (c + h) +
          h * (k - ((i : ℕ) + 1)) =
        c + h * (k + 1) := by
    have hi : (i : ℕ) + 1 ≤ k := i.isLt
    have hsplit :
        h * ((i : ℕ) + 1) + h * (k - ((i : ℕ) + 1)) = h * k := by
      rw [← Nat.mul_add, Nat.add_sub_of_le hi]
    calc
      h * ((i : ℕ) + 1) + (c + h) +
          h * (k - ((i : ℕ) + 1)) =
        c + h + (h * ((i : ℕ) + 1) +
          h * (k - ((i : ℕ) + 1))) := by omega
      _ = c + h + h * k := by rw [hsplit]
      _ = c + h * (k + 1) := by rw [Nat.mul_succ]; omega
  have hpow :
      (p : ℤ) ^ c * (p : ℤ) ^ (h * (k + 1)) =
        (p : ℤ) ^ (h * ((i : ℕ) + 1)) *
          ((p : ℤ) ^ (c + h) *
            (p : ℤ) ^ (h * (k - ((i : ℕ) + 1)))) := by
    rw [← pow_add, ← pow_add, ← pow_add]
    congr 1
    omega
  unfold wooleySection7NormalSystem wooleySection4DilatedSystem
    wooleySection4DilatedTail
  simp only [eval_add, eval_pow, eval_X, eval_mul, eval_C, eval_comp]
  simp only [mul_pow, ← pow_mul]
  have htail :
      (p : ℤ) ^ c *
          ((p : ℤ) ^ (h * (k + 1)) * y ^ (k + 1)) *
          (psi i).eval ((p : ℤ) ^ h * y) =
        (p : ℤ) ^ (h * ((i : ℕ) + 1)) *
          ((p : ℤ) ^ (c + h) *
            ((p : ℤ) ^ (h * (k - ((i : ℕ) + 1))) *
              y ^ (k + 1) * (psi i).eval ((p : ℤ) ^ h * y))) := by
    calc
      _ = ((p : ℤ) ^ c * (p : ℤ) ^ (h * (k + 1))) *
          (y ^ (k + 1) * (psi i).eval ((p : ℤ) ^ h * y)) := by ring
      _ = _ := by rw [hpow]; ring
  rw [htail]
  ring

#print axioms wooleySection4DilatedSystem_spaced
#print axioms wooleySection7NormalSystem_eval_dilation

end

end GafniTao
