import GafniTao.FordLemma34Terminal

/-!
# Ford Lemma 3.4: consuming Lemma 3.3 in the induction

This file converts upper bounds for the genuine Vinogradov moment and for
the genuine `K_s` count into the preceding `L_s` bound.  The existential
polynomial system returned by Lemma 3.3 is explicitly unpacked and passed to
the uniform `K_s` hypothesis.
-/

namespace GafniTao

noncomputable section

theorem ford_lemma_3_3_consume_uniform_K_bound
    {k d T P p r s Q q : ℕ} {JBound KBound : ℝ}
    (Ψ : FordIntegerPolynomialSystem k d T)
    (hsd : d ≤ s) (hr2 : 2 ≤ r) (hrk : r ≤ k)
    (hdk : d ≤ k - 2) (hq : 1 ≤ q) (hp : Nat.Prime p)
    (hT : 0 < T) (hP : 0 < P)
    (hJ : (fordVinogradovMomentNat s k Q : ℝ) ≤ JBound)
    (hK : ∀ {T' : ℕ} (Υ : FordIntegerPolynomialSystem k (d + 1) T'),
      T ≤ T' → T' ≤ P * T →
      (fordKCount Υ s P Q (p * q) : ℝ) ≤ KBound)
    (hJBound : 0 ≤ JBound) :
    (fordLCount Ψ s P Q p q r : ℝ) ≤
      ((2 * P : ℕ) : ℝ) ^ k *
        max (((k ^ k : ℕ) : ℝ) * JBound)
          (2 * (((p : ℝ) ^ (r * k))⁻¹) * √(JBound * KBound)) := by
  obtain ⟨T', Υ, hTT', hT'PT, hL⟩ :=
    ford_lemma_3_3_finite_source Ψ hsd hr2 hrk hdk hq hp hT hP
  have hKΥ := hK Υ hTT' hT'PT
  have hdiag :
      (((k ^ k * fordVinogradovMomentNat s k Q : ℕ) : ℝ)) ≤
        (((k ^ k : ℕ) : ℝ) * JBound) := by
    push_cast
    gcongr
  have hprod :
      (fordVinogradovMomentNat s k Q : ℝ) *
          (fordKCount Υ s P Q (p * q) : ℝ) ≤
        JBound * KBound := by
    exact mul_le_mul hJ hKΥ (by positivity) hJBound
  have hsqrt :
      √((fordVinogradovMomentNat s k Q : ℝ) *
          (fordKCount Υ s P Q (p * q) : ℝ)) ≤
        √(JBound * KBound) :=
    Real.sqrt_le_sqrt hprod
  have hoff :
      2 * (((p : ℝ) ^ (r * k))⁻¹) *
          √((fordVinogradovMomentNat s k Q : ℝ) *
            (fordKCount Υ s P Q (p * q) : ℝ)) ≤
        2 * (((p : ℝ) ^ (r * k))⁻¹) * √(JBound * KBound) := by
    gcongr
  exact hL.trans (mul_le_mul_of_nonneg_left
    (max_le_max hdiag hoff) (by positivity))

#print axioms ford_lemma_3_3_consume_uniform_K_bound

end

end GafniTao
