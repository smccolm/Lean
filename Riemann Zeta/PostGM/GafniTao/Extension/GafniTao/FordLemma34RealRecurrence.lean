import GafniTao.FordLemma34RealStep

/-!
# Ford Lemma 3.4: real-scale Lemma 3.3 consumer

The source `P,Q` are real endpoints; the congruence and polynomial variables
remain integral.  This wrapper is definitionally the already proved finite
Lemma 3.3 consumer after flooring the two box endpoints once.
-/

namespace GafniTao

noncomputable section

theorem ford_lemma_3_3_consume_uniform_K_bound_real
    {k d T p r s q : ℕ} {P Q JBound KBound : ℝ}
    (Ψ : FordIntegerPolynomialSystem k d T)
    (hsd : d ≤ s) (hr2 : 2 ≤ r) (hrk : r ≤ k)
    (hdk : d ≤ k - 2) (hq : 1 ≤ q) (hp : Nat.Prime p)
    (hT : 0 < T) (hP : 0 < ⌊P⌋₊)
    (hJ : (fordVinogradovMoment s k Q : ℝ) ≤ JBound)
    (hK : ∀ {T' : ℕ} (Υ : FordIntegerPolynomialSystem k (d + 1) T'),
      T ≤ T' → T' ≤ ⌊P⌋₊ * T →
      (fordKCountReal Υ s P Q (p * q) : ℝ) ≤ KBound)
    (hJBound : 0 ≤ JBound) :
    (fordLCountReal Ψ s P Q p q r : ℝ) ≤
      ((2 * ⌊P⌋₊ : ℕ) : ℝ) ^ k *
        max (((k ^ k : ℕ) : ℝ) * JBound)
          (2 * (((p : ℝ) ^ (r * k))⁻¹) * √(JBound * KBound)) := by
  simpa [fordLCountReal, fordKCountReal, fordVinogradovMoment] using
    ford_lemma_3_3_consume_uniform_K_bound Ψ hsd hr2 hrk hdk hq hp hT hP
      hJ hK hJBound

#print axioms ford_lemma_3_3_consume_uniform_K_bound_real

end

end GafniTao
