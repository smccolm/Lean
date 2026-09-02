import GafniTao.FordLemma34BackwardCombinatorial

/-! # Ford Lemma 3.4: the named Lemma-3.3 raw bound -/

namespace GafniTao

noncomputable section

theorem ford_equation_3_10_L_raw
    {s k r d T p q : ℕ} {C delta P eta M Q Qnext EschE : ℝ}
    (Ψ : FordIntegerPolynomialSystem k d T)
    (hJr : d + 1 < r) (hr2 : 2 ≤ r) (hrk : r ≤ k)
    (hJs : d + 1 ≤ s) (hq : 0 < q) (hp : Nat.Prime p)
    (hT : 0 < T) (hP : 1 ≤ P) (hQ : 1 ≤ Q)
    (hmoment : FordVinogradovMomentBound s k C delta)
    (hK : ∀ {T' : ℕ} (Υ : FordIntegerPolynomialSystem k (d + 1) T'),
      T ≤ T' → T' ≤ ⌊P⌋₊ * T →
      (fordKCountReal Υ s P Q (p * q) : ℝ) ≤
        fordLemma34KBound s k r (d + 1) C delta P eta M Qnext EschE) :
    (fordLCountReal Ψ s P Q p q r : ℝ) ≤
      fordLemma34RawBound s k r (d + 1) p C delta P eta M Q Qnext EschE := by
  have hJactual : (fordVinogradovMoment s k Q : ℝ) ≤
      fordLemma34JBound s k C delta Q := hmoment.real_endpoint hQ
  have hJnonneg : 0 ≤ fordLemma34JBound s k C delta Q := by
    unfold fordLemma34JBound
    have hC : 0 ≤ C := hmoment.one_le_coefficient.trans' zero_le_one
    positivity
  exact ford_lemma_3_3_consume_uniform_K_bound_real
    (s := s) (r := r) (Q := Q)
    (JBound := fordLemma34JBound s k C delta Q)
    (KBound := fordLemma34KBound s k r (d + 1) C delta P eta M Qnext EschE)
    Ψ (show d ≤ s by omega) hr2 hrk (show d ≤ k - 2 by omega)
    (show 1 ≤ q by omega) hp hT (Nat.floor_pos.mpr hP) hJactual
    hK hJnonneg

#print axioms ford_equation_3_10_L_raw

end

end GafniTao
