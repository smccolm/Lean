import GafniTao.FordLemma34RawAlgebra

/-! # Ford Lemma 3.4: unconditional backward equation-(3.10) step -/

namespace GafniTao

noncomputable section

/-- One complete backward step in Ford equation (3.10).  Unlike the
counting-only composition theorem, this public theorem derives the raw-bound
absorption from the source `phi` and `E` recurrences. -/
theorem ford_equation_3_10_backward
    {s k r j d : ℕ} {C delta P eta omega : ℝ}
    (Φ : FordPhiSchedule k r j delta)
    (Esch : FordESchedule s k j eta)
    (hk : 26 ≤ k) (hr2 : 2 ≤ r) (hrk : r ≤ k) (hks : k ≤ s)
    (hdj : d + 1 < j) (hjr : j ≤ r)
    (hP : 1 ≤ P) (hPbig : 4 * k ^ 4 < ⌊P⌋₊)
    (heta : 1 ≤ eta)
    (homega : 1 / (3 * Real.log k) ≤ omega) (hetaEq : eta = 1 + omega)
    (hM : 1 < fordMScale P Φ (d + 2))
    (hkM : k ≤ ⌊fordMScale P Φ (d + 2)⌋₊)
    (hPM : P ≤ (fordMScale P Φ (d + 2)) ^ (k + 1))
    (hQbox : 32 * s ^ 2 * ⌈fordMScale P Φ (d + 2)⌉₊ <
      ⌊fordQScale P Φ (d + 1)⌋₊)
    (hpacketTwo : ∀ p ∈ fordPrimeSet k ⌊fordMScale P Φ (d + 2)⌋₊,
      p ≤ 2 * ⌈fordMScale P Φ (d + 2)⌉₊)
    (hpacketBound : ∀ p ∈ fordPrimeSet k ⌊fordMScale P Φ (d + 2)⌋₊,
      (p : ℝ) ≤ eta * fordMScale P Φ (d + 2))
    (hquotient : ∀ p ∈ fordPrimeSet k ⌊fordMScale P Φ (d + 2)⌋₊,
      ((⌊fordQScale P Φ (d + 1)⌋₊ / p : ℕ) : ℝ) ≤
        fordQScale P Φ (d + 2))
    (hQ : 1 ≤ fordQScale P Φ (d + 1))
    (hmoment : FordVinogradovMomentBound s k C delta)
    (hIH : FordEquation310Eta s k r j C delta P eta Φ Esch (d + 1)) :
    FordEquation310Eta s k r j C delta P eta Φ Esch d := by
  apply ford_equation_3_10_backward_combinatorial Φ Esch
    hk hr2 hrk hks hdj hjr hP hPbig hM hkM hPM hQbox
    hpacketTwo hpacketBound hquotient hQ hmoment hIH
  intro p hp
  have habs := ford_lemma_3_4_raw_absorption Φ Esch
    hk hr2 hrk hks (show 1 ≤ d + 1 by omega) hdj hjr hP heta
    homega hetaEq hM.le hmoment hp
  simpa only [Nat.add_sub_cancel] using habs

#print axioms ford_equation_3_10_backward

end

end GafniTao
