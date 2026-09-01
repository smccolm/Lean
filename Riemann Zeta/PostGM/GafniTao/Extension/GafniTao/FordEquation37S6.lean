import GafniTao.FordS6ToL

/-!
# Ford equation (3.7): completed `S_6` estimate

This is the complete final Cauchy--Schwarz line in Ford's proof: the actual
equation-(3.6) collision count is bounded by the literal mixed-modulus `B*`
cardinality and then injected into the exact `L_s` solution count.
-/

namespace GafniTao

noncomputable section

def fordS6Count
    {k d T : ℕ} (Ψ : FordIntegerPolynomialSystem k d T) (c : ℤ)
    (s P Q p q r : ℕ) (hdk : d ≤ k) : ℕ :=
  Nat.card (FordCollisionPairs
    (fun z : FordS6Half k d s P Q p r hdk =>
      fordS6Moment (p := p) (q := q)
        (fordBinomialTranslateSystem Ψ c) z.1))

theorem ford_S6_le_L
    {k d T s P Q p q r : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (c : ℤ) (hp : Nat.Prime p) (hr : 0 < r) (hk2 : 2 ≤ k)
    (hkp : k < p) (hdk : d ≤ k) (hdr : d < r) (hrk : r ≤ k)
    (hpT : ¬p ∣ T) :
    fordS6Count Ψ c s P Q p q r hdk ≤
      ((k - d).factorial *
          p ^ ((r - d - 1) * (r - d) / 2 + r * d)) *
        fordLCount (fordBinomialTranslateSystem Ψ c) s P Q p q r := by
  unfold fordS6Count
  exact (ford_S6_moment_collision_le_residue_diagonal
      Ψ c hp hr hk2 hkp hdk hdr hrk hpT).trans
    (Nat.mul_le_mul_left
      ((k - d).factorial *
        p ^ ((r - d - 1) * (r - d) / 2 + r * d))
      (fordS6FineCollision_card_le_L
        (s := s) (P := P) (Q := Q) (p := p) (q := q) (r := r)
        (fordBinomialTranslateSystem Ψ c) hdk))

#print axioms ford_S6_le_L

end

end GafniTao
