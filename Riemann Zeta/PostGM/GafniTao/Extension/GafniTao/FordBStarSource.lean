import GafniTao.FordBStarBound

/-!
# Ford Lemma 3.2: source-specialized `B*`

The generic resolved count is specialized here to Ford's binomial translate
`Phi`.  Once the last `d` coordinates are fixed, the head target is literally
the selected lift of `m_j` minus the contribution of those tail coordinates.
-/

namespace GafniTao

noncomputable section

def fordTranslatedSystemAboveModPrimePower
    {k d T p r : ℕ} (ψ : FordIntegerPolynomialSystem k d T) (c : ℤ)
    (hp : Nat.Prime p) (hr : 0 < r) (hk2 : 2 ≤ k)
    (hkp : k < p) (hdk : d ≤ k) (hpT : ¬p ∣ T) :
    FordPrimePowerTriangularPolynomialSystem p r (k - d) :=
  fordIntegerSystemAboveModPrimePower (fordBinomialTranslateSystem ψ c)
    hp hr hk2 hkp hdk hpT

def fordSourceBStarTarget
    {k d T p r : ℕ} (ψ : FordIntegerPolynomialSystem k d T) (c : ℤ)
    (hp : Nat.Prime p) (hr : 0 < r) (hk2 : 2 ≤ k)
    (hkp : k < p) (hdk : d ≤ k) (hpT : ¬p ∣ T)
    (m : ∀ j : Fin (k - d),
      ZMod (p ^ fordBStarModulusExponent d r j))
    (tail : Fin d → ZMod (p ^ r))
    (lifts : FordBStarLiftFamily p d r (k - d) m) :
    Fin (k - d) → ZMod (p ^ r) := fun j =>
  (lifts j).1 - fordPolynomialEvalSum
    ((fordTranslatedSystemAboveModPrimePower ψ c hp hr hk2 hkp hdk hpT).1 j)
    tail

def FordSourceResolvedBStar
    {k d T p r : ℕ} (ψ : FordIntegerPolynomialSystem k d T) (c : ℤ)
    (hp : Nat.Prime p) (hr : 0 < r) (hk2 : 2 ≤ k)
    (hkp : k < p) (hdk : d ≤ k) (hpT : ¬p ∣ T)
    (m : ∀ j : Fin (k - d),
      ZMod (p ^ fordBStarModulusExponent d r j)) :=
  FordResolvedBStar
    (fordTranslatedSystemAboveModPrimePower ψ c hp hr hk2 hkp hdk hpT) m
    (fordSourceBStarTarget ψ c hp hr hk2 hkp hdk hpT m)

/-- Ford's displayed `B*` estimate, with the exact source polynomial system,
the exact mixed moduli `p^min(j,r)`, and the exact tail subtraction. -/
theorem ford_source_resolvedBStar_card_le
    {k d T p r : ℕ} (ψ : FordIntegerPolynomialSystem k d T) (c : ℤ)
    (hp : Nat.Prime p) (hr : 0 < r) (hk2 : 2 ≤ k)
    (hkp : k < p) (hdk : d ≤ k) (hdr : d < r) (hrk : r ≤ k)
    (hpT : ¬p ∣ T)
    (m : ∀ j : Fin (k - d),
      ZMod (p ^ fordBStarModulusExponent d r j)) :
    Nat.card (FordSourceResolvedBStar ψ c hp hr hk2 hkp hdk hpT m) ≤
      (k - d).factorial *
        p ^ ((r - d - 1) * (r - d) / 2 + r * d) := by
  have hnp : k - d < p := (Nat.sub_le k d).trans_lt hkp
  have h := fordResolvedBStar_card_le hp hr hdr hnp
    (fordTranslatedSystemAboveModPrimePower ψ c hp hr hk2 hkp hdk hpT) m
    (fordSourceBStarTarget ψ c hp hr hk2 hkp hdk hpT m)
  rw [fordBStarLiftExponent_eq hdr hrk] at h
  exact h

theorem ford_prime_avoiding_jacobian_implies_not_dvd_T
    {p T A B : ℕ} (havoid : ¬p ∣ T * A * B) : ¬p ∣ T := by
  intro hpT
  exact havoid (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hpT A) B)

#print axioms fordTranslatedSystemAboveModPrimePower
#print axioms fordSourceBStarTarget
#print axioms ford_source_resolvedBStar_card_le
#print axioms ford_prime_avoiding_jacobian_implies_not_dvd_T

end

end GafniTao
