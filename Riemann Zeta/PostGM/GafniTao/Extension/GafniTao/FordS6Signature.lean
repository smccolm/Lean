import GafniTao.FordS6Setup

/-!
# Ford Lemma 3.2: the moment determines the mixed residue signature

Equation (3.6) has a factor `(pq)^j` in its power-sum term.  Reduction modulo
`p^min(j,r)` therefore removes that term, leaving exactly the `B*(m)`
signature of the polynomial coordinates.  The lemmas below prove this using
the literal translated system and the split finite index set.
-/

open Finset Polynomial
open scoped BigOperators

namespace GafniTao

noncomputable section

theorem fordPolynomialEvalSum_map_split
    {k d P n : ℕ} (hdk : d ≤ k) (f : ℤ[X]) (z : FordBox k P) :
    fordPolynomialEvalSum (f.map (Int.castRingHom (ZMod n)))
        (fun i : Fin (k - d) =>
          (fordBoxValue z (fordHeadIndex hdk i) : ZMod n)) +
      fordPolynomialEvalSum (f.map (Int.castRingHom (ZMod n)))
        (fun i : Fin d =>
          (fordBoxValue z (fordTailIndex hdk i) : ZMod n)) =
      ((∑ i : Fin k, f.eval (fordBoxValue z i : ℤ) : ℤ) : ZMod n) := by
  unfold fordPolynomialEvalSum
  calc
    (∑ i : Fin (k - d),
        (f.map (Int.castRingHom (ZMod n))).eval
          (fordBoxValue z (fordHeadIndex hdk i) : ZMod n)) +
        ∑ i : Fin d,
          (f.map (Int.castRingHom (ZMod n))).eval
            (fordBoxValue z (fordTailIndex hdk i) : ZMod n) =
        ∑ i : Fin (k - d) ⊕ Fin d,
          (f.map (Int.castRingHom (ZMod n))).eval
            (fordBoxValue z (fordSplitFinEquiv hdk i) : ZMod n) := by
      rw [Fintype.sum_sum_type]
      rfl
    _ = ∑ i : Fin k,
          (f.map (Int.castRingHom (ZMod n))).eval
            (fordBoxValue z i : ZMod n) :=
      Equiv.sum_comp (fordSplitFinEquiv hdk)
        (fun i : Fin k =>
          (f.map (Int.castRingHom (ZMod n))).eval
            (fordBoxValue z i : ZMod n))
    _ = ((∑ i : Fin k, f.eval (fordBoxValue z i : ℤ) : ℤ) :
        ZMod n) := by
      push_cast
      apply Finset.sum_congr rfl
      intro i _
      rw [Polynomial.eval_map]
      simpa using (Polynomial.eval₂_at_apply
        (p := f) (Int.castRingHom (ZMod n))
        (fordBoxValue z i : ℤ))

theorem fordSourceBStarSignature_split_eq_cast
    {k d T P p r : ℕ} (Ψ : FordIntegerPolynomialSystem k d T) (c : ℤ)
    (hp : Nat.Prime p) (hr : 0 < r) (hk2 : 2 ≤ k)
    (hkp : k < p) (hdk : d ≤ k) (hpT : ¬p ∣ T)
    (z : FordBox k P) (hinj : Function.Injective (fun i : Fin (k - d) =>
      fordPrimeReduction
        ((fordBoxValue z (fordHeadIndex hdk i) : ℕ) : ZMod (p ^ r))))
    (j : Fin (k - d)) :
    fordSourceBStarSignature Ψ c hp hr hk2 hkp hdk hpT
        ⟨(fordSplitResidue (p := p) (r := r) hdk z).1,
          ⟨(fordSplitResidue (p := p) (r := r) hdk z).2, hinj⟩⟩ j =
      ((fordPolynomialSumInt (fordBinomialTranslateSystem Ψ c) z
          (fordAboveIndex hdk j) : ℤ) :
        ZMod (p ^ fordBStarModulusExponent d r j)) := by
  unfold fordSourceBStarSignature fordTranslatedSystemAboveModPrimePower
    fordIntegerSystemAboveModPrimePower fordSplitResidue
  change fordPrimePowerCastHom p r (fordBStarModulusExponent d r j)
      (fordBStarModulusExponent_le j)
      (fordPolynomialEvalSum
          (((fordBinomialTranslateSystem Ψ c).poly
            (fordAboveIndex hdk j)).map (Int.castRingHom (ZMod (p ^ r))))
          (fun i : Fin (k - d) =>
            (fordBoxValue z (fordHeadIndex hdk i) : ZMod (p ^ r))) +
        fordPolynomialEvalSum
          (((fordBinomialTranslateSystem Ψ c).poly
            (fordAboveIndex hdk j)).map (Int.castRingHom (ZMod (p ^ r))))
          (fun i : Fin d =>
            (fordBoxValue z (fordTailIndex hdk i) : ZMod (p ^ r)))) = _
  rw [fordPolynomialEvalSum_map_split hdk]
  unfold fordPrimePowerCastHom
  simp [fordPolynomialSumInt]

theorem fordS6_power_term_cast_eq_zero
    {s Q p q J e : ℕ} (heJ : e ≤ J) (u : FordBox s Q) :
    ((((p * q : ℕ) : ℤ) ^ J * fordPowerSumInt u J : ℤ) :
      ZMod (p ^ e)) = 0 := by
  have hpow : p ^ e ∣ p ^ J := pow_dvd_pow p heJ
  have hpq : p ^ J ∣ (p * q) ^ J :=
    pow_dvd_pow_of_dvd (Nat.dvd_mul_right p q) J
  have hzero : (((p * q) ^ J : ℕ) : ZMod (p ^ e)) = 0 :=
    (ZMod.natCast_eq_zero_iff ((p * q) ^ J) (p ^ e)).2
      (hpow.trans hpq)
  push_cast
  have hzero' : ((p : ZMod (p ^ e)) * (q : ZMod (p ^ e))) ^ J = 0 := by
    simpa only [Nat.cast_mul, Nat.cast_pow] using hzero
  rw [hzero', zero_mul]

theorem fordS6_signature_eq_moment_cast
    {k d T s P Q p q r : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (c : ℤ) (hp : Nat.Prime p) (hr : 0 < r) (hk2 : 2 ≤ k)
    (hkp : k < p) (hdk : d ≤ k) (hpT : ¬p ∣ T)
    (z : FordS6Half k d s P Q p r hdk) :
    fordSourceBStarSignature Ψ c hp hr hk2 hkp hdk hpT
        (fordS6HalfResidue z) =
      fun j : Fin (k - d) =>
        ((fordS6Moment (p := p) (q := q)
            (fordBinomialTranslateSystem Ψ c) z.1
            (fordAboveIndex hdk j) : ℤ) :
          ZMod (p ^ fordBStarModulusExponent d r j)) := by
  funext j
  change fordSourceBStarSignature Ψ c hp hr hk2 hkp hdk hpT
      ⟨(fordSplitResidue (p := p) (r := r) hdk z.1.1).1,
        ⟨(fordSplitResidue (p := p) (r := r) hdk z.1.1).2, z.2⟩⟩ j = _
  rw [fordSourceBStarSignature_split_eq_cast Ψ c hp hr hk2 hkp hdk hpT
    z.1.1 z.2 j]
  have hterm := fordS6_power_term_cast_eq_zero
    (p := p) (q := q) (u := z.1.2)
    (show fordBStarModulusExponent d r j ≤
        ((fordAboveIndex hdk j : Fin k) : ℕ) + 1 by
      unfold fordBStarModulusExponent
      simp only [fordAboveIndex_val]
      exact min_le_left _ _)
  push_cast at hterm
  unfold fordS6Moment
  push_cast
  rw [hterm, add_zero]

#print axioms fordPolynomialEvalSum_map_split
#print axioms fordSourceBStarSignature_split_eq_cast
#print axioms fordS6_power_term_cast_eq_zero
#print axioms fordS6_signature_eq_moment_cast

end

end GafniTao
