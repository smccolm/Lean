import Dubon2026.HeckeTransversalTrace

/-! # Exact adjugate trace over the lower Gamma0 congruence transversal -/

namespace Dubon2026

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane Finset
open scoped MatrixGroups ModularForm

noncomputable section

/-- The actual classical prime matrices indexed by the projective line. -/
def heckePrimeRepresentative (p : ℕ) [NeZero p] : Option (ZMod p) → GL (Fin 2) ℝ
  | none => heckeTriangularMatrix p 1 0
  | some x => heckeTriangularMatrix 1 p x.val

/-- The lower-transversal permutation exchanges infinity with zero. -/
def heckeLowerIndex (p Q : ℕ) : Option (ZMod p) → Option (ZMod p)
  | none => some 0
  | some x => if x = 0 then none else some (((Q : ZMod p) * x)⁻¹)

/-- The exact finite permutation is involutive at every good prime. -/
theorem heckeLowerIndex_involutive {p Q : ℕ} (hp : Nat.Prime p) (hpQ : Nat.Coprime p Q) :
    Function.Involutive (heckeLowerIndex p Q) := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  intro x
  cases x with
  | none => simp [heckeLowerIndex]
  | some x =>
    by_cases hx : x = 0
    · simp [heckeLowerIndex, hx]
    · have hQ := heckePrime_level_ne_zero hp hpQ
      simp [heckeLowerIndex, hx, hQ, _root_.mul_inv_rev, mul_left_comm]

/-- The actual index equivalence for the lower trace. -/
def heckeLowerIndexEquiv {p Q : ℕ} (hp : Nat.Prime p) (hpQ : Nat.Coprime p Q) :
    Option (ZMod p) ≃ Option (ZMod p) :=
  (heckeLowerIndex_involutive hp hpQ).toPerm

/-- Each lower-transversal slash term is an ordinary classical prime term with the exact index. -/
theorem heckeLowerTrace_term {p Q : ℕ} [NeZero p] {k : ℤ}
    (hp : Nat.Prime p) (hpQ : Nat.Coprime p Q)
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (x : Option (ZMod p)) :
    (⇑f ∣[k] heckeTriangularMatrix p 1 0) ∣[k]
        mapGL ℝ (heckeLowerRepresentative p Q hpQ x).val =
      ⇑f ∣[k] heckePrimeRepresentative p (heckeLowerIndex p Q x) := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  cases x with
  | none =>
    have hC : ¬(p : ℤ) ∣ (heckeLowerRepresentative p Q hpQ none).val 1 0 := by
      intro h
      apply heckePrime_level_ne_zero hp hpQ
      simpa [heckeLowerRepresentative, heckeLowerBezoutRepresentative] using
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr h
    have h := cusp_slash_factor f (heckeLowerRepresentative p Q hpQ none).val
      (heckePrime_lower_factor hp _ (heckeLowerRepresentative p Q hpQ none).property hC)
    simpa [heckeLowerIndex, heckePrimeRepresentative, heckeLowerRepresentative,
      heckeLowerBezoutRepresentative] using h
  | some x =>
    by_cases hx : x = 0
    · subst hx
      have he : mapGL ℝ (heckeLowerRepresentative p Q hpQ (some 0)).val = 1 := by
        apply Units.ext
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [heckeLowerRepresentative, heckeLowerTranslation, mapGL_coe_matrix]
      simp [heckeLowerIndex, heckePrimeRepresentative, he]
    · have hC : ¬(p : ℤ) ∣ (heckeLowerRepresentative p Q hpQ (some x)).val 1 0 := by
        intro h
        have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr h
        have hn : (Q : ZMod p) * x ≠ 0 := mul_ne_zero (heckePrime_level_ne_zero hp hpQ) hx
        apply hn
        simpa [heckeLowerRepresentative, heckeLowerTranslation] using hz
      have h := cusp_slash_factor f (heckeLowerRepresentative p Q hpQ (some x)).val
        (heckePrime_lower_factor hp _ (heckeLowerRepresentative p Q hpQ (some x)).property hC)
      simpa [heckeLowerIndex, hx, heckePrimeRepresentative, heckeLowerRepresentative,
        heckeLowerTranslation] using h

/-- Summing the standard prime representatives gives the literal classical operator. -/
theorem heckePrimeRepresentative_sum {p Q : ℕ} [NeZero p] {k : ℤ}
    (hp : Nat.Prime p) (hpQ : Nat.Coprime p Q)
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) :
    ∑ x : Option (ZMod p), ⇑f ∣[k] heckePrimeRepresentative p x =
      classicalHeckeFunction Q k p f := by
  rw [← heckeUpperTrace_eq hp hpQ f]
  apply Finset.sum_congr rfl
  intro x _
  cases x with
  | none => exact (cusp_slash_factor f (heckeUpperRepresentative p Q hpQ none).val
      (heckeUpperMatrix_none hpQ)).symm
  | some x =>
    rw [← SlashAction.slash_mul, heckeUpperMatrix_some]
    rfl

/-- The adjugate lower trace is precisely the same good-prime classical Hecke operator. -/
theorem heckeLowerTrace_eq {p Q : ℕ} [NeZero p] {k : ℤ}
    (hp : Nat.Prime p) (hpQ : Nat.Coprime p Q)
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) :
    ∑ x : Option (ZMod p), (⇑f ∣[k] heckeTriangularMatrix p 1 0) ∣[k]
        mapGL ℝ (heckeLowerRepresentative p Q hpQ x).val =
      classicalHeckeFunction Q k p f := by
  simp only [heckeLowerTrace_term hp hpQ f]
  rw [← heckePrimeRepresentative_sum hp hpQ f]
  exact (heckeLowerIndexEquiv hp hpQ).sum_comp
    (fun x : Option (ZMod p) => (⇑f ∣[k] heckePrimeRepresentative p x))

end
end Dubon2026
