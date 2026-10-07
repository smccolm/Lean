import Dubon2026.PrimitiveCuspForms
import Dubon2026.CharacterCoefficients

/-! # Character self-twists of actual cusp coefficients

For weights at least two, non-CM is expressed by the standard absence of a
nontrivial primitive quadratic self-twist at the primes away from both levels.
See Sutherland, MIT 18.786 (2024), Lecture 15, and LMFDB knowl mf.cm.
This is an actual character/coefficient condition. No equidistribution, energy
estimate or Galois representation is assumed in it. The conductor restriction
for a self-twist and the automorphic specialization remain separate obligations.
-/

namespace Dubon2026

open Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups ModularForm

noncomputable section

/-- Equality with a character twist at every prime away from the two levels. -/
def IsCoefficientSelfTwist (Q : ℕ) {D : ℕ} (χ : DirichletCharacter ℂ D)
    (a : ℕ → ℂ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → Nat.Coprime p (Q * D) → characterCoefficients χ p * a p = a p

/-- The classical non-CM condition on the actual Fourier coefficients,
using nontrivial primitive quadratic characters rather than an analytic proxy. -/
def IsNonCMCuspForm {Q : ℕ} {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) : Prop :=
  ¬ ∃ (D : ℕ+) (χ : DirichletCharacter ℂ D),
    χ.IsPrimitive ∧ χ ≠ 1 ∧ χ.IsQuadratic ∧ IsCoefficientSelfTwist Q χ (cuspCoefficients f)

/-- A non-CM primitive cusp form, with no deep arithmetic estimates in its fields. -/
structure NonCMPrimitiveCuspForm (Q : ℕ) [NeZero Q] (k : ℤ)
    extends PrimitiveCuspForm Q k where
  /-- Absence of a nontrivial primitive quadratic coefficient self-twist. -/
  nonCM : IsNonCMCuspForm toPrimitiveCuspForm.toCuspForm

/-- The underlying genuine primitive cusp form. -/
add_decl_doc NonCMPrimitiveCuspForm.toPrimitiveCuspForm

/-- At an inert good prime, a self-twist forces the actual coefficient to vanish. -/
theorem coefficientSelfTwist_inert_zero {Q D : ℕ} {χ : DirichletCharacter ℂ D}
    {a : ℕ → ℂ} (h : IsCoefficientSelfTwist Q χ a) {p : ℕ} (hp : Nat.Prime p)
    (hpQD : Nat.Coprime p (Q * D)) (hχp : characterCoefficients χ p = -1) : a p = 0 := by
  have he := h p hp hpQD
  rw [hχp, neg_one_mul] at he
  linear_combination -(1 / 2 : ℂ) * he

/-- For a quadratic character, the prime self-twist condition is exactly inert-prime vanishing. -/
theorem coefficientSelfTwist_iff_inert_zero {Q D : ℕ} (χ : DirichletCharacter ℂ D)
    (hχ : χ.IsQuadratic) (a : ℕ → ℂ) :
    IsCoefficientSelfTwist Q χ a ↔ ∀ p, Nat.Prime p → Nat.Coprime p (Q * D) →
      characterCoefficients χ p = -1 → a p = 0 := by
  constructor
  · exact fun h p hp hpQD hχp => coefficientSelfTwist_inert_zero h hp hpQD hχp
  · intro h p hp hpQD
    have hpD : Nat.Coprime p D := (Nat.coprime_mul_iff_right.mp hpQD).2
    rcases hχ (p : ZMod D) with hz | ho | hm
    · have hn := norm_characterCoefficients_of_coprime χ hpD
      change characterCoefficients χ p = 0 at hz
      rw [hz, norm_zero] at hn
      exact (zero_ne_one hn).elim
    · change characterCoefficients χ p = 1 at ho
      rw [ho, one_mul]
    · have ha := h p hp hpQD hm
      rw [ha, mul_zero]

/-- Positive real coefficient rescaling preserves and reflects every prime self-twist. -/
theorem coefficientSelfTwist_shift_iff (Q : ℕ) {D : ℕ} (χ : DirichletCharacter ℂ D)
    (a : ℕ → ℂ) (c : ℝ) :
    IsCoefficientSelfTwist Q χ (shiftedCoefficients a c) ↔ IsCoefficientSelfTwist Q χ a := by
  constructor
  · intro h p hp hpQD
    have hw : (p : ℂ) ^ (c : ℂ) ≠ 0 := Complex.cpow_ne_zero_iff.mpr
      (Or.inl (Nat.cast_ne_zero.mpr hp.ne_zero))
    apply mul_right_cancel₀ hw
    simpa only [shiftedCoefficients, mul_assoc] using h p hp hpQD
  · intro h p hp hpQD
    simp only [shiftedCoefficients, ← mul_assoc, h p hp hpQD]

/-- Classical and automorphic normalization give exactly the same self-twist condition. -/
theorem cusp_selfTwist_normalization_iff {Q D : ℕ} {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (χ : DirichletCharacter ℂ D) :
    IsCoefficientSelfTwist Q χ (normalizedCuspCoefficients f) ↔
      IsCoefficientSelfTwist Q χ (cuspCoefficients f) :=
  coefficientSelfTwist_shift_iff Q χ (cuspCoefficients f) (-((k : ℝ) - 1) / 2)

end
end Dubon2026
