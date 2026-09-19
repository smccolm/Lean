import Tao2026.BurgessWeilPrimeKummerLegendreCanonicalRoots

/-!
# Unconditional Legendre trace integrality

Every value of a complex multiplicative character on a finite field is zero
or a root of unity, hence an algebraic integer.  It follows directly that all
literal power-Legendre extension correlations, and therefore the canonical
trace coefficient, are algebraic integers without assuming a spectrum.

For the explicit monic quadratic, integrality of both canonical roots is then
equivalent to integrality of its determinant.  The reverse implication views
each root as integral over the integral closure of `ℤ` in `ℂ` and applies
transitivity.  Thus the remaining Legendre integrality condition is one
explicit coefficient assertion rather than a predicate on an abstract root
multiset.
-/

namespace Tao2026

open Finset Complex Polynomial
open scoped BigOperators ComplexConjugate

noncomputable section

/-- Every literal finite-field power-Legendre correlation is an algebraic
integer. -/
theorem isIntegral_finiteFieldPowerLegendreCorrelation
    (F : Type*) [Field F] [Fintype F]
    (α β γ : MulChar F ℂ) (t : F) :
    IsIntegral ℤ (finiteFieldPowerLegendreCorrelation F α β γ t) := by
  unfold finiteFieldPowerLegendreCorrelation
  exact IsIntegral.sum
    (fun x : F => α x * β (x - 1) * γ (x - t))
    (fun x _hx =>
      ((isIntegral_finiteFieldMulChar_apply α x).mul
        (isIntegral_finiteFieldMulChar_apply β (x - 1))).mul
          (isIntegral_finiteFieldMulChar_apply γ (x - t)))

/-- Every member of the literal power-Legendre extension-correlation sequence
is an algebraic integer, independently of any Frobenius spectrum. -/
theorem isIntegral_primePowerLegendreExtensionCorrelation
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (m n k : ℕ) (t : ZMod p) (q : ℕ) :
    IsIntegral ℤ (primePowerLegendreExtensionCorrelation p χ m n k t q) := by
  cases q with
  | zero =>
      exact isIntegral_finiteFieldPowerLegendreCorrelation
        (ZMod p) (χ ^ m) (χ ^ n) (χ ^ k) t
  | succ q =>
      let E := FiniteField.Extension (ZMod p) p (q + 2)
      letI : Fintype E := Fintype.ofFinite E
      letI : DecidableEq E := Classical.decEq E
      let χE := finiteFieldNormLiftMulChar (ZMod p) E χ
      change IsIntegral ℤ
        (finiteFieldPowerLegendreCorrelation E (χE ^ m) (χE ^ n) (χE ^ k)
          (algebraMap (ZMod p) E t))
      exact isIntegral_finiteFieldPowerLegendreCorrelation
        E (χE ^ m) (χE ^ n) (χE ^ k) (algebraMap (ZMod p) E t)

/-- The correlation-determined characteristic trace is unconditionally an
algebraic integer. -/
theorem primePowerLegendreCharacteristicTrace_integral_unconditional
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (m n k : ℕ) (t : ZMod p) :
    IsIntegral ℤ (primePowerLegendreCharacteristicTrace p χ m n k t) := by
  exact (isIntegral_primePowerLegendreExtensionCorrelation
    p χ m n k t 0).neg

/-- Since the canonical trace is already integral, both roots of the explicit
quadratic are integral exactly when its determinant coefficient is integral. -/
theorem integral_primePowerLegendreCanonicalEigenvalues_iff_characteristicDeterminant
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (m n k : ℕ) (t : ZMod p) :
    (∀ a ∈ primePowerLegendreCanonicalEigenvalues p χ m n k t,
        IsIntegral ℤ a) ↔
      IsIntegral ℤ
        (primePowerLegendreCharacteristicDeterminant p χ m n k t) := by
  constructor
  · intro h
    rw [← prod_primePowerLegendreCanonicalEigenvalues p χ m n k t]
    exact IsIntegral.multiset_prod h
  · intro hdet a ha
    let T := integralClosure ℤ ℂ
    let tr : T := ⟨primePowerLegendreCharacteristicTrace p χ m n k t,
      primePowerLegendreCharacteristicTrace_integral_unconditional p χ m n k t⟩
    let det : T := ⟨primePowerLegendreCharacteristicDeterminant p χ m n k t,
      hdet⟩
    let f : T[X] := X ^ 2 - C tr * X + C det
    have hfmonic : f.Monic := by
      unfold f
      exact isMonicOfDegree_sub_add_two _ _ |>.monic
    have ha0 :
        (primePowerLegendreCharacteristicPolynomial p χ m n k t).eval a = 0 := by
      exact (mem_roots
        (primePowerLegendreCharacteristicPolynomial_monic p χ m n k t).ne_zero).mp ha
    have hfa : aeval a f = 0 := by
      simpa [f, tr, det, aeval_def,
        primePowerLegendreCharacteristicPolynomial] using ha0
    exact isIntegral_trans a ⟨f, hfmonic, hfa⟩

/-- The exact remaining canonical Legendre conditions with root integrality
compressed to the single explicit determinant coefficient. -/
def PrimePowerLegendreCanonicalDeterminantConditions
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (m n k : ℕ) (t : ZMod p) : Prop :=
  IsIntegral ℤ
      (primePowerLegendreCharacteristicDeterminant p χ m n k t) ∧
  (∀ a ∈ primePowerLegendreCanonicalEigenvalues p χ m n k t,
      ‖a‖ ≤ Real.sqrt p) ∧
  ∀ q : ℕ,
    primePowerLegendreExtensionCorrelation p χ m n k t (q + 2) =
      primePowerLegendreCharacteristicTrace p χ m n k t *
          primePowerLegendreExtensionCorrelation p χ m n k t (q + 1) -
        primePowerLegendreCharacteristicDeterminant p χ m n k t *
          primePowerLegendreExtensionCorrelation p χ m n k t q

theorem primePowerLegendreCanonicalConditions_iff_determinantConditions
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (m n k : ℕ) (t : ZMod p) :
    PrimePowerLegendreCanonicalConditions p χ m n k t ↔
      PrimePowerLegendreCanonicalDeterminantConditions p χ m n k t := by
  unfold PrimePowerLegendreCanonicalConditions
    PrimePowerLegendreCanonicalDeterminantConditions
  rw [integral_primePowerLegendreCanonicalEigenvalues_iff_characteristicDeterminant]

theorem nonempty_primePowerLegendreSpectrum_iff_canonicalDeterminantConditions
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {m n k : ℕ} {t : ZMod p} :
    Nonempty (PrimePowerLegendreSpectrum p χ m n k t) ↔
      PrimePowerLegendreCanonicalDeterminantConditions p χ m n k t := by
  rw [nonempty_primePowerLegendreSpectrum_iff_canonicalConditions,
    primePowerLegendreCanonicalConditions_iff_determinantConditions]

/-- The global Legendre source stated using only determinant integrality,
canonical-root weights, and the explicit recurrence. -/
def TaoPrimePowerLegendreCanonicalDeterminantConditions : Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (m n k : ℕ) (t : ZMod p),
    χ ≠ 1 → 0 < m → 0 < n → 0 < k →
      m < orderOf χ → n < orderOf χ → k < orderOf χ →
      t ≠ 0 → t ≠ 1 → ¬orderOf χ ∣ m + n + k →
        PrimePowerLegendreCanonicalDeterminantConditions p χ m n k t

theorem taoPrimePowerLegendreCanonicalConditions_iff_determinantConditions :
    TaoPrimePowerLegendreCanonicalConditions ↔
      TaoPrimePowerLegendreCanonicalDeterminantConditions := by
  constructor
  · intro h p _ _ χ m n k t hχ hm hn hk hmred hnred hkred ht0 ht1 hsum
    exact (primePowerLegendreCanonicalConditions_iff_determinantConditions
      p χ m n k t).mp
        (h p χ m n k t hχ hm hn hk hmred hnred hkred ht0 ht1 hsum)
  · intro h p _ _ χ m n k t hχ hm hn hk hmred hnred hkred ht0 ht1 hsum
    exact (primePowerLegendreCanonicalConditions_iff_determinantConditions
      p χ m n k t).mpr
        (h p χ m n k t hχ hm hn hk hmred hnred hkred ht0 ht1 hsum)

theorem taoPrimePowerLegendreSpectrum_iff_canonicalDeterminantConditions :
    TaoPrimePowerLegendreSpectrum ↔
      TaoPrimePowerLegendreCanonicalDeterminantConditions := by
  rw [taoPrimePowerLegendreSpectrum_iff_canonicalConditions,
    taoPrimePowerLegendreCanonicalConditions_iff_determinantConditions]

/-- The complete residual after removing both the abstract Legendre spectrum
and its redundant root-integrality predicate. -/
def TaoPrimeCanonicalDeterminantLegendreAndRootMultisetSpectra : Prop :=
  TaoPrimePowerLegendreCanonicalDeterminantConditions ∧
    TaoPrimeKummerExplicitRootMultisetSpectrumFourRootsOrMore

theorem taoPrimeCanonicalLegendreAndRootMultisetSpectra_iff_determinant :
    TaoPrimeCanonicalLegendreAndRootMultisetSpectra ↔
      TaoPrimeCanonicalDeterminantLegendreAndRootMultisetSpectra := by
  rw [TaoPrimeCanonicalLegendreAndRootMultisetSpectra,
    TaoPrimeCanonicalDeterminantLegendreAndRootMultisetSpectra,
    taoPrimePowerLegendreCanonicalConditions_iff_determinantConditions]

theorem TaoPrimeCanonicalDeterminantLegendreAndRootMultisetSpectra.toFull
    (h : TaoPrimeCanonicalDeterminantLegendreAndRootMultisetSpectra) :
    TaoPrimeKummerIsotypicFrobeniusSystem :=
  TaoPrimeCanonicalLegendreAndRootMultisetSpectra.toFull
    (taoPrimeCanonicalLegendreAndRootMultisetSpectra_iff_determinant.mpr h)

end
end Tao2026
