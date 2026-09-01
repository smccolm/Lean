import GafniTao.FordShiftedBinomial
import GafniTao.FordEquation37S6

/-!
# Ford equations (3.5)--(3.7): the interior collision consumer

The exact interior part of `S₄(c,p)` is embedded here into the actual `S₆`
collision type.  The translated system uses the scaled parameter `q*a`, and
the proof consumes the literal binomial identities rather than identifying
the two counts by an unrelated cardinality estimate.
-/

namespace GafniTao

noncomputable section

theorem fordPrimeReduction_natCast
    {p r : ℕ} [NeZero p] (hr : 0 < r) (n : ℕ) :
    fordPrimeReduction ((n : ℕ) : ZMod (p ^ r)) = (n : ZMod p) := by
  letI : NeZero (p ^ r) := ⟨pow_ne_zero r (NeZero.ne p)⟩
  exact ZMod.cast_natCast (dvd_pow_self p hr.ne') n

def fordS4InteriorHalfToS6
    {k d P p s Q r : ℕ} [NeZero p] (hdk : d ≤ k)
    (hr : 0 < r)
    (z : FordS3PolynomialBox k d P p hdk × FordS4InteriorTuple s Q p) :
    FordS6Half k d s P (Q / p) p r hdk := by
  refine ⟨(z.1.1, z.2), ?_⟩
  intro i i' hii'
  apply z.1.property
  simpa only [fordPrimeReduction_natCast hr] using hii'

theorem fordS4InteriorHalfToS6_injective
    {k d P p s Q r : ℕ} [NeZero p] (hdk : d ≤ k) (hr : 0 < r) :
    Function.Injective
      (fordS4InteriorHalfToS6 (P := P) (p := p) (s := s) (Q := Q)
        (r := r) hdk hr) := by
  intro z w hzw
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg (fun v : FordS6Half k d s P (Q / p) p r hdk ↦
      v.1.1) hzw
  · exact congrArg (fun v : FordS6Half k d s P (Q / p) p r hdk ↦
      v.1.2) hzw

def fordS4InteriorCombinedMoment
    {k d T P p s Q : ℕ} [NeZero p]
    (Ψ : FordIntegerPolynomialSystem k d T) (hdk : d ≤ k)
    (q : ℕ) (c : ZMod p)
    (z : FordS3PolynomialBox k d P p hdk × FordS4InteriorTuple s Q p) :
    Fin k → ℤ :=
  fordS4PolynomialMoment Ψ hdk z.1 + fordS4InteriorMoment q c z.2

def fordS4TranslationScale {p : ℕ} (q : ℕ) (c : ZMod p) : ℤ :=
  (q : ℤ) * (fordNegativeResidue p c : ℤ)

def fordS4TranslationConstant {k s p : ℕ} (q : ℕ) (c : ZMod p) :
    Fin k → ℤ :=
  fun j ↦ ∑ _i : Fin s,
    fordS4TranslationScale q c ^ ((j : ℕ) + 1)

theorem fordS4InteriorHalfToS6_moment
    {k d T P p s Q q r : ℕ} [NeZero p]
    (Ψ : FordIntegerPolynomialSystem k d T) (hdk : d ≤ k)
    (hr : 0 < r) (c : ZMod p)
    (z : FordS3PolynomialBox k d P p hdk × FordS4InteriorTuple s Q p) :
    fordS6Moment (p := p) (q := q)
        (fordBinomialTranslateSystem Ψ (fordS4TranslationScale q c))
        (fordS4InteriorHalfToS6 (r := r) hdk hr z).1 =
      fordMomentBinomialTransform (fordS4TranslationScale q c)
          (fordS4InteriorCombinedMoment Ψ hdk q c z) +
        fordS4TranslationConstant (k := k) (s := s) q c := by
  funext j
  unfold fordS6Moment fordS4InteriorCombinedMoment
    fordS4TranslationConstant fordS4TranslationScale
  simp only [Pi.add_apply]
  rw [fordPolynomialSumInt_translate]
  change fordMomentBinomialTransform
        ((q : ℤ) * (fordNegativeResidue p c : ℤ))
          (fordS4PolynomialMoment Ψ hdk z.1) j +
      ((p * q : ℕ) : ℤ) ^ ((j : ℕ) + 1) *
        fordPowerSumInt z.2 ((j : ℕ) + 1) = _
  rw [← fordS4InteriorMoment_transform q c z.2 j]
  have hadd := congrFun
    (map_add (fordMomentBinomialTransformHom
      ((q : ℤ) * (fordNegativeResidue p c : ℤ)))
      (fordS4PolynomialMoment Ψ hdk z.1)
      (fordS4InteriorMoment q c z.2)) j
  simp only [fordMomentBinomialTransformHom_apply, Pi.add_apply] at hadd
  rw [hadd]
  ring

def fordS4InteriorCollisionToS6
    {k d T P p s Q q r : ℕ} [NeZero p]
    (Ψ : FordIntegerPolynomialSystem k d T) (hdk : d ≤ k)
    (hr : 0 < r) (c : ZMod p)
    (u : FordCharacterCollision
      (fordS4PolynomialMoment (P := P) (p := p) Ψ hdk)
      (fordS4InteriorMoment (k := k) q c :
        FordS4InteriorTuple s Q p → Fin k → ℤ)) :
    FordCollisionPairs
      (fun z : FordS6Half k d s P (Q / p) p r hdk ↦
        fordS6Moment (p := p) (q := q)
          (fordBinomialTranslateSystem Ψ (fordS4TranslationScale q c)) z.1) := by
  refine ⟨(fordS4InteriorHalfToS6 (r := r) hdk hr u.val.1,
    fordS4InteriorHalfToS6 (r := r) hdk hr u.val.2), ?_⟩
  change fordS6Moment (p := p) (q := q)
      (fordBinomialTranslateSystem Ψ (fordS4TranslationScale q c))
        (fordS4InteriorHalfToS6 (r := r) hdk hr u.val.1).1 =
    fordS6Moment (p := p) (q := q)
      (fordBinomialTranslateSystem Ψ (fordS4TranslationScale q c))
        (fordS4InteriorHalfToS6 (r := r) hdk hr u.val.2).1
  rw [fordS4InteriorHalfToS6_moment Ψ hdk hr c,
    fordS4InteriorHalfToS6_moment Ψ hdk hr c]
  unfold fordS4InteriorCombinedMoment
  rw [u.property]

theorem fordS4InteriorCollisionToS6_injective
    {k d T P p s Q q r : ℕ} [NeZero p]
    (Ψ : FordIntegerPolynomialSystem k d T) (hdk : d ≤ k)
    (hr : 0 < r) (c : ZMod p) :
    Function.Injective
      (fordS4InteriorCollisionToS6 (P := P) (s := s) (Q := Q) (q := q)
        (r := r) Ψ hdk hr c) := by
  intro u v huv
  apply Subtype.ext
  apply Prod.ext
  · exact fordS4InteriorHalfToS6_injective hdk hr
      (congrArg (fun w ↦ w.val.1) huv)
  · exact fordS4InteriorHalfToS6_injective hdk hr
      (congrArg (fun w ↦ w.val.2) huv)

theorem fordS4InteriorCount_le_S6
    {k d T P p s Q q r : ℕ} [NeZero p]
    (Ψ : FordIntegerPolynomialSystem k d T) (hdk : d ≤ k)
    (hr : 0 < r) (c : ZMod p) :
    fordS4InteriorCount (P := P) Ψ hdk s Q q c ≤
      fordS6Count Ψ (fordS4TranslationScale q c)
        s P (Q / p) p q r hdk := by
  unfold fordS4InteriorCount fordS6Count
  letI : Finite (FordS6Half k d s P (Q / p) p r hdk) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Finite (FordCollisionPairs
      (fun z : FordS6Half k d s P (Q / p) p r hdk ↦
        fordS6Moment (p := p) (q := q)
          (fordBinomialTranslateSystem Ψ (fordS4TranslationScale q c)) z.1)) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Nat.card_le_card_of_injective
    (fordS4InteriorCollisionToS6 Ψ hdk hr c)
    (fordS4InteriorCollisionToS6_injective Ψ hdk hr c)

#print axioms fordPrimeReduction_natCast
#print axioms fordS4InteriorHalfToS6_moment
#print axioms fordS4InteriorCount_le_S6

end

end GafniTao
