import Dubon2026.PrincipalCongruenceQuotient
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Algebra.Group.Pi.Lemmas

/-! # Actual prime-power factors of the finite principal congruence action -/

namespace Dubon2026

open Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

noncomputable section
attribute [local instance] principalNormal

/-- Determinant-one matrices over a product of rings are exactly families of determinant-one matrices. -/
def sl2PiEquiv {I : Type*} (R : I → Type*) [∀ i, CommRing (R i)] :
    SL(2, ∀ i, R i) ≃* ∀ i, SL(2, R i) where
  toFun g i := Matrix.SpecialLinearGroup.map (Pi.evalRingHom R i) g
  invFun g := ⟨fun a b i => g i a b, by
    funext i
    simpa only [Matrix.det_fin_two, Pi.sub_apply, Pi.mul_apply, Pi.one_apply] using (g i).property⟩
  left_inv g := by ext a b i; rfl
  right_inv g := by funext i; ext a b; rfl
  map_mul' g h := by
    funext i
    exact (Matrix.SpecialLinearGroup.map (Pi.evalRingHom R i)).map_mul g h

/-- Chinese remaindering decomposes the full finite matrix group into all prime-power factors. -/
def sl2PrimeFactorsEquiv (N : ℕ) [NeZero N] :
    SL(2, ZMod N) ≃* ∀ p : N.primeFactors, SL(2, ZMod (p.val ^ N.factorization p.val)) :=
  (sl2RingEquiv (ZMod.equivPi N (NeZero.ne N))).trans (sl2PiEquiv _)

/-- The actual principal congruence quotient has precisely these prime-power matrix factors. -/
def principalPrimeFactorsEquiv (N : ℕ) [NeZero N] :
    (SL(2, ℤ) ⧸ Gamma N) ≃*
      ∀ p : N.primeFactors, SL(2, ZMod (p.val ^ N.factorization p.val)) :=
  (principalCongruenceEquiv N).trans (sl2PrimeFactorsEquiv N)

/-- The canonical embedding of a single genuine local matrix factor into the principal quotient. -/
def principalPrimeFactorEmbedding (N : ℕ) [NeZero N] (p : N.primeFactors) :
    SL(2, ZMod (p.val ^ N.factorization p.val)) →* (SL(2, ℤ) ⧸ Gamma N) :=
  (principalPrimeFactorsEquiv N).symm.toMonoidHom.comp (MonoidHom.mulSingle (fun q : N.primeFactors => SL(2, ZMod (q.val ^ N.factorization q.val))) p)

/-- The embedded local element has exactly its given component and identity elsewhere. -/
theorem principalPrimeFactorEmbedding_components (N : ℕ) [NeZero N] (p : N.primeFactors)
    (g : SL(2, ZMod (p.val ^ N.factorization p.val))) :
    principalPrimeFactorsEquiv N (principalPrimeFactorEmbedding N p g) = Pi.mulSingle p g := by
  exact (principalPrimeFactorsEquiv N).apply_symm_apply _

/-- Distinct actual prime factors commute inside the principal congruence quotient. -/
theorem principalPrimeFactorEmbedding_commute (N : ℕ) [NeZero N]
    (p q : N.primeFactors) (hpq : p ≠ q)
    (g : SL(2, ZMod (p.val ^ N.factorization p.val)))
    (h : SL(2, ZMod (q.val ^ N.factorization q.val))) :
    Commute (principalPrimeFactorEmbedding N p g) (principalPrimeFactorEmbedding N q h) := by
  have hs : Commute
      (Pi.mulSingle (M := fun t : N.primeFactors => SL(2, ZMod (t.val ^ N.factorization t.val))) p g)
      (Pi.mulSingle q h) := Pi.mulSingle_commute
        (f := fun t : N.primeFactors => SL(2, ZMod (t.val ^ N.factorization t.val))) hpq g h
  change Commute ((principalPrimeFactorsEquiv N).symm (Pi.mulSingle p g))
    ((principalPrimeFactorsEquiv N).symm (Pi.mulSingle q h))
  exact hs.map (principalPrimeFactorsEquiv N).symm.toMonoidHom

/-- Restriction of the actual finite slash-orbit representation to one prime-power factor. -/
def principalPrimeFactorOrbitRepresentation (N : ℕ) [NeZero N] (k : ℤ)
    (f : CuspForm ((Gamma N).map (mapGL ℝ)) k) (p : N.primeFactors) :
    Representation ℂ SL(2, ZMod (p.val ^ N.factorization p.val)) (principalCuspOrbit N k f) :=
  (principalCuspOrbitRepresentation N k f).comp (principalPrimeFactorEmbedding N p)

/-- Operators belonging to different local matrix factors commute on the genuine finite cusp orbit. -/
theorem principalPrimeFactorOrbit_commute (N : ℕ) [NeZero N] (k : ℤ)
    (f : CuspForm ((Gamma N).map (mapGL ℝ)) k) (p q : N.primeFactors) (hpq : p ≠ q)
    (g : SL(2, ZMod (p.val ^ N.factorization p.val)))
    (h : SL(2, ZMod (q.val ^ N.factorization q.val))) :
    Commute (principalPrimeFactorOrbitRepresentation N k f p g)
      (principalPrimeFactorOrbitRepresentation N k f q h) :=
  (principalPrimeFactorEmbedding_commute N p q hpq g h).map (principalCuspOrbitRepresentation N k f)

end
end Dubon2026
