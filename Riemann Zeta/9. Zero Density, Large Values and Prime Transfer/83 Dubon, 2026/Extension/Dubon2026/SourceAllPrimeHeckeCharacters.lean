import Dubon2026.SourceTrivialIntegralHecke
import Dubon2026.SourceWeightTwoScalarHecke

/-! DUB-17/18 -> rational rank-two Hecke algebra descent -> a rational
character realization of every prime operator. Reuse the existing actual
native H1 correspondence and its complete coset-transition formula. The
construction itself requires primality, with no coprimality-to-level
premise. Only the operator family needed for rational descent is extended.
-/
namespace Dubon2026
noncomputable section
open CongruenceSubgroup groupCohomology
open scoped MatrixGroups
private local instance (ell : Nat.Primes) : NeZero ell.val := ⟨ell.property.ne_zero⟩
section Ring
variable (R : Type) [CommRing R] (Q : ℕ)
/-- The same full original trivial-coefficient Hecke operator, including
the integral coefficient ring required for characteristic-zero lifting. -/
def sourceAllPrimeRingHeckeOperators :
    Nat.Primes → Module.End R (H1 (Rep.trivial R (Gamma0 Q) R)) :=
  fun ell =>
    letI : NeZero ell.val := ⟨ell.property.ne_zero⟩
    sourcePrimeHeckeH1 ell.property (Rep.trivial R (Gamma0 Q) R) LinearMap.id
      (fun _ => rfl)

/-- Under the pinned native H1 identification, the original Hecke operator
is the complete original coset-transition sum. -/
theorem sourceAllPrimeRingHecke_hom_apply (ell : Nat.Primes)
    (x : H1 (Rep.trivial R (Gamma0 Q) R)) (γ : Gamma0 Q) :
    (H1IsoOfIsTrivial (Rep.trivial R (Gamma0 Q) R)).hom
        (sourceAllPrimeRingHeckeOperators R Q ell x) (Additive.ofMul γ) =
      letI : NeZero ell.val := ⟨ell.property.ne_zero⟩
      letI := sourceHeckeUpperFintype Q ell.val
      ∑ q : Gamma0 Q ⧸ heckeUpperSubgroup Q ell.val,
        (H1IsoOfIsTrivial (Rep.trivial R (Gamma0 Q) R)).hom x
          (Additive.ofMul (sourceHeckeConjugation ell.property
            (cosetTransition (heckeUpperSubgroup Q ell.val) γ q))) := by
  letI : NeZero ell.val := ⟨ell.property.ne_zero⟩
  letI := sourceHeckeUpperFintype Q ell.val
  induction x using H1_induction_on with
  | h z =>
    change (H1IsoOfIsTrivial (Rep.trivial R (Gamma0 Q) R)).hom
      (sourcePrimeHeckeH1 _ _ _ _ (H1π _ z)) (Additive.ofMul γ) = _
    rw [sourcePrimeHeckeH1_cocycle, H1IsoOfIsTrivial_H1π_apply_apply]
    change (∑ q : Gamma0 Q ⧸ heckeUpperSubgroup Q ell.val,
      z (sourceHeckeConjugation ell.property
        (cosetTransition (heckeUpperSubgroup Q ell.val) γ q))) = _
    apply Finset.sum_congr rfl
    intro q _
    exact (H1IsoOfIsTrivial_H1π_apply_apply z
      (Additive.ofMul (sourceHeckeConjugation ell.property
        (cosetTransition (heckeUpperSubgroup Q ell.val) γ q)))).symm

end Ring

/-- The original trivial-coefficient Hecke operator on native additive characters. -/
def sourceAllPrimeHeckeHom (R : Type) [CommRing R] (N : ℕ) (ell : Nat.Primes) :
    Module.End R (Additive (Gamma0 N) →+ R) :=
  (H1IsoOfIsTrivial (Rep.trivial R (Gamma0 N) R)).hom.hom.comp
    ((sourceAllPrimeRingHeckeOperators R N ell).comp
      (H1IsoOfIsTrivial (Rep.trivial R (Gamma0 N) R)).inv.hom)

theorem sourceAllPrimeHeckeHom_apply (R : Type) [CommRing R] (N : ℕ) (ell : Nat.Primes)
    (φ : Additive (Gamma0 N) →+ R) (γ : Gamma0 N) :
    sourceAllPrimeHeckeHom R N ell φ (Additive.ofMul γ) =
      letI : NeZero ell.val := ⟨ell.property.ne_zero⟩
      letI := sourceHeckeUpperFintype N ell.val
      ∑ q : Gamma0 N ⧸ heckeUpperSubgroup N ell.val,
        φ (Additive.ofMul (sourceHeckeConjugation ell.property
          (cosetTransition (heckeUpperSubgroup N ell.val) γ q))) := by
  letI : NeZero ell.val := ⟨ell.property.ne_zero⟩
  letI := sourceHeckeUpperFintype N ell.val
  change (H1IsoOfIsTrivial (Rep.trivial R (Gamma0 N) R)).hom
    (sourceAllPrimeRingHeckeOperators R N ell
      ((H1IsoOfIsTrivial (Rep.trivial R (Gamma0 N) R)).inv φ)) (Additive.ofMul γ) = _
  rw [sourceAllPrimeRingHecke_hom_apply]
  simp only [CategoryTheory.Iso.inv_hom_id_apply]


end
end Dubon2026
