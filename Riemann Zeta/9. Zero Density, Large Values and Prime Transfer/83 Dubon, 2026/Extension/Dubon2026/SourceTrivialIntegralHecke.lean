import Dubon2026.SourceTrivialCoefficientHecke
import Dubon2026.SourceIntegralCohomologyFinite

/-! DUB-17/18 -> residual Galois association -> characteristic-zero
weight-two eigenvalue lifting -> the actual finite integral Hecke action.
The already proved full native correspondence and its commutativity are
used over Z and over fields. The field action is definitionally the
existing operator returned by all-prime weight-two reduction.
-/

namespace Dubon2026
noncomputable section
open CongruenceSubgroup groupCohomology
open scoped MatrixGroups

variable (R : Type) [CommRing R] (Q : ℕ)

/-- The same full original trivial-coefficient Hecke operator, including
the integral coefficient ring required for characteristic-zero lifting. -/
def sourceTrivialRingHeckeOperators :
    sourceBinaryHeckePrime Q → Module.End R (H1 (Rep.trivial R (Gamma0 Q) R)) :=
  fun ell =>
    letI : NeZero ell.val := ⟨ell.property.1.ne_zero⟩
    sourcePrimeHeckeH1 ell.property.1 (Rep.trivial R (Gamma0 Q) R) LinearMap.id
      (fun _ => rfl)

/-- On fields the integral construction is exactly the existing original
weight-two Hecke operator, with no normalization change. -/
theorem sourceTrivialRingHeckeOperators_field
    (F : Type) [Field F] (ell : sourceBinaryHeckePrime Q) :
    sourceTrivialRingHeckeOperators F Q ell =
      sourceTrivialCoefficientHeckeOperators F Q ell := rfl

/-- The full original trivial-coefficient H1 module is finite over each
Noetherian coefficient ring, including Z and C. -/
theorem sourceTrivialH1_finite [NeZero Q] [IsNoetherianRing R] :
    Module.Finite R (H1 (Rep.trivial R (Gamma0 Q) R)) := by
  letI : Group.FG SL(2, ℤ) :=
    Group.fg_iff.mpr ⟨{ModularGroup.S, ModularGroup.T},
      SpecialLinearGroup.SL2Z_generators, Set.toFinite _⟩
  exact sourceH1Finite (Rep.trivial R (Gamma0 Q) R)

/-- Every pair of original good-prime trivial-coefficient Hecke operators
commutes over the integral ring as well as over fields. -/
theorem sourceTrivialRingHeckeOperators_commute (ell ell' : sourceBinaryHeckePrime Q) :
    Commute (sourceTrivialRingHeckeOperators R Q ell)
      (sourceTrivialRingHeckeOperators R Q ell') := by
  by_cases he : ell.val = ell'.val
  · have : ell = ell' := Subtype.ext he
    subst ell'
    exact Commute.refl _
  · letI : NeZero ell.val := ⟨ell.property.1.ne_zero⟩
    letI : NeZero ell'.val := ⟨ell'.property.1.ne_zero⟩
    exact sourcePrimeHeckeH1_commute ell.property.1 (Rep.trivial R (Gamma0 Q) R)
      LinearMap.id (fun _ => rfl) ell'.property.1 ell.property.2 ell'.property.2 he
      LinearMap.id (fun _ => rfl) rfl

/-- Under the pinned native H1 identification, the original Hecke operator
is the complete original coset-transition sum. -/
theorem sourceTrivialRingHecke_hom_apply (ell : sourceBinaryHeckePrime Q)
    (x : H1 (Rep.trivial R (Gamma0 Q) R)) (γ : Gamma0 Q) :
    (H1IsoOfIsTrivial (Rep.trivial R (Gamma0 Q) R)).hom
        (sourceTrivialRingHeckeOperators R Q ell x) (Additive.ofMul γ) =
      letI : NeZero ell.val := ⟨ell.property.1.ne_zero⟩
      letI := sourceHeckeUpperFintype Q ell.val
      ∑ q : Gamma0 Q ⧸ heckeUpperSubgroup Q ell.val,
        (H1IsoOfIsTrivial (Rep.trivial R (Gamma0 Q) R)).hom x
          (Additive.ofMul (sourceHeckeConjugation ell.property.1
            (cosetTransition (heckeUpperSubgroup Q ell.val) γ q))) := by
  letI : NeZero ell.val := ⟨ell.property.1.ne_zero⟩
  letI := sourceHeckeUpperFintype Q ell.val
  induction x using H1_induction_on with
  | h z =>
    change (H1IsoOfIsTrivial (Rep.trivial R (Gamma0 Q) R)).hom
      (sourcePrimeHeckeH1 _ _ _ _ (H1π _ z)) (Additive.ofMul γ) = _
    rw [sourcePrimeHeckeH1_cocycle, H1IsoOfIsTrivial_H1π_apply_apply]
    change (∑ q : Gamma0 Q ⧸ heckeUpperSubgroup Q ell.val,
      z (sourceHeckeConjugation ell.property.1
        (cosetTransition (heckeUpperSubgroup Q ell.val) γ q))) = _
    apply Finset.sum_congr rfl
    intro q _
    exact (H1IsoOfIsTrivial_H1π_apply_apply z
      (Additive.ofMul (sourceHeckeConjugation ell.property.1
        (cosetTransition (heckeUpperSubgroup Q ell.val) γ q)))).symm

end
end Dubon2026
