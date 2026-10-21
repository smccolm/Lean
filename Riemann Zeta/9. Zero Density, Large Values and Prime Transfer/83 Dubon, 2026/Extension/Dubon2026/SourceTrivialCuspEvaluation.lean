import Dubon2026.SourceTrivialCuspHecke
import Dubon2026.SourceGamma0CuspFunctional

/-! The actual cusp-evaluation quotient of native trivial-coefficient H1.
DUB-17/18 -> residual modular Galois association -> character-to-weight-two
reduction -> removal of the Eisenstein exception -> an actual nonzero
Hecke quotient with eigenvalues ell+1. Pinned native trivial-coefficient H1
identification supplies the evaluation map; its nonzero value and full
Hecke action are derived from the original objects.
-/

namespace Dubon2026
noncomputable section
open CongruenceSubgroup groupCohomology CategoryTheory

variable (F : Type) [Field F] (Q : ℕ)

/-- Evaluate the original trivial-coefficient H1 class on the actual unit translation. -/
def sourceTrivialCuspEvaluation :
    H1 (Rep.trivial F (Gamma0 Q) F) →ₗ[F] F where
  toFun x := (H1IsoOfIsTrivial (Rep.trivial F (Gamma0 Q) F)).hom x
    (Additive.ofMul (heckeUpperTranslation Q 1))
  map_add' x y := by simp
  map_smul' r x := by simp

/-- Actual cusp evaluation on a native class is its literal cocycle value. -/
theorem sourceTrivialCuspEvaluation_cocycle
    (z : cocycles₁ (Rep.trivial F (Gamma0 Q) F)) :
    sourceTrivialCuspEvaluation F Q (H1π _ z) = z (heckeUpperTranslation Q 1) :=
  H1IsoOfIsTrivial_H1π_apply_apply _ _

/-- At every actual level at least two, the original cusp evaluation takes the value one. -/
theorem sourceTrivialCuspEvaluation_one (hQ : 2 ≤ Q) :
    ∃ x : H1 (Rep.trivial F (Gamma0 Q) F), sourceTrivialCuspEvaluation F Q x = 1 := by
  obtain ⟨φ, hφ⟩ := sourceGamma0_exists_translation_hom Q F hQ
  refine ⟨(H1IsoOfIsTrivial (Rep.trivial F (Gamma0 Q) F)).inv φ, ?_⟩
  change (H1IsoOfIsTrivial (Rep.trivial F (Gamma0 Q) F)).hom
    ((H1IsoOfIsTrivial (Rep.trivial F (Gamma0 Q) F)).inv φ)
      (Additive.ofMul (heckeUpperTranslation Q 1)) = 1
  simpa using hφ

/-- Every original good-prime Hecke operator acts on cusp evaluation by its exact scalar ell+1. -/
theorem sourceTrivialCuspEvaluation_hecke (ell : sourceBinaryHeckePrime Q)
    (x : H1 (Rep.trivial F (Gamma0 Q) F)) :
    sourceTrivialCuspEvaluation F Q (sourceTrivialCoefficientHeckeOperators F Q ell x) =
      ((ell.val : F) + 1) * sourceTrivialCuspEvaluation F Q x := by
  letI : NeZero ell.val := ⟨ell.property.1.ne_zero⟩
  induction x using H1_induction_on with
  | h z =>
    change sourceTrivialCuspEvaluation F Q (sourcePrimeHeckeH1 _ _ _ _ (H1π _ z)) = _
    rw [sourcePrimeHeckeH1_cocycle, sourceTrivialCuspEvaluation_cocycle,
      sourceTrivialCuspEvaluation_cocycle]
    exact sourceTrivialCoefficientHecke_translation F Q ell.val ell.property.1 ell.property.2 z

end
end Dubon2026
