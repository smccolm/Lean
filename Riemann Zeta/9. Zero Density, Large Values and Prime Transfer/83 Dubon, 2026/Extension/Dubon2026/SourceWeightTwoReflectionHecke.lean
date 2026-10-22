import Dubon2026.SourceJHeckeCosets

/-! DUB-17/18 -> original parabolic Hecke eigensystem realization.
The reflected original coset sum differs termwise by explicit correction
values. Their total cancels by the original group action on the same finite
cosets. This proves reflection compatibility for the actual H1 Hecke action.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_Period_charInvolution_heckeOperatorHom.
-/
namespace Dubon2026
noncomputable section
open CongruenceSubgroup SourceJHecke
open scoped MatrixGroups BigOperators

theorem sourceWeightTwoHecke_sum_reflection (N : ℕ) (ell : sourceBinaryHeckePrime N)
    (φ : Additive (Gamma0 N) →+ ℂ) (g : Gamma0 N) :
    letI : NeZero ell.val := ⟨ell.property.1.ne_zero⟩
    letI := sourceHeckeUpperFintype N ell.val
    ∑ q : Gamma0 N ⧸ heckeUpperSubgroup N ell.val,
      φ (Additive.ofMul (sourceHeckeConjugation ell.property.1
        (cosetTransition (heckeUpperSubgroup N ell.val) (sourceJConjugateGamma0Hom N g) q))) =
    ∑ q : Gamma0 N ⧸ heckeUpperSubgroup N ell.val,
      φ (Additive.ofMul (sourceJConjugateGamma0Hom N
        (sourceHeckeConjugation ell.property.1 (cosetTransition (heckeUpperSubgroup N ell.val) g q)))) := by
  letI : NeZero ell.val := ⟨ell.property.1.ne_zero⟩
  letI := sourceHeckeUpperFintype N ell.val
  rw [← Equiv.sum_comp (quotientReflection N ell.val)
    (fun q => φ (Additive.ofMul (sourceHeckeConjugation ell.property.1
      (cosetTransition (heckeUpperSubgroup N ell.val) (sourceJConjugateGamma0Hom N g) q))))]
  have hterm (q : Gamma0 N ⧸ heckeUpperSubgroup N ell.val) :
      φ (Additive.ofMul (sourceHeckeConjugation ell.property.1
        (cosetTransition (heckeUpperSubgroup N ell.val) (sourceJConjugateGamma0Hom N g)
          (quotientReflection N ell.val q)))) =
        φ (Additive.ofMul (sourceHeckeConjugation ell.property.1 (correction N ell.val (g • q)))) +
        φ (Additive.ofMul (sourceJConjugateGamma0Hom N
          (sourceHeckeConjugation ell.property.1 (cosetTransition (heckeUpperSubgroup N ell.val) g q)))) -
        φ (Additive.ofMul (sourceHeckeConjugation ell.property.1 (correction N ell.val q))) := by
    rw [transition_reflection]
    simp only [map_mul, map_inv, sourceHeckeConjugation_reflection,
      ofMul_mul, ofMul_inv, map_add, map_neg]
    dsimp [sourceJConjugateGamma0Hom]
    abel
  rw [Finset.sum_congr rfl (fun q _ => hterm q), Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hcancel :
      (∑ q : Gamma0 N ⧸ heckeUpperSubgroup N ell.val,
        φ (Additive.ofMul (sourceHeckeConjugation ell.property.1 (correction N ell.val (g • q))))) =
      ∑ q : Gamma0 N ⧸ heckeUpperSubgroup N ell.val,
        φ (Additive.ofMul (sourceHeckeConjugation ell.property.1 (correction N ell.val q))) :=
    Equiv.sum_comp (MulAction.toPerm g)
      (fun q => φ (Additive.ofMul (sourceHeckeConjugation ell.property.1 (correction N ell.val q))))
  rw [hcancel]
  abel

theorem sourceWeightTwoPeriodReflection_hecke (N : ℕ) [NeZero N]
    (ell : sourceBinaryHeckePrime N) (φ : Additive (Gamma0 N) →+ ℂ) :
    sourceWeightTwoPeriodReflection N (sourceWeightTwoHeckeHom N ell φ) =
      sourceWeightTwoHeckeHom N ell (sourceWeightTwoPeriodReflection N φ) := by
  apply AddMonoidHom.ext
  intro γ
  change sourceWeightTwoHeckeHom N ell φ (Additive.ofMul (sourceJConjugateGamma0 N γ.toMul)) = _
  rw [show γ = Additive.ofMul γ.toMul from rfl, sourceWeightTwoHeckeHom_apply,
    sourceWeightTwoHeckeHom_apply]
  exact sourceWeightTwoHecke_sum_reflection N ell φ γ.toMul

end
end Dubon2026
