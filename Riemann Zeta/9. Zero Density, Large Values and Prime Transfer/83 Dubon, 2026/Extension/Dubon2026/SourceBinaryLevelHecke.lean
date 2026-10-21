import Dubon2026.SourceLevelHeckeRepresentatives
import Dubon2026.SourceBinaryLevelRestriction
import Dubon2026.SourceBinaryHeckeCohomology
import Dubon2026.SourceCorrespondenceOne

/-! The original binary H1 restriction preserves full good-prime Hecke actions.
DUB-17/18 -> residual modular Galois association -> weight/level reduction
-> level raising with the original eigenvalues. The exact coset equivalence
and chosen representatives reduce the comparison to the already proved
native coboundary correction for the genuine full prime correspondence.
-/

namespace Dubon2026
noncomputable section
open CongruenceSubgroup

variable (F : Type) [Field F] (Q p n : ℕ) {ell : ℕ} [NeZero ell]
    (hell : ell.Prime) (hellQp : Nat.Coprime ell (Q * p))

private local instance levelHeckeOldFinite :
    Fintype (Gamma0 Q ⧸ heckeUpperSubgroup Q ell) := sourceHeckeUpperFintype Q ell

private local instance levelHeckeNewFinite :
    Fintype (Gamma0 (Q * p) ⧸ heckeUpperSubgroup (Q * p) ell) :=
  sourceHeckeUpperFintype (Q * p) ell

private theorem chosen_sum (c : groupCohomology.cocycles₁ (sourceBinaryCoefficientRep F Q n))
    (g : Gamma0 (Q * p)) :
    (∑ x : Gamma0 Q ⧸ heckeUpperSubgroup Q ell,
      (sourceBinaryCoefficientRep F Q n).ρ
        (sourceLevelHeckeRepresentative Q p ell hell hellQp (sourceGamma0LevelInclusion Q p g • x))
        (homogeneousMatrixAction n (Matrix.diagonal ![(ell : F), 1])
          (c (sourceHeckeConjugation hell
            (sourceChosenCosetTransition (heckeUpperSubgroup Q ell)
              (sourceLevelHeckeRepresentative Q p ell hell hellQp)
              (sourceLevelHeckeRepresentative_coset Q p ell hell hellQp)
              (sourceGamma0LevelInclusion Q p g) x))))) =
      sourceBinaryHeckeCocycle F hell n
        (groupCohomology.mapCocycles₁ (sourceGamma0LevelInclusion Q p)
          (sourceBinaryLevelMorphism F Q p n) c) g := by
  rw [← (sourceLevelHeckeCosetEquiv Q p ell hell hellQp).sum_comp,
    sourceBinaryHeckeCocycle_apply]
  apply Finset.sum_congr rfl
  intro x _
  rw [sourceLevelHeckeRepresentative_smul]
  let u := cosetTransition (heckeUpperSubgroup (Q * p) ell) g x
  have hu : sourceGamma0LevelInclusion Q p u.val ∈ heckeUpperSubgroup Q ell :=
    (sourceLevelInclusion_mem_upper Q p ell u.val).mpr u.property
  have ht : sourceChosenCosetTransition (heckeUpperSubgroup Q ell)
      (sourceLevelHeckeRepresentative Q p ell hell hellQp)
      (sourceLevelHeckeRepresentative_coset Q p ell hell hellQp)
      (sourceGamma0LevelInclusion Q p g)
      (sourceLevelHeckeCosetEquiv Q p ell hell hellQp x) =
      ⟨sourceGamma0LevelInclusion Q p u.val, hu⟩ :=
    Subtype.ext (sourceLevelHeckeTransition_inclusion Q p ell hell hellQp g x)
  rw [ht, sourceLevelHeckeConjugation_inclusion]
  rfl

include hellQp in
/-- The actual level restriction commutes with the full original Hecke
operator at every prime good at the raised level. The full coset sum and
native coboundary correction are proved, rather than supplied. -/
theorem sourceBinaryLevelRestriction_hecke
    (x : groupCohomology.H1 (sourceBinaryCoefficientRep F Q n)) :
    sourceBinaryLevelRestriction F Q p n (sourceBinaryHeckeH1 F hell n x) =
      sourceBinaryHeckeH1 F hell n (sourceBinaryLevelRestriction F Q p n x) := by
  refine groupCohomology.H1_induction_on x ?_
  intro c
  rw [sourceBinaryHeckeH1_cocycle, sourceBinaryLevelRestriction_cocycle,
    sourceBinaryLevelRestriction_cocycle, sourceBinaryHeckeH1_cocycle]
  apply (groupCohomology.H1π_eq_iff _ _).mpr
  have hcorr := sourceCorrespondenceOne_chosen_sub (sourceBinaryCoefficientRep F Q n)
    (heckeUpperSubgroup Q ell) (sourceHeckeConjugation hell)
    (homogeneousMatrixAction n (Matrix.diagonal ![(ell : F), 1]))
    (sourceBinaryHeckeDiagonal_intertwine F hell n)
    (sourceLevelHeckeRepresentative Q p ell hell hellQp)
    (sourceLevelHeckeRepresentative_coset Q p ell hell hellQp) c
  obtain ⟨v, hv⟩ := hcorr
  refine ⟨-v, ?_⟩
  funext g
  have h := congrFun hv (sourceGamma0LevelInclusion Q p g)
  change (sourceBinaryCoefficientRep F Q n).ρ (sourceGamma0LevelInclusion Q p g) v - v =
    (∑ x : Gamma0 Q ⧸ heckeUpperSubgroup Q ell,
      (sourceBinaryCoefficientRep F Q n).ρ
        (sourceLevelHeckeRepresentative Q p ell hell hellQp (sourceGamma0LevelInclusion Q p g • x))
        (homogeneousMatrixAction n (Matrix.diagonal ![(ell : F), 1])
          (c (sourceHeckeConjugation hell
            (sourceChosenCosetTransition (heckeUpperSubgroup Q ell)
              (sourceLevelHeckeRepresentative Q p ell hell hellQp)
              (sourceLevelHeckeRepresentative_coset Q p ell hell hellQp)
              (sourceGamma0LevelInclusion Q p g) x))))) -
      sourceBinaryHeckeCocycle F hell n c (sourceGamma0LevelInclusion Q p g) at h
  rw [chosen_sum F Q p n hell hellQp c g] at h
  change (sourceBinaryCoefficientRep F Q n).ρ (sourceGamma0LevelInclusion Q p g) (-v) - (-v) =
    sourceBinaryHeckeCocycle F hell n c (sourceGamma0LevelInclusion Q p g) -
      sourceBinaryHeckeCocycle F hell n
        (groupCohomology.mapCocycles₁ (sourceGamma0LevelInclusion Q p)
          (sourceBinaryLevelMorphism F Q p n) c) g
  rw [map_neg]
  have he := congrArg Neg.neg h
  simpa only [neg_sub, neg_sub_neg] using he

end
end Dubon2026
