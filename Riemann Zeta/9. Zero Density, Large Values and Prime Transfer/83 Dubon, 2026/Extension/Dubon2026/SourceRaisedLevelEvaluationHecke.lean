import Dubon2026.SourceRaisedHeckeRepresentatives
import Dubon2026.SourceRaisedLevelEvaluation
import Dubon2026.SourceAffineFunctionHecke
import Dubon2026.SourceTrivialCoefficientHecke
import Dubon2026.SourceCorrespondenceOne

/-! Original Hecke compatibility of raised-level evaluation.
DUB-17/18 -> residual modular Galois association -> character-to-weight-two
reduction -> the actual nonzero trivial-coefficient Hecke eigensystem.
The actual conjugation gives a bijection of original Hecke cosets. Its
representatives fix evaluation at zero, as does the affine diagonal.
The proved native representative correction therefore evaluates to zero.
-/

namespace Dubon2026
noncomputable section
open CongruenceSubgroup groupCohomology

variable (F : Type) [Field F] (p Q : ℕ) [Fact p.Prime] (hpQ : p ∣ Q)
    {ell : ℕ} [NeZero ell] (hell : ell.Prime) (hellQp : Nat.Coprime ell (Q * p))

private local instance raisedHeckeOldFinite :
    Fintype (Gamma0 Q ⧸ heckeUpperSubgroup Q ell) := sourceHeckeUpperFintype Q ell

private local instance raisedHeckeNewFinite :
    Fintype (Gamma0 (Q * p) ⧸ heckeUpperSubgroup (Q * p) ell) :=
  sourceHeckeUpperFintype (Q * p) ell

private theorem chosen_sum (z : cocycles₁ (sourceAffineFunctionRep p Q F hpQ))
    (g : Gamma0 (Q * p)) :
    (∑ x : Gamma0 Q ⧸ heckeUpperSubgroup Q ell,
      (sourceAffineFunctionRep p Q F hpQ).ρ
        (sourceRaisedHeckeRepresentative Q p ell hell hellQp
          (sourceRaisedLevelConjugation Q p g • x))
        (sourceAffineFunctionDiagonal p F ell
          (z (sourceHeckeConjugation hell
            (sourceChosenCosetTransition (heckeUpperSubgroup Q ell)
              (sourceRaisedHeckeRepresentative Q p ell hell hellQp)
              (sourceRaisedHeckeRepresentative_coset Q p ell hell hellQp)
              (sourceRaisedLevelConjugation Q p g) x)))) 0) =
      ∑ x : Gamma0 (Q * p) ⧸ heckeUpperSubgroup (Q * p) ell,
        z (sourceRaisedLevelConjugation Q p
          (sourceHeckeConjugation hell
            (cosetTransition (heckeUpperSubgroup (Q * p) ell) g x))) 0 := by
  rw [← (sourceRaisedHeckeCosetEquiv Q p ell hellQp hell).sum_comp]
  apply Finset.sum_congr rfl
  intro x _
  rw [sourceRaisedHeckeRepresentative_smul, sourceRaisedLevelEvaluation_action]
  let u := cosetTransition (heckeUpperSubgroup (Q * p) ell) g x
  have hu : sourceRaisedLevelConjugation Q p u.val ∈ heckeUpperSubgroup Q ell :=
    (sourceRaisedLevel_mem_upper Q p ell hellQp u.val).mpr u.property
  have ht : sourceChosenCosetTransition (heckeUpperSubgroup Q ell)
      (sourceRaisedHeckeRepresentative Q p ell hell hellQp)
      (sourceRaisedHeckeRepresentative_coset Q p ell hell hellQp)
      (sourceRaisedLevelConjugation Q p g)
      (sourceRaisedHeckeCosetEquiv Q p ell hellQp hell x) =
      ⟨sourceRaisedLevelConjugation Q p u.val, hu⟩ :=
    Subtype.ext (sourceRaisedHeckeTransition_inclusion Q p ell hell hellQp g x)
  rw [ht, sourceRaisedHeckeConjugation_inclusion Q p ell hell hellQp]
  change z (sourceRaisedLevelConjugation Q p (sourceHeckeConjugation hell u))
    ((ell : ZMod p)⁻¹ * 0) = _
  rw [mul_zero]

/-- Evaluation intertwines the actual full prime correspondences already
on native cocycles: the change-of-representative coboundary evaluates to zero. -/
theorem sourceRaisedLevelEvaluation_cocycles_hecke
    (z : cocycles₁ (sourceAffineFunctionRep p Q F hpQ)) :
    mapCocycles₁ (sourceRaisedLevelConjugation Q p)
        (sourceRaisedLevelEvaluationCoefficient F p Q hpQ)
        (sourcePrimeHeckeCocycles hell (sourceAffineFunctionRep p Q F hpQ)
          (sourceAffineFunctionDiagonal p F ell)
          (sourceAffineFunctionDiagonal_intertwine F p Q hpQ
            ⟨ell, hell, hellQp.of_dvd_right (dvd_mul_right Q p)⟩) z) =
      sourcePrimeHeckeCocycles hell (Rep.trivial F (Gamma0 (Q * p)) F) LinearMap.id
        (sourceTrivialCoefficient_intertwine F (Q * p) hell)
        (mapCocycles₁ (sourceRaisedLevelConjugation Q p)
          (sourceRaisedLevelEvaluationCoefficient F p Q hpQ) z) := by
  apply Subtype.ext
  funext g
  obtain ⟨v, hv⟩ := sourceCorrespondenceOne_chosen_sub (sourceAffineFunctionRep p Q F hpQ)
    (heckeUpperSubgroup Q ell) (sourceHeckeConjugation hell)
    (sourceAffineFunctionDiagonal p F ell)
    (sourceAffineFunctionDiagonal_intertwine F p Q hpQ
      ⟨ell, hell, hellQp.of_dvd_right (dvd_mul_right Q p)⟩)
    (sourceRaisedHeckeRepresentative Q p ell hell hellQp)
    (sourceRaisedHeckeRepresentative_coset Q p ell hell hellQp) z
  have h := congrFun (congrFun hv (sourceRaisedLevelConjugation Q p g)) 0
  change (sourceAffineFunctionRep p Q F hpQ).ρ
      (sourceRaisedLevelConjugation Q p g) v 0 - v 0 =
    (∑ x : Gamma0 Q ⧸ heckeUpperSubgroup Q ell,
      (sourceAffineFunctionRep p Q F hpQ).ρ
        (sourceRaisedHeckeRepresentative Q p ell hell hellQp
          (sourceRaisedLevelConjugation Q p g • x))
        (sourceAffineFunctionDiagonal p F ell
          (z (sourceHeckeConjugation hell
            (sourceChosenCosetTransition (heckeUpperSubgroup Q ell)
              (sourceRaisedHeckeRepresentative Q p ell hell hellQp)
              (sourceRaisedHeckeRepresentative_coset Q p ell hell hellQp)
              (sourceRaisedLevelConjugation Q p g) x))))) 0 -
      sourceCorrespondenceOne (sourceAffineFunctionRep p Q F hpQ)
        (heckeUpperSubgroup Q ell) (sourceHeckeConjugation hell)
        (sourceAffineFunctionDiagonal p F ell) z (sourceRaisedLevelConjugation Q p g) 0 at h
  have hs (f : Gamma0 Q ⧸ heckeUpperSubgroup Q ell → sourceAffineFunctionRep p Q F hpQ) :
      (∑ x, f x) 0 = ∑ x, f x 0 :=
    map_sum (sourceRaisedLevelEvaluationCoefficient F p Q hpQ).hom.toLinearMap f Finset.univ
  rw [sourceRaisedLevelEvaluation_action, sub_self, hs,
    chosen_sum F p Q hpQ hell hellQp z g] at h
  exact (sub_eq_zero.mp h.symm).symm

/-- Original raised-level evaluation on H1 preserves every full good-prime Hecke operator. -/
theorem sourceRaisedLevelEvaluationH1_hecke
    (x : H1 (sourceAffineFunctionRep p Q F hpQ)) :
    sourceRaisedLevelEvaluationH1 F p Q hpQ
        (sourceAffineFunctionHeckeOperators F p Q hpQ
          ⟨ell, hell, hellQp.of_dvd_right (dvd_mul_right Q p)⟩ x) =
      sourceTrivialCoefficientHeckeOperators F (Q * p) ⟨ell, hell, hellQp⟩
        (sourceRaisedLevelEvaluationH1 F p Q hpQ x) := by
  induction x using H1_induction_on with
  | h z =>
    change sourceRaisedLevelEvaluationH1 F p Q hpQ (sourcePrimeHeckeH1 _ _ _ _ (H1π _ z)) =
      sourcePrimeHeckeH1 _ _ _ _ (sourceRaisedLevelEvaluationH1 F p Q hpQ (H1π _ z))
    rw [sourcePrimeHeckeH1_cocycle, sourceRaisedLevelEvaluationH1_cocycle,
      sourceRaisedLevelEvaluationH1_cocycle, sourcePrimeHeckeH1_cocycle,
      sourceRaisedLevelEvaluation_cocycles_hecke F p Q hpQ hell hellQp]

end
end Dubon2026
