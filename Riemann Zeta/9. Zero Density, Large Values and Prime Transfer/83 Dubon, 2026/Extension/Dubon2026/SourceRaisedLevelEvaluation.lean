import Dubon2026.SourceAffineCocycleEvaluation
import Dubon2026.SourceRaisedLevelConjugation
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-! Injective original evaluation into trivial-coefficient H1 at level Q*p.
DUB-17/18 -> residual modular Galois association -> character-to-weight-two
reduction -> the nonzero original weight-two cohomology class. The actual
raised-level conjugation reaches the complete stabilizer of zero; the
proved cocycle primitive therefore discharges injectivity. Comparison of
the original Hecke operators is a separate required next obligation.
-/

namespace Dubon2026
noncomputable section
open CongruenceSubgroup CategoryTheory groupCohomology

variable (F : Type) [Field F] (p Q : ℕ) [Fact p.Prime] (hpQ : p ∣ Q)

/-- Evaluation at zero after actual raised-level conjugation is equivariant
with the genuine trivial coefficient representation. -/
def sourceRaisedLevelEvaluationCoefficient :
    Rep.res (sourceRaisedLevelConjugation Q p) (sourceAffineFunctionRep p Q F hpQ) ⟶
      Rep.trivial F (Gamma0 (Q * p)) F :=
  Rep.ofHom {
    toLinearMap := {
      toFun f := f 0
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
    isIntertwining' := by
      intro g
      apply LinearMap.ext
      intro f
      change (sourceAffineFunctionRep p Q F hpQ).ρ (sourceRaisedLevelConjugation Q p g) f 0 = f 0
      rw [sourceAffineFunctionRep_apply]
      have hb : sourceAffineB p Q (sourceRaisedLevelConjugation Q p g) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr (sourceRaisedLevelConjugation_upper Q p g)
      rw [mul_zero, hb, sub_self, mul_zero] }

/-- The original raised-level subgroup fixes evaluation of every coefficient at zero. -/
theorem sourceRaisedLevelEvaluation_action (g : Gamma0 (Q * p))
    (v : sourceAffineFunctionRep p Q F hpQ) :
    (sourceAffineFunctionRep p Q F hpQ).ρ (sourceRaisedLevelConjugation Q p g) v 0 = v 0 :=
  LinearMap.congr_fun ((sourceRaisedLevelEvaluationCoefficient F p Q hpQ).hom.isIntertwining' g) v

/-- The actual native H1 evaluation map to trivial coefficients at the original raised level. -/
def sourceRaisedLevelEvaluationH1 :
    H1 (sourceAffineFunctionRep p Q F hpQ) →ₗ[F]
      H1 (Rep.trivial F (Gamma0 (Q * p)) F) :=
  (groupCohomology.map (sourceRaisedLevelConjugation Q p)
    (sourceRaisedLevelEvaluationCoefficient F p Q hpQ) 1).hom

/-- Native H1 evaluation is represented by the literal conjugated cocycle evaluated at zero. -/
theorem sourceRaisedLevelEvaluationH1_cocycle
    (z : cocycles₁ (sourceAffineFunctionRep p Q F hpQ)) :
    sourceRaisedLevelEvaluationH1 F p Q hpQ (H1π _ z) =
      H1π _ (mapCocycles₁ (sourceRaisedLevelConjugation Q p)
        (sourceRaisedLevelEvaluationCoefficient F p Q hpQ) z) :=
  H1π_comp_map_apply _ _ z

/-- The actual raised-level evaluation on native H1 is injective.
Its kernel vanishes by the original explicit cocycle primitive, with
every stabilizer element reached by the integral conjugation. -/
theorem sourceRaisedLevelEvaluationH1_injective :
    Function.Injective (sourceRaisedLevelEvaluationH1 F p Q hpQ) := by
  apply LinearMap.ker_eq_bot.mp
  rw [Submodule.eq_bot_iff]
  intro x hx
  change sourceRaisedLevelEvaluationH1 F p Q hpQ x = 0 at hx
  induction x using H1_induction_on with
  | h z =>
    apply (H1π_eq_zero_iff z).mpr
    apply sourceAffineCocycleEvaluation_coboundary F p Q hpQ z
    intro h hh
    obtain ⟨g, hg⟩ := sourceRaisedLevelConjugation_surjective_upper Q p
      ⟨h, (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hh⟩
    rw [sourceRaisedLevelEvaluationH1_cocycle, H1π_eq_zero_iff,
      coboundaries₁_eq_bot_of_isTrivial] at hx
    have hz : (mapCocycles₁ (sourceRaisedLevelConjugation Q p)
        (sourceRaisedLevelEvaluationCoefficient F p Q hpQ) z :
          Gamma0 (Q * p) → Rep.trivial F (Gamma0 (Q * p)) F) = 0 := hx
    have he := congrFun hz g
    change z (sourceRaisedLevelConjugation Q p g) 0 = 0 at he
    rw [hg] at he
    exact he

end
end Dubon2026
