import Dubon2026.OriginalCompletionGaloisBaseChange

/-! # Actual global H2 localization commutes with finite base change

The proved square on original automorphisms and the literal completion
embedding give equality on the same cocycles, hence every original H2
class. This discharges the compatibility needed to apply local degree
killing to global odd-primary detection on DUB-17's sum-zero route.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical
attribute [local instance 1100] Rep.hV2
attribute [-instance] UniformSpace.Completion.instSMul
variable (K E L M : Type) [Field K] [NumberField K] [Field E] [NumberField E]
  [Field L] [NumberField L] [Field M] [NumberField M]
  [Algebra K E] [Algebra K L] [Algebra K M] [Algebra E M] [Algebra L M]
  [IsScalarTower K E M] [IsScalarTower K L M]
  [FiniteDimensional K L] [FiniteDimensional E M] [IsGalois K L] [IsGalois E M]
  (v : HeightOneSpectrum (𝓞 K)) (u : HeightOneSpectrum (𝓞 E))
  (w : HeightOneSpectrum (𝓞 L)) (t : HeightOneSpectrum (𝓞 M))
  [u.asIdeal.LiesOver v.asIdeal] [w.asIdeal.LiesOver v.asIdeal]
  [t.asIdeal.LiesOver v.asIdeal] [t.asIdeal.LiesOver u.asIdeal] [t.asIdeal.LiesOver w.asIdeal]

/-- Localizing the actual globally base-changed class equals base-changing its actual original completion class. -/
theorem originalGlobalCompletionH2_baseChange
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) :
  letI : Algebra (v.adicCompletion K) (u.adicCompletion E) :=
    (originalAdicBaseChangeMap K E v u).toAlgebra
  letI : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
    (originalAdicBaseChangeMap K L v w).toAlgebra
  letI : Algebra (v.adicCompletion K) (t.adicCompletion M) :=
    (originalAdicBaseChangeMap K M v t).toAlgebra
  letI : Algebra (u.adicCompletion E) (t.adicCompletion M) :=
    (originalAdicBaseChangeMap E M u t).toAlgebra
  letI : Algebra (w.adicCompletion L) (t.adicCompletion M) :=
    (originalAdicBaseChangeMap L M w t).toAlgebra
  letI := originalAdicBaseChange_isScalarTower K E M v u t
  letI := originalAdicBaseChange_isScalarTower K L M v w t
  letI := (originalAdicBaseChange_finite_galois K L v w).2
  groupCohomology.map
      (galoisBaseChangeRestriction (v.adicCompletion K) (u.adicCompletion E)
        (w.adicCompletion L) (t.adicCompletion M))
      (galoisUnitBaseChangeInclusion (v.adicCompletion K) (u.adicCompletion E)
        (w.adicCompletion L) (t.adicCompletion M)) 2
      (originalGlobalCompletionH2 K L v w x) =
    originalGlobalCompletionH2 E M u t
      (groupCohomology.map (galoisBaseChangeRestriction K E L M)
        (galoisUnitBaseChangeInclusion K E L M) 2 x) := by
  letI : Algebra (v.adicCompletion K) (u.adicCompletion E) :=
    (originalAdicBaseChangeMap K E v u).toAlgebra
  letI : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
    (originalAdicBaseChangeMap K L v w).toAlgebra
  letI : Algebra (v.adicCompletion K) (t.adicCompletion M) :=
    (originalAdicBaseChangeMap K M v t).toAlgebra
  letI : Algebra (u.adicCompletion E) (t.adicCompletion M) :=
    (originalAdicBaseChangeMap E M u t).toAlgebra
  letI : Algebra (w.adicCompletion L) (t.adicCompletion M) :=
    (originalAdicBaseChangeMap L M w t).toAlgebra
  letI := originalAdicBaseChange_isScalarTower K E M v u t
  letI := originalAdicBaseChange_isScalarTower K L M v w t
  letI := (originalAdicBaseChange_finite_galois K L v w).2
  induction x using groupCohomology.H2_induction_on with
  | h c =>
    simp only [originalGlobalCompletionH2, groupCohomology.H2π_comp_map_apply]
    apply congrArg (groupCohomology.H2π _)
    apply Subtype.ext
    funext g
    change Additive.ofMul (Units.map (originalAdicBaseChangeMap L M w t).toMonoidHom
      (Units.map (algebraMap L (w.adicCompletion L)).toMonoidHom
        (c (originalCompletionGaloisRestriction K L v w
          (galoisBaseChangeRestriction (v.adicCompletion K) (u.adicCompletion E)
            (w.adicCompletion L) (t.adicCompletion M) g.1),
          originalCompletionGaloisRestriction K L v w
            (galoisBaseChangeRestriction (v.adicCompletion K) (u.adicCompletion E)
              (w.adicCompletion L) (t.adicCompletion M) g.2))).toMul)) = _
    rw [originalCompletionGaloisRestriction_baseChange K E L M v u w t,
      originalCompletionGaloisRestriction_baseChange K E L M v u w t]
    apply congrArg Additive.ofMul
    apply Units.ext
    exact originalAdicBaseChangeMap_algebraMap L M w t _

end
end Dubon2026
