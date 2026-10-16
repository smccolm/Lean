import Dubon2026.OriginalFullIdeleBaseChangeH2
import Dubon2026.OriginalFullIdeleCompletionCocycle
import Dubon2026.OriginalCompletionGaloisBaseChange
import Dubon2026.OriginalIdeleNormFiniteComponent

/-! # Original full-idele completion localization under base change

The literal idele-coordinate identity and proved completion-Galois square
give the actual H2 compatibility. This removes the local comparison
premise needed to evaluate the auxiliary cyclic class after restriction
in DUB-17's arbitrary-stage generator transfer.
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

/-- The actual full-idele completion localization commutes with genuine field base change. -/
theorem originalFullIdeleCompletionH2_baseChange
    (x : groupCohomology (originalFullIdeleRep K L) 2) :
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
      (originalFullIdeleCompletionH2 K L v w x) =
    originalFullIdeleCompletionH2 E M u t
      (originalFullIdeleBaseChangeH2 K E L M x) := by
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
  rw [originalFullIdeleCompletionH2_eq_map, originalFullIdeleCompletionH2_eq_map]
  induction x using groupCohomology.H2_induction_on with
  | h c =>
    simp only [originalFullIdeleBaseChangeH2, groupCohomology.H2π_comp_map_apply]
    apply congrArg (groupCohomology.H2π _)
    apply Subtype.ext
    funext g
    change Additive.ofMul (Units.map (originalAdicBaseChangeMap L M w t).toMonoidHom
      (numberFieldIdeleFiniteComponent L w
        (c (originalCompletionGaloisRestriction K L v w
          (galoisBaseChangeRestriction (v.adicCompletion K) (u.adicCompletion E)
            (w.adicCompletion L) (t.adicCompletion M) g.1),
          originalCompletionGaloisRestriction K L v w
            (galoisBaseChangeRestriction (v.adicCompletion K) (u.adicCompletion E)
              (w.adicCompletion L) (t.adicCompletion M) g.2))).toMul)) = _
    have hg := congrArg₂ (fun (a b : Gal(L/K)) => (a, b))
      (originalCompletionGaloisRestriction_baseChange K E L M v u w t g.1)
      (originalCompletionGaloisRestriction_baseChange K E L M v u w t g.2)
    exact (congrArg (fun z : Gal(L/K) × Gal(L/K) =>
      Additive.ofMul (Units.map (originalAdicBaseChangeMap L M w t).toMonoidHom
        (numberFieldIdeleFiniteComponent L w (c z).toMul))) hg).trans
      (congrArg Additive.ofMul (originalIdeleBaseChangeMap_finiteComponent L M w t _).symm)

end
end Dubon2026
