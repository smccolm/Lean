import Dubon2026.OriginalGlobalCompletionH2
import Dubon2026.GaloisUnitCharacterCarryPeriod

/-! # Literal original completion localization of character carry classes

Restriction uses the actual completion automorphism on original field
elements, and the coefficient is the same original base unit embedded in
its completion. This supplies the source-entry identity for the local
character pairing in DUB-17's global invariant sum-zero dependency.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical
attribute [local instance 1100] Rep.hV2
attribute [-instance] UniformSpace.Completion.instSMul

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]

/-- Original completion localization sends an actual global carry class to the carry of the literal restricted character and the original completed base unit. -/
theorem originalGlobalCompletionH2_characterCarry
    {n : ℕ} [NeZero n] (χ : Gal(L/K) →* Multiplicative (ZMod n)) (u : Kˣ) :
    letI : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
      (originalAdicBaseChangeMap K L v w).toAlgebra
    originalGlobalCompletionH2 K L v w
      (groupCohomology.H2π (Rep.ofAlgebraAutOnUnits K L)
        (representationCarryCocycle (Rep.ofAlgebraAutOnUnits K L) χ
          (galoisUnitsBaseCoefficient u) (galoisUnitsBaseCoefficient_fixed u))) =
      groupCohomology.H2π
        (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.adicCompletion L))
        (representationCarryCocycle
          (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.adicCompletion L))
          (χ.comp (originalCompletionGaloisRestriction K L v w))
          (galoisUnitsBaseCoefficient
            (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom u))
          (galoisUnitsBaseCoefficient_fixed
            (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom u))) := by
  letI : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
    (originalAdicBaseChangeMap K L v w).toAlgebra
  simp only [originalGlobalCompletionH2, groupCohomology.H2π_comp_map_apply]
  apply congrArg (groupCohomology.H2π _)
  apply groupCohomology.cocycles₂_ext
  intro σ τ
  let a := zmodAdditionCarry (χ (originalCompletionGaloisRestriction K L v w σ)).toAdd
    (χ (originalCompletionGaloisRestriction K L v w τ)).toAdd
  change (Units.map (algebraMap L (w.adicCompletion L)).toMonoidHom).toAdditive
    (a • Additive.ofMul (Units.map (algebraMap K L).toMonoidHom u)) =
      a • Additive.ofMul
        (Units.map (algebraMap (v.adicCompletion K) (w.adicCompletion L)).toMonoidHom
          (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom u))
  rw [map_nsmul]
  congr 1
  apply Additive.toMul.injective
  apply Units.ext
  exact (originalAdicBaseChangeMap_algebraMap K L v w u.val).symm

end
end Dubon2026
