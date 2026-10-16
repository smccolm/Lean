import Dubon2026.OriginalAdicPrimeConjugation
import Dubon2026.OriginalH2InnerConjugation

/-! # Actual idele localization under a change of original upper prime

The original completion Galois comparison and actual idele coordinate
transport identify the two localization maps. The already proved
inner-conjugation coboundary makes the global H2 class unchanged. This
supplies the cohomological part of upper-prime independence for DUB-17.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2
attribute [-instance] UniformSpace.Completion.instSMul
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (v : HeightOneSpectrum (𝓞 K)) (u w : HeightOneSpectrum (𝓞 L))
  [u.asIdeal.LiesOver v.asIdeal] [w.asIdeal.LiesOver v.asIdeal]
  (σ : Gal(L/K)) (hσ : numberFieldGaloisPlaceEquiv K L σ u = w)

/-- The actual completion localizations at conjugate original upper primes agree after the genuine finite local coefficient base change. -/
theorem originalFullIdeleCompletionH2_prime_transport
    (x : groupCohomology (originalFullIdeleRep K L) 2) :
    letI : Algebra (v.adicCompletion K) (u.adicCompletion L) :=
      (originalAdicBaseChangeMap K L v u).toAlgebra
    letI : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
      (originalAdicBaseChangeMap K L v w).toAlgebra
    let e := originalAdicPrimeTransportAlgEquiv K L v u w σ hσ
    letI : Algebra (u.adicCompletion L) (w.adicCompletion L) := e.toRingHom.toAlgebra
    letI : IsScalarTower (v.adicCompletion K) (u.adicCompletion L) (w.adicCompletion L) :=
      IsScalarTower.of_algHom e.toAlgHom
    letI : IsGalois (v.adicCompletion K) (u.adicCompletion L) :=
      (originalAdicBaseChange_finite_galois K L v u).2
    groupCohomology.map
      (galoisBaseChangeRestriction (v.adicCompletion K) (v.adicCompletion K)
        (u.adicCompletion L) (w.adicCompletion L))
      (galoisUnitBaseChangeInclusion (v.adicCompletion K) (v.adicCompletion K)
        (u.adicCompletion L) (w.adicCompletion L)) 2
      (originalFullIdeleCompletionH2 K L v u x) = originalFullIdeleCompletionH2 K L v w x := by
  letI : Algebra (v.adicCompletion K) (u.adicCompletion L) :=
    (originalAdicBaseChangeMap K L v u).toAlgebra
  letI : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
    (originalAdicBaseChangeMap K L v w).toAlgebra
  let e := originalAdicPrimeTransportAlgEquiv K L v u w σ hσ
  letI : Algebra (u.adicCompletion L) (w.adicCompletion L) := e.toRingHom.toAlgebra
  letI : IsScalarTower (v.adicCompletion K) (u.adicCompletion L) (w.adicCompletion L) :=
    IsScalarTower.of_algHom e.toAlgHom
  letI : IsGalois (v.adicCompletion K) (u.adicCompletion L) :=
    (originalAdicBaseChange_finite_galois K L v u).2
  let T := groupCohomology.map (MulAut.conj σ⁻¹).toMonoidHom
    (originalInnerConjugationRepHom (originalFullIdeleRep K L) σ) 2
  have hcomp : groupCohomology.map
      (galoisBaseChangeRestriction (v.adicCompletion K) (v.adicCompletion K)
        (u.adicCompletion L) (w.adicCompletion L))
      (galoisUnitBaseChangeInclusion (v.adicCompletion K) (v.adicCompletion K)
        (u.adicCompletion L) (w.adicCompletion L)) 2
      (originalFullIdeleCompletionH2 K L v u x) = originalFullIdeleCompletionH2 K L v w (T x) := by
    rw [originalFullIdeleCompletionH2_eq_map, originalFullIdeleCompletionH2_eq_map]
    induction x using groupCohomology.H2_induction_on with
    | h c =>
      change groupCohomology.map _ _ 2 (groupCohomology.map _ _ 2
        (groupCohomology.H2π _ c)) =
        groupCohomology.map _ _ 2 (groupCohomology.map _ _ 2 (groupCohomology.H2π _ c))
      simp only [groupCohomology.H2π_comp_map_apply]
      apply congrArg (groupCohomology.H2π _)
      apply Subtype.ext
      funext g
      have hg := congrArg₂ (fun (a b : Gal(L/K)) => (a, b))
        (originalCompletionGaloisRestriction_prime_transport K L v u w σ hσ g.1)
        (originalCompletionGaloisRestriction_prime_transport K L v u w σ hσ g.2)
      change Additive.ofMul (Units.map e.toRingHom.toMonoidHom
        (numberFieldIdeleFiniteComponent L u
          (c (originalCompletionGaloisRestriction K L v u
              (galoisBaseChangeRestriction (v.adicCompletion K) (v.adicCompletion K)
                (u.adicCompletion L) (w.adicCompletion L) g.1),
            originalCompletionGaloisRestriction K L v u
              (galoisBaseChangeRestriction (v.adicCompletion K) (v.adicCompletion K)
                (u.adicCompletion L) (w.adicCompletion L) g.2))).toMul)) = _
      refine (congrArg (fun z : Gal(L/K) × Gal(L/K) =>
        Additive.ofMul (Units.map e.toRingHom.toMonoidHom
          (numberFieldIdeleFiniteComponent L u (c z).toMul))) hg).trans ?_
      apply congrArg Additive.ofMul
      apply Units.ext
      exact (numberFieldFiniteAdeleGaloisMap_apply K L σ _ u w hσ).symm
  exact hcomp.trans (congrArg (originalFullIdeleCompletionH2 K L v w)
    (originalH2_innerConjugation (originalFullIdeleRep K L) σ x))

end
end Dubon2026
