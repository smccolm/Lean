import Dubon2026.OriginalGlobalAdicH2FiniteSupport
import Dubon2026.OriginalGlobalCompletionH2

/-! # Finite support for the original finite-completion localization

Reuse the proved finite support of original decomposition localization
and its actual completion cohomology isomorphism. The same finite set
works for every underlying prime and every proved lying-over witness.
This removes a finite-support premise from DUB-17's invariant-sum route.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] UniformSpace.Completion.instSMul

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- Original decomposition-localization vanishing implies vanishing in the actual completion Galois cohomology. -/
theorem originalGlobalCompletionH2_eq_zero_of_adic
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2)
    (hx : originalGlobalAdicH2 K L w x = 0) :
    letI : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
      (originalAdicBaseChangeMap K L v w).toAlgebra
    originalGlobalCompletionH2 K L v w x = 0 := by
  letI : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
    (originalAdicBaseChangeMap K L v w).toAlgebra
  apply (originalAdicUnitCohomologyIso K L v w 2).toLinearEquiv.injective
  change (originalAdicUnitCohomologyIso K L v w 2).hom
    (originalGlobalCompletionH2 K L v w x) = (originalAdicUnitCohomologyIso K L v w 2).hom 0
  rw [originalGlobalCompletionH2_decomposition, hx, map_zero]

/-- Every original global H2 class has a proved finite support for its actual completion localizations, uniformly in the original lower prime. -/
theorem originalGlobalCompletionH2_exists_finite_support
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) :
    ∃ S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 L)),
      ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 L), w ∉ S →
      ∀ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
        (h : w.asIdeal.LiesOver v.asIdeal),
      letI := h
      letI : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
        (originalAdicBaseChangeMap K L v w).toAlgebra
      originalGlobalCompletionH2 K L v w x = 0 := by
  obtain ⟨S, hS⟩ := originalGlobalAdicH2_exists_finite_support K L x
  refine ⟨S, ?_⟩
  intro w hw v h
  letI := h
  exact originalGlobalCompletionH2_eq_zero_of_adic K L v w x (hS w hw)

end
end Dubon2026
