import Dubon2026.OriginalGlobalCompletionH2BaseChange

/-! # Actual global base change preserves original local vanishing

The same-cocycle square and original decomposition/Galois cohomology
isomorphism preserve every already vanishing localization. Together with
finite support, this limits cyclotomic degree killing to the necessary
finite set on DUB-17's arithmetic invariant sum-zero dependency.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical
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

include v u in
/-- Actual original finite-prime vanishing persists after the genuine global base change. -/
theorem originalGlobalAdicH2_baseChange_zero_of_local_zero
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2)
    (hx : originalGlobalAdicH2 K L w x = 0) :
    originalGlobalAdicH2 E M t
      (groupCohomology.map (galoisBaseChangeRestriction K E L M)
        (galoisUnitBaseChangeInclusion K E L M) 2 x) = 0 := by
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
  have hy : originalGlobalCompletionH2 K L v w x = 0 := by
    apply (originalAdicUnitCohomologyIso K L v w 2).toLinearEquiv.injective
    change (originalAdicUnitCohomologyIso K L v w 2).hom
      (originalGlobalCompletionH2 K L v w x) = (originalAdicUnitCohomologyIso K L v w 2).hom 0
    rw [originalGlobalCompletionH2_decomposition, hx, map_zero]
  rw [← originalGlobalCompletionH2_decomposition E M u t,
    ← originalGlobalCompletionH2_baseChange K E L M v u w t, hy]
  simp only [map_zero]

end
end Dubon2026
