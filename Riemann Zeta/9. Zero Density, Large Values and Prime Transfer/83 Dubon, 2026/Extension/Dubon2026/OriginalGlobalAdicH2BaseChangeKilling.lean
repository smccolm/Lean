import Dubon2026.OriginalGlobalCompletionH2BaseChange
import Dubon2026.LocalFieldAlgebraicH2BaseChangeKilling
import Dubon2026.OriginalAdicLocalFieldStructures

/-! # Original global base change vanishes at degree-divisible completions

The actual local finite H2 killing theorem and the proved global/local
square discharge the local vanishing premise of original global detection.
All completion field structures and comparisons are derived from the
original number fields and embeddings. This serves DUB-17's cyclotomic
killing, then principal-product and arithmetic invariant sum-zero route.
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
  [FiniteDimensional K E] [IsGalois K E] [FiniteDimensional K L] [FiniteDimensional E M] [IsGalois K L] [IsGalois E M]
  (v : HeightOneSpectrum (𝓞 K)) (u : HeightOneSpectrum (𝓞 E))
  (w : HeightOneSpectrum (𝓞 L)) (t : HeightOneSpectrum (𝓞 M))
  [u.asIdeal.LiesOver v.asIdeal] [w.asIdeal.LiesOver v.asIdeal]
  [t.asIdeal.LiesOver v.asIdeal] [t.asIdeal.LiesOver u.asIdeal] [t.asIdeal.LiesOver w.asIdeal]

include w in
/-- An actual divisible completion degree kills the localized globally base-changed original torsion class. -/
theorem originalGlobalAdicH2_baseChange_zero_of_degree_dvd
    (q : ℕ) (x : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) (hx : q • x = 0)
    (hq : letI : Algebra (v.adicCompletion K) (u.adicCompletion E) :=
      (originalAdicBaseChangeMap K E v u).toAlgebra
      q ∣ Module.finrank (v.adicCompletion K) (u.adicCompletion E)) :
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
  letI := (originalAdicBaseChange_finite_galois K L v w).1
  letI := (originalAdicBaseChange_finite_galois K E v u).1
  letI := (originalAdicBaseChange_finite_galois E M u t).1
  letI := (originalAdicBaseChange_finite_galois E M u t).2
  letI : ValuativeRel (v.adicCompletion K) :=
    ValuativeRel.ofValuation (NormedField.valuation (K := v.adicCompletion K))
  letI := originalAdic_isNonarchimedeanLocalField K v
  haveI : CharZero (v.adicCompletion K) := Algebra.charZero_of_charZero K (v.adicCompletion K)
  let y := originalGlobalCompletionH2 K L v w x
  have hy : q • y = 0 := by
    change q • originalGlobalCompletionH2 K L v w x = 0
    rw [← map_nsmul, hx, map_zero]
  have hkill := localFieldAlgebraicH2_baseChange_zero_of_degree_dvd
    (v.adicCompletion K) (u.adicCompletion E) (w.adicCompletion L) (t.adicCompletion M)
    q hq y hy
  change groupCohomology.map _ _ 2 (originalGlobalCompletionH2 K L v w x) = 0 at hkill
  rw [originalGlobalCompletionH2_baseChange K E L M v u w t] at hkill
  rw [← originalGlobalCompletionH2_decomposition E M u t, hkill, map_zero]

end
end Dubon2026
