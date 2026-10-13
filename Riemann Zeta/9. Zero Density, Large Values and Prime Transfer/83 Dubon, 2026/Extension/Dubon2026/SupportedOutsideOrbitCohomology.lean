import Dubon2026.SupportedOutsideUnitRepresentation
import Dubon2026.TransportedFiniteOrbitCohomology
import Dubon2026.CyclicProductCohomologyVanishing

/-! # Outside-support cohomology reduced to the actual integer-unit stabilizers

The actual orbit decomposition and original Shapiro comparison reduce
each factor to its original integer-unit stabilizer. Coordinatewise
cyclic vanishing handles the infinite product. The only remaining local
input is vanishing on these specified original modules, to be discharged
by unramified completion theory in DUB-17's global norm-index chain.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsCyclic Gal(L/K)]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)

/-- The actual integer-unit coefficient at an original outside-support orbit representative. -/
def supportedOutsideOrbitPointRep :
    letI := IsCyclic.commGroup (α := Gal(L/K))
    letI := supportedOutsidePlaceAction K L S hS
    ∀ ω : MulAction.orbitRel.Quotient Gal(L/K) {v : HeightOneSpectrum (𝓞 L) // v ∉ S},
      Rep ℤ (MulAction.stabilizer Gal(L/K)
        (permutationOrbitPoint Gal(L/K) {v : HeightOneSpectrum (𝓞 L) // v ∉ S} ω)) := by
  letI := IsCyclic.commGroup (α := Gal(L/K))
  letI := supportedOutsidePlaceAction K L S hS
  intro ω
  exact transportedOrbitPointRep ℤ Gal(L/K) {v : HeightOneSpectrum (𝓞 L) // v ∉ S}
    (fun v => Additive (v.val.adicCompletionIntegers L)ˣ)
    (supportedOutsideUnitTransport K L S hS)
    (supportedOutsideUnitTransport_one K L S hS)
    (supportedOutsideUnitTransport_mul K L S hS) ω
    (permutationOrbitPoint Gal(L/K) {v : HeightOneSpectrum (𝓞 L) // v ∉ S} ω)

/-- Vanishing on the actual outside-support integer-unit stabilizers implies vanishing on the original whole outside-support representation. -/
theorem supportedOutsideUnit_cohomology_zero_of_local (n : ℕ) (hn : 0 < n) :
    letI := IsCyclic.commGroup (α := Gal(L/K))
    letI := supportedOutsidePlaceAction K L S hS
    (∀ ω : MulAction.orbitRel.Quotient Gal(L/K) {v : HeightOneSpectrum (𝓞 L) // v ∉ S},
      Limits.IsZero (groupCohomology (supportedOutsideOrbitPointRep K L S hS ω) n)) →
    Limits.IsZero (groupCohomology (supportedOutsideUnitRep K L S hS) n) := by
  letI := IsCyclic.commGroup (α := Gal(L/K))
  letI := supportedOutsidePlaceAction K L S hS
  intro hlocal
  let I := {v : HeightOneSpectrum (𝓞 L) // v ∉ S}
  let A := transportedOrbitFactorRep ℤ Gal(L/K) I
    (fun v => Additive (v.val.adicCompletionIntegers L)ˣ)
    (supportedOutsideUnitTransport K L S hS)
    (supportedOutsideUnitTransport_one K L S hS)
    (supportedOutsideUnitTransport_mul K L S hS)
  have hz (ω : MulAction.orbitRel.Quotient Gal(L/K) I) :
      Limits.IsZero (groupCohomology (A ω) n) := by
    let e : groupCohomology (A ω) n ≅
        groupCohomology (supportedOutsideOrbitPointRep K L S hS ω) n :=
      transportedOrbitFactorCohomologyIso ℤ Gal(L/K) I
      (fun v => Additive (v.val.adicCompletionIntegers L)ˣ)
      (supportedOutsideUnitTransport K L S hS)
      (supportedOutsideUnitTransport_one K L S hS)
      (supportedOutsideUnitTransport_mul K L S hS) ω (permutationOrbitPoint Gal(L/K) I ω) n
    letI : Subsingleton (groupCohomology (supportedOutsideOrbitPointRep K L S hS ω) n) :=
      ModuleCat.isZero_iff_subsingleton.mp (hlocal ω)
    apply ModuleCat.isZero_iff_subsingleton.mpr
    exact Function.Injective.subsingleton e.toLinearEquiv.injective
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Gal(L/K))
  have hpi := cyclic_originalPi_cohomology_zero A g hg n hn hz
  let e : groupCohomology (supportedOutsideUnitRep K L S hS) n ≅
      groupCohomology (originalPiRep A) n := (groupCohomology.functor ℤ Gal(L/K) n).mapIso
    (transportedOrbitProductIso ℤ Gal(L/K) I
      (fun v => Additive (v.val.adicCompletionIntegers L)ˣ)
      (supportedOutsideUnitTransport K L S hS)
      (supportedOutsideUnitTransport_one K L S hS)
      (supportedOutsideUnitTransport_mul K L S hS))
  letI : Subsingleton (groupCohomology (originalPiRep A) n) :=
    ModuleCat.isZero_iff_subsingleton.mp hpi
  apply ModuleCat.isZero_iff_subsingleton.mpr
  exact Function.Injective.subsingleton e.toLinearEquiv.injective

end
end Dubon2026
