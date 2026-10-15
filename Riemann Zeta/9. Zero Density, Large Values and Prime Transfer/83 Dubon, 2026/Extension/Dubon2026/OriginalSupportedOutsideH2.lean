import Dubon2026.OriginalOutsidePointVanishing

/-! # Original outside-support H2 vanishing for arbitrary finite Galois extensions

Only the actual unramified decomposition group must be cyclic; its cyclicity
is proved from the original residue action. The existing fixed-uniformizer
local theorem then kills each factor, and the direct product H2 argument
kills the original outside-support coefficient. This removes the cyclic
restriction from the local-detection step serving DUB-17's arithmetic sum-zero.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical WithZero
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)

attribute [-instance] UniformSpace.Completion.instSMul in
/-- The actual outside-support stabilizer H2 vanishes at an absolutely unramified place without a cyclic global-group assumption. -/
theorem originalOutsideOrbitPoint_second_zero_of_unramified :
    letI := supportedOutsidePlaceAction K L S hS
    ∀ ω : MulAction.orbitRel.Quotient Gal(L/K) {v : HeightOneSpectrum (𝓞 L) // v ∉ S},
      Algebra.IsUnramifiedAt ℤ ω.out.val.asIdeal →
      Limits.IsZero (groupCohomology (originalOutsideOrbitPointRep K L S hS ω) 2) := by
  letI := supportedOutsidePlaceAction K L S hS
  intro ω hw
  exact (originalOutsideOrbitPoint_first_second_zero_of_unramified K L S hS ω hw).2

/-- The original outside-support H2 vanishes when all its actual places are absolutely unramified. -/
theorem originalOutsideUnit_second_zero_of_unramified
    (hu : ∀ w : HeightOneSpectrum (𝓞 L), w ∉ S → Algebra.IsUnramifiedAt ℤ w.asIdeal) :
    Limits.IsZero (groupCohomology (supportedOutsideUnitRep K L S hS) 2) := by
  letI := supportedOutsidePlaceAction K L S hS
  apply originalTransported_second_zero_of_stabilizers ℤ Gal(L/K)
    {v : HeightOneSpectrum (𝓞 L) // v ∉ S}
    (fun v => Additive (v.val.adicCompletionIntegers L)ˣ)
    (supportedOutsideUnitTransport K L S hS)
    (supportedOutsideUnitTransport_one K L S hS)
    (supportedOutsideUnitTransport_mul K L S hS)
  intro ω
  exact originalOutsideOrbitPoint_second_zero_of_unramified K L S hS ω
    (hu ω.out.val ω.out.property)

end
end Dubon2026
