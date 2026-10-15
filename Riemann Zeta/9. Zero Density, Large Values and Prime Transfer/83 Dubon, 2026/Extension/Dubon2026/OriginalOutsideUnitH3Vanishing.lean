import Dubon2026.OriginalProductH3Vanishing
import Dubon2026.OriginalOutsidePointVanishing
import Dubon2026.CyclicPositiveCohomologyVanishing

/-! # Original outside-unit H3 vanishing without a cyclic global extension

The actual unramified decomposition groups are cyclic. Their proved H1
vanishing and cyclic periodicity give H3 vanishing. Original orbit/Shapiro
comparison and coordinate primitives assemble this over all outside places.
This is the exact obstruction to surjectivity of the full-class to quotient
H2 comparison required by DUB-17's arithmetic class-formation route.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)

/-- The actual original outside-place H3 vanishes because its unramified stabilizer is cyclic and has zero H1. -/
theorem originalOutsideOrbitPoint_third_zero_of_unramified :
    letI := supportedOutsidePlaceAction K L S hS
    ∀ ω : MulAction.orbitRel.Quotient Gal(L/K) {v : HeightOneSpectrum (𝓞 L) // v ∉ S},
      Algebra.IsUnramifiedAt ℤ ω.out.val.asIdeal →
      Limits.IsZero (groupCohomology (originalOutsideOrbitPointRep K L S hS ω) 3) := by
  letI := supportedOutsidePlaceAction K L S hS
  intro ω hw
  let w := ω.out.val
  let H := MulAction.stabilizer Gal(L/K)
    (originalOrbitPoint Gal(L/K) {v : HeightOneSpectrum (𝓞 L) // v ∉ S} ω)
  let f : H →* OriginalFiniteDecompositionGroup K L w := {
    toFun := fun σ => ⟨σ.val, by
      change numberFieldGaloisPlaceEquiv K L σ.val w = w
      exact congrArg (fun z : ω.orbit => z.val.val) σ.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hf : Function.Injective f := fun x y h =>
    Subtype.ext (congrArg (fun z : OriginalFiniteDecompositionGroup K L w => z.val) h)
  haveI : IsCyclic (OriginalFiniteDecompositionGroup K L w) :=
    originalFiniteDecomposition_isCyclic_of_unramified K L w hw
  haveI : IsCyclic H := isCyclic_of_injective f hf
  letI := IsCyclic.commGroup (α := H)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := H)
  exact cyclic_oddCohomology_zero_of_first (originalOutsideOrbitPointRep K L S hS ω) g hg
    (originalOutsideOrbitPoint_first_second_zero_of_unramified K L S hS ω hw).1 3 (by decide)

/-- The original whole outside-unit H3 vanishes for every actual arithmetic finite extension unramified outside its support. -/
theorem originalOutsideUnit_third_zero_of_unramified
    (hu : ∀ w : HeightOneSpectrum (𝓞 L), w ∉ S → Algebra.IsUnramifiedAt ℤ w.asIdeal) :
    Limits.IsZero (groupCohomology (supportedOutsideUnitRep K L S hS) 3) := by
  letI := supportedOutsidePlaceAction K L S hS
  apply originalTransported_third_zero_of_stabilizers ℤ Gal(L/K)
    {v : HeightOneSpectrum (𝓞 L) // v ∉ S}
    (fun v => Additive (v.val.adicCompletionIntegers L)ˣ)
    (supportedOutsideUnitTransport K L S hS)
    (supportedOutsideUnitTransport_one K L S hS)
    (supportedOutsideUnitTransport_mul K L S hS)
  intro ω
  exact originalOutsideOrbitPoint_third_zero_of_unramified K L S hS ω
    (hu ω.out.val ω.out.property)

end
end Dubon2026
