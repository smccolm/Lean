import Dubon2026.SUnitLogarithmicCohomologySequence

/-! # The original finite logarithmic kernel has Herbrand factor one

The actual logarithmic kernel is proved finite, so the existing finite
periodic cohomology calculation applies directly. Its first and second
cohomology cardinalities agree. This discharges the torsion-kernel factor
in DUB-17's S-unit logarithmic Herbrand comparison; multiplicativity along
the original short exact sequence is still required.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)

/-- The actual finite original logarithmic kernel has equal first and second cyclic cohomology cardinalities. -/
theorem sUnitLogarithmicKernel_first_second_card_eq
    (σ : Gal(L/K)) (hgen : ∀ τ, τ ∈ Subgroup.zpowers σ) :
    Nat.card (groupCohomology (sUnitLogarithmicShortComplex K L S hS).X₁ 1) =
      Nat.card (groupCohomology (sUnitLogarithmicShortComplex K L S hS).X₁ 2) := by
  letI : Fintype Gal(L/K) := Fintype.ofFinite _
  letI : IsCyclic Gal(L/K) := ⟨⟨σ, hgen⟩⟩
  letI := IsCyclic.commGroup (α := Gal(L/K))
  letI := sUnitLogarithmicShortComplex_finite_kernel K L S hS
  exact finite_cyclic_first_second_cohomology_card_eq _ σ hgen

end
end Dubon2026
