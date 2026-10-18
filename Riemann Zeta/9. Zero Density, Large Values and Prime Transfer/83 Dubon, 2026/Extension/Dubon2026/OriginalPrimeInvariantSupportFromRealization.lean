import Dubon2026.ArithmeticRelativePrimeCompletionComparison
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! A proved prime realization transfers actual coordinate vanishing to
the normalized prime invariant. The compatible closure is constructed,
so the DUB-17 rational-total support step needs no closure premise. -/
namespace Dubon2026
noncomputable section
open IsDedekindDomain
open scoped NumberField
attribute [-instance] UniformSpace.Completion.instSMul
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2 Submodule.module
attribute [local instance] originalCompletionCarryAlgebra originalCompletionCarryFinite
  originalCompletionCarryGalois originalCompletionCarryValuation originalCompletionCarryLocalField

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (J : HeightOneSpectrum (𝓞 K) → groupCohomology (originalFullIdeleRep K L) 2 →+ AddCircle (1 : ℚ))
  (hJ : OriginalPrimeInvariantRealization K L J)

include hJ

/-- The algebraic closure of the actual upper completion supplies every
comparison structure needed to send a zero coordinate to a zero invariant. -/
theorem originalPrimeInvariant_zero_of_adic
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal]
    (x : groupCohomology (originalFullIdeleRep K L) 2)
    (hx : originalFullIdeleAdicH2 K L w x = 0) : J v x = 0 := by
  let Ω := AlgebraicClosure (w.adicCompletion L)
  letI : CharZero (v.adicCompletion K) :=
    charZero_of_injective_algebraMap (algebraMap K (v.adicCompletion K)).injective
  letI : Algebra.IsAlgebraic (v.adicCompletion K) Ω :=
    Algebra.IsAlgebraic.trans (v.adicCompletion K) (w.adicCompletion L) Ω
  letI : IsGalois (v.adicCompletion K) Ω := ⟨⟩
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) Ω) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) Ω) := ⟨rfl⟩
  exact (hJ v w Ω x).trans (originalFullIdeleCompletionInvariant_eq_zero_of_adic K L v w Ω x hx)

/-- An actual upper prime is obtained from the proved surjectivity of
contraction, so vanishing on the whole fibre suffices without a chosen prime. -/
theorem originalPrimeInvariant_zero_of_fibre
    (v : HeightOneSpectrum (𝓞 K))
    (x : groupCohomology (originalFullIdeleRep K L) 2)
    (hx : ∀ w : HeightOneSpectrum (𝓞 L), originalFinitePrimeBelow K L w = v →
      originalFullIdeleAdicH2 K L w x = 0) : J v x = 0 := by
  obtain ⟨w, hw⟩ := originalFinitePrimeBelow_surjective K L v
  letI : w.asIdeal.LiesOver v.asIdeal := hw ▸ originalFinitePrimeBelow_liesOver K L w
  exact originalPrimeInvariant_zero_of_adic K L J hJ v w x (hx w hw)

end
end Dubon2026
