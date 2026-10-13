import Dubon2026.ArithmeticFiniteStageH2Restriction

/-! # Original finite-coefficient arithmetic H2 restriction away from S

Actual finite descent removes the finite-stage presentation from the local
vanishing theorem. This is the precise intermediate result used for the
original cyclotomic H2 in DUB-17's finite-support requirement.
-/

namespace Dubon2026
noncomputable section
open scoped NumberField

attribute [local instance] arithmeticFiniteLocalStageAlgebra arithmeticFiniteStageH2Galois

variable (a : 𝓞 ℚ) (p : ℕ) (hp : p.Prime) (q : ℕ) [Fact q.Prime]
  (A : Rep.{0} (ZMod q) Gal(rationalUnramifiedExtension a / ℚ))
  [Finite A] [TopologicalSpace A] [DiscreteTopology A] [ContinuousSMul (ZMod q) A]
  (hA : Continuous (fun z : Gal(rationalUnramifiedExtension a / ℚ) × A => A.ρ z.1 z.2))

/-- Actual finite descent proves vanishing of the original arithmetic H2
restriction away from the exceptional integer for every original class. -/
theorem arithmeticH2Restriction_eq_zero (ha : a ≠ 0) (hpa : ¬(p : 𝓞 ℚ) ∣ a)
    (x : ContinuousRepresentationH2 A hA) :
    continuousRepresentationH2Restriction A hA
      (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
      (rationalPrimeArithmeticRestriction a p hp).continuous x = 0 := by
  have hstage := continuousFiniteCoefficientH2_exists_finite_stage
    (K := ℚ) (Ω := rationalUnramifiedExtension a) A hA x
  obtain ⟨F, hF⟩ := hstage
  obtain ⟨ρ, hρexist⟩ := hF
  obtain ⟨hρ, hyexist⟩ := hρexist
  obtain ⟨y, hy⟩ := hyexist
  exact (congrArg (continuousRepresentationH2Restriction A hA
    (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
    (rationalPrimeArithmeticRestriction a p hp).continuous) hy).symm.trans
    (arithmeticFiniteStageH2Restriction_eq_zero a F p hp q A hA ρ hρ ha hpa y)

end
end Dubon2026
