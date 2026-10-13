import Dubon2026.ArithmeticFiniteLocalStage
import Dubon2026.RationalUnramifiedLocalCompositum
import Dubon2026.UnramifiedUnionFiniteRamification

/-! # The original arithmetic finite local stage is unramified away from S

This discharges local integer unramifiedness for the exact stage and exact
arithmetic embedding, by the proved base change and global ramification input.
It is the actual field premise for DUB-17 local H2 support control.
-/

namespace Dubon2026
noncomputable section
open scoped NumberField ValuativeRel

attribute [local instance] arithmeticFiniteLocalStageAlgebra
  arithmeticFiniteLocalStageGalois arithmeticFiniteLocalStageRationalAlgebra

variable (a : 𝓞 ℚ) (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
  (p : ℕ) (hp : p.Prime)
  [ValuativeRel (rationalArithmeticFiniteLocalStage a F p hp)]
  [TopologicalSpace (rationalArithmeticFiniteLocalStage a F p hp)]
  [IsNonarchimedeanLocalField (rationalArithmeticFiniteLocalStage a F p hp)]
  [(ValuativeRel.valuation (rationalPrimeLocalField p hp)).HasExtension
    (ValuativeRel.valuation (rationalArithmeticFiniteLocalStage a F p hp))]

/-- The original constructed local stage has unramified integer extension at
each prime away from the original exceptional integer. All algebraic maps and
the field-generation premise are supplied by the exact arithmetic embedding. -/
theorem arithmeticFiniteLocalStage_integer_unramified (ha : a ≠ 0) (hpa : ¬(p : 𝓞 ℚ) ∣ a) :
    Algebra.FormallyUnramified 𝒪[rationalPrimeLocalField p hp]
      𝒪[rationalArithmeticFiniteLocalStage a F p hp] := by
  let M := rationalArithmeticFiniteLocalStage a F p hp
  let j : F →ₐ[ℚ] M := rationalArithmeticFiniteLocalStageInclusion a F p hp
  let algebraFM : Algebra F M := j.toRingHom.toAlgebra
  letI : SMul F M := algebraFM.toSMul
  letI : Algebra F M := algebraFM
  letI : SMul ℚ F := (inferInstance : Algebra ℚ F).toSMul
  letI : SMul ℚ M := (inferInstance : Algebra ℚ M).toSMul
  haveI : IsScalarTower ℚ F M := IsScalarTower.of_algebraMap_eq fun r => (j.commutes r).symm
  have hF : ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
      algebraMap (𝓞 ℚ) (𝓞 F) a ∉ w.asIdeal →
        (w.asIdeal.under (𝓞 ℚ)).ramificationIdx w.asIdeal = 1 :=
    originalUnramifiedUnion_finite_ramification a ha F.toIntermediateField
  have htop : (algebraMap (rationalPrimeLocalField p hp) M).fieldRange ⊔
      (algebraMap F M).fieldRange = ⊤ := rationalArithmeticFiniteLocalStage_ranges a F p hp
  exact rationalUnramifiedLocalCompositum_integer_unramified F M p hp a ha hpa hF htop

end
end Dubon2026
