import Dubon2026.ArithmeticFiniteLocalStageUnramified
import Dubon2026.CyclotomicUnramifiedPrimes

/-! # The actual arithmetic cyclotomic local compositum is unramified away from its conductor

Pinned cyclotomic ramification and the existing original local-compositum
base-change theorem discharge unramifiedness for the exact arithmetic
embedding. This supplies the field premise of the unramified Frobenius
formula in DUB-17's cyclotomic principal product, including primes dividing
the ambient exceptional integer but not the cyclotomic conductor.
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

/-- For the original arithmetic cyclotomic finite stage, every prime outside its actual conductor has unramified original local compositum. -/
theorem arithmeticCyclotomicFiniteLocalStage_integer_unramified
    (n : ℕ) [NeZero n] [IsCyclotomicExtension {n} ℚ F] (hpn : ¬p ∣ n) :
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
  have hn : (n : 𝓞 ℚ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hpaway : ¬(p : 𝓞 ℚ) ∣ (n : 𝓞 ℚ) := by
    intro hd
    have hi := map_dvd Rat.ringOfIntegersEquiv.toRingHom hd
    simp only [map_natCast] at hi
    exact hpn (Int.natCast_dvd_natCast.mp hi)
  have hF : ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
      algebraMap (𝓞 ℚ) (𝓞 F) (n : 𝓞 ℚ) ∉ w.asIdeal →
        (w.asIdeal.under (𝓞 ℚ)).ramificationIdx w.asIdeal = 1 := by
    intro w hw
    have hm : (n : 𝓞 F) ∉ w.asIdeal := by simpa only [map_natCast] using hw
    exact rationalCyclotomic_originalBase_ramificationIdx_one n w hm
  have htop : (algebraMap (rationalPrimeLocalField p hp) M).fieldRange ⊔
      (algebraMap F M).fieldRange = ⊤ := rationalArithmeticFiniteLocalStage_ranges a F p hp
  exact rationalUnramifiedLocalCompositum_integer_unramified F M p hp n hn hpaway hF htop

end
end Dubon2026
