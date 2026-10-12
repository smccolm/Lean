import Dubon2026.ArithmeticCoherentLocalInvariant

/-! # Exact comparison with the existing original local scalar normalization

The coherent global-root normalization need not equal the independently
chosen original local normalization. Their actual nonzero scalar is derived
and the coordinate identity is proved. DUB-17's global duality may therefore
use coherent invariants without silently changing any earlier local pairing.
-/

namespace Dubon2026
noncomputable section
open scoped NumberField

variable (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a)
  (p : ℕ) (hp : p.Prime)
  [TopologicalSpace (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]

/-- The actual factor comparing the coherent arithmetic normalization
with the existing independently chosen local scalar coordinate. -/
def rationalArithmeticLocalNormalizationScalar : ZMod q :=
  rationalArithmeticLocalH2ScalarEquiv a q hqa p hp
    ((rationalPrimeCyclotomicH2ScalarLinearEquiv p hp q).symm 1)

/-- The actual normalization factor is nonzero because both original
cohomology coordinate maps are proved equivalences. -/
theorem rationalArithmeticLocalNormalizationScalar_ne_zero :
    rationalArithmeticLocalNormalizationScalar a q hqa p hp ≠ 0 := by
  intro h
  have h₁ := (rationalArithmeticLocalH2ScalarEquiv a q hqa p hp).map_eq_zero_iff.mp h
  have h₂ := (rationalPrimeCyclotomicH2ScalarLinearEquiv p hp q).symm.map_eq_zero_iff.mp h₁
  exact one_ne_zero h₂

/-- Every original H2 class has the two coordinates related by the
derived nonzero factor; no equality of unrelated primitive roots is assumed. -/
theorem rationalArithmeticLocalH2ScalarEquiv_comparison
    (x : ContinuousRepresentationH2 (coefficientCharacterRep
      (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom)
      (coefficientCharacterAction_continuous _
        (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).continuous)) :
    rationalArithmeticLocalH2ScalarEquiv a q hqa p hp x =
      rationalArithmeticLocalNormalizationScalar a q hqa p hp *
        rationalPrimeCyclotomicH2ScalarLinearEquiv p hp q x := by
  let e := (rationalPrimeCyclotomicH2ScalarLinearEquiv p hp q).symm.trans
    (rationalArithmeticLocalH2ScalarEquiv a q hqa p hp)
  have he : e (rationalPrimeCyclotomicH2ScalarLinearEquiv p hp q x) =
      rationalPrimeCyclotomicH2ScalarLinearEquiv p hp q x * e 1 := by
    simpa only [smul_eq_mul, mul_one] using
      e.map_smul (rationalPrimeCyclotomicH2ScalarLinearEquiv p hp q x) 1
  have hx := congrArg (rationalArithmeticLocalH2ScalarEquiv a q hqa p hp)
    ((rationalPrimeCyclotomicH2ScalarLinearEquiv p hp q).symm_apply_apply x)
  exact hx.symm.trans (he.trans (mul_comm _ _))

end
end Dubon2026
