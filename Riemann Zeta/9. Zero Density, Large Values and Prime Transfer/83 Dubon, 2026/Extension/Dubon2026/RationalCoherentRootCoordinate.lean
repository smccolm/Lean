import Dubon2026.ArithmeticLocalNormalizationComparison

/-! Compare the literal local root coefficient maps. DUB-17 needs the
Cartier family normalized by the image of the original global root when
recovering the arithmetic S-unit diagonal. This is the coefficient-level
edge behind the already proved H2 normalization comparison. -/
namespace Dubon2026
noncomputable section
open scoped NumberField

variable (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a)
  (p : ℕ) (hp : p.Prime)

/-- The actual coordinate of the coherent global root in the independently
chosen original local root basis. -/
def rationalArithmeticLocalRootCoordinate : ZMod q :=
  (rationalPrimeCyclotomicRootCoefficientEquiv p hp q).symm
    (rationalArithmeticLocalRootCoefficientEquiv a q hqa p hp 1)

/-- Every coherent root coefficient is the literal local root coefficient
of its scalar multiple by the derived root coordinate. -/
theorem rationalArithmeticLocalRootCoefficientEquiv_coordinate (z : ZMod q) :
    rationalArithmeticLocalRootCoefficientEquiv a q hqa p hp z =
      rationalPrimeCyclotomicRootCoefficientEquiv p hp q
        (rationalArithmeticLocalRootCoordinate a q hqa p hp * z) := by
  let e := (rationalArithmeticLocalRootCoefficientEquiv a q hqa p hp).trans
    (rationalPrimeCyclotomicRootCoefficientEquiv p hp q).symm
  let f : ZMod q →ₗ[ZMod q] ZMod q := e.toAddMonoidHom.toZModLinearMap q
  have hf : e z = z * e 1 := by
    simpa only [smul_eq_mul, mul_one] using f.map_smul z 1
  exact ((rationalPrimeCyclotomicRootCoefficientEquiv p hp q).apply_symm_apply _).symm.trans
    (congrArg (rationalPrimeCyclotomicRootCoefficientEquiv p hp q) (hf.trans (mul_comm _ _)))

end
end Dubon2026
