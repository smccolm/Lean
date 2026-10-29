import Dubon2026.SourceGammaOneTateOpenCongruence
import Dubon2026.SourceGammaOneTwistedGalois

/-! DUB-17/18 -> original all-weight arithmetic association -> continuous
finite homogeneous-valued Tate action. The original period basis and
homogeneous monomial basis prove finiteness of the actual dual. The exact
Tate projection kernel shows that each such functional only depends on
the indicated finite torsion coordinate. Neither finiteness nor a finite
quotient factorization is supplied as a premise. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open SourceCurve CongruenceSubgroup
private theorem tate_map_eq_of_proj_eq {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (p r : ℕ) [Fact p.Prime] [Module ℤ_[p] B]
    (φ : TateModule p A →ₗ[ℤ_[p]] B) {x y : TateModule p A}
    (hxy : TateModule.proj p A r x = TateModule.proj p A r y)
    (hzero : ∀ v : B, (p : ℤ_[p]) ^ r • v = 0) : φ x = φ y := by
  have hz : TateModule.proj p A r (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  apply sub_eq_zero.mp
  rw [← map_sub, ← TateModule.pow_smul_shiftOfProjEqZero r (x - y) hz, map_smul]
  exact hzero _

variable (Q p n w : ℕ) [NeZero Q] [Fact p.Prime]
local notation "N" => p ^ (n + 1)
local notation "M" => Q * N ^ 2
local notation "Qbar" => AlgebraicClosure ℚ
local notation "V" => sourceBinaryCoefficientRep (ZMod N) Q w
local notation "J" => Pic0 Qbar (functionFieldOver (Gamma1 M) Qbar)
local notation "T" => TateModule p J

private local instance : Algebra ℤ_[p] (ZMod N) := (PadicInt.toZModPow (n + 1)).toAlgebra
private local instance : Module ℤ_[p] V := Module.restrictScalars ℤ_[p] (ZMod N) V
private local instance : IsScalarTower ℤ_[p] (ZMod N) V :=
  IsScalarTower.restrictScalars ℤ_[p] (ZMod N) V

theorem binaryArithmeticTateDual_finite : Finite (T →ₗ[ℤ_[p]] V) := by
  letI : Module.Finite (ZMod N) V := Module.Finite.of_basis (binaryHomogeneousMonomialBasis w)
  letI : Finite V := Module.finite_of_finite (ZMod N)
  let b := ((integralPeriodBasis M).baseChange ℤ_[p]).map
    (arithmeticPicardTatePeriodTensorEquiv M p).symm
  exact Finite.of_injective (fun (φ : T →ₗ[ℤ_[p]] V) i => φ (b i))
    (fun φ ψ h => b.ext (fun i => congrFun h i))

omit [NeZero Q] in
theorem binaryArithmeticTateDual_eq_of_proj_eq (φ : T →ₗ[ℤ_[p]] V) {x y : T}
    (hxy : TateModule.proj p J (n + 1) x = TateModule.proj p J (n + 1) y) :
    φ x = φ y := by
  apply tate_map_eq_of_proj_eq p (n + 1) φ hxy
  intro v
  rw [← IsScalarTower.algebraMap_smul (ZMod N)]
  simp only [map_natCast, ← Nat.cast_pow, ZMod.natCast_self, zero_smul]

end
end Dubon2026.SourceFunctionField.GammaOne
