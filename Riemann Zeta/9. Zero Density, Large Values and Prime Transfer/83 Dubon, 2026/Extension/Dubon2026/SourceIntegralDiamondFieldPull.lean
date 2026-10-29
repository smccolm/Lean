import Dubon2026.SourceIntegralDiamondReducedAddition

/-! DUB-17/18 -> original Gamma1 degree/genus -> reduced field action.
The representative below is constructed from the proved representation
theorem for every element of the original field. The pullback uses actual
integral diamond witnesses, and the proved cross-relation theorem gives
its value on every alternative representative. These are constructions
from proved existence, not additional representation or descent premises. -/
namespace Dubon2026.SourceFunctionField.IntegralDiamond
noncomputable section
open UpperHalfPlane CongruenceSubgroup GammaOne
open scoped MatrixGroups ModularForm

/-- An actual even-weight integral ratio representing the specified Laurent series. -/
structure EvenIntegralRepresentative (N ℓ : ℕ) [Fact ℓ.Prime] (x : LaurentSeries (ZMod ℓ)) where
  /-- The shared integer weight of the two actual modular forms. -/
  weight : ℤ
  evenWeight : Even weight
  /-- The actual Gamma1 modular form in the numerator. -/
  numerator : ModularForm (Gamma1 N) weight
  /-- The actual Gamma1 modular form in the denominator. -/
  denominator : ModularForm (Gamma1 N) weight
  /-- The integer Fourier series of the numerator. -/
  numeratorSeries : PowerSeries ℤ
  /-- The integer Fourier series of the denominator. -/
  denominatorSeries : PowerSeries ℤ
  numeratorIntegral : IsIntegralQExp numerator numeratorSeries
  denominatorIntegral : IsIntegralQExp denominator denominatorSeries
  denominatorNonzero : red ℓ denominatorSeries ≠ 0
  represents : x = red ℓ numeratorSeries / red ℓ denominatorSeries

/-- Choose only from the proved actual even integral representatives. -/
def originalEvenRepresentative (N ℓ : ℕ) [Fact ℓ.Prime]
    (x : qExpFunctionFieldC (ZMod ℓ) (Gamma1 N)) :
    EvenIntegralRepresentative N ℓ (x : LaurentSeries (ZMod ℓ)) := Classical.choice (by
  obtain ⟨k, hk, f, g, pf, pg, hf, hg, hg0, hx⟩ := exists_even_originalReducedField_ratio x
  exact ⟨⟨k, hk, f, g, pf, pg, hf, hg, hg0, hx⟩⟩)

/-- Pull back an original reduced field element using the actual diamond forms. -/
def reducedFieldPull (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime] (δ : Gamma0 N)
    (x : qExpFunctionFieldC (ZMod ℓ) (Gamma1 N)) : LaurentSeries (ZMod ℓ) :=
  let v := originalEvenRepresentative N ℓ x
  reducedDiamond N ℓ v.evenWeight δ v.numerator v.numeratorIntegral /
    reducedDiamond N ℓ v.evenWeight δ v.denominator v.denominatorIntegral

theorem reducedFieldPull_eq (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    (δ : Gamma0 N) (x : qExpFunctionFieldC (ZMod ℓ) (Gamma1 N))
    {k : ℤ} (hk : Even k) (f g : ModularForm (Gamma1 N) k)
    {pf pg : PowerSeries ℤ} (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg)
    (hg0 : red ℓ pg ≠ 0) (hx : (x : LaurentSeries (ZMod ℓ)) = red ℓ pf / red ℓ pg) :
    reducedFieldPull N ℓ δ x =
      reducedDiamond N ℓ hk δ f hf / reducedDiamond N ℓ hk δ g hg := by
  let v := originalEvenRepresentative N ℓ x
  exact reducedDiamond_ratio_eq N ℓ hℓN v.evenWeight hk δ v.numerator v.denominator f g
    v.numeratorIntegral v.denominatorIntegral hf hg v.denominatorNonzero hg0
    (v.represents.symm.trans hx)

end
end Dubon2026.SourceFunctionField.IntegralDiamond
