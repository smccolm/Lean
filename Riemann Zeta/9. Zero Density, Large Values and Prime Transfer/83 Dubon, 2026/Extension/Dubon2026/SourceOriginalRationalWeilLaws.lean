import Dubon2026.SourceOriginalRationalWeilNondegeneracy
import Dubon2026.SourceOriginalTateWeilSkew
import Dubon2026.SourceBilinearBaseChangeLaws
import Dubon2026.SourceOriginalTateWeilHecke
import Dubon2026.SourceOriginalTateWeilCyclotomic
import Dubon2026.SourceOriginalRationalTateGalois

/-! DUB-17/18 -> primitive determinant -> the rational original pairing.
The literal rational tensor pairing is alternating at every Tate prime,
self-adjoint for Hecke primes away from the level, and cyclotomic under
the actual original Galois representation. These are the exact laws needed
for its still-required primitive-component restriction. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open OriginalChart
open scoped TensorProduct
local notation "Qbar" => AlgebraicClosure ℚ
variable (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime]

theorem originalRationalWeilBilinear_self (x : originalRationalTateModule N p) :
    originalRationalWeilBilinear N p x x = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    change (a * a) ⊗ₜ[ℤ_[p]] originalTateWeilBilinear N p x x = 0
    rw [originalTateWeilBilinear_self, TensorProduct.tmul_zero]
  | add x y hx hy =>
    simp only [map_add, LinearMap.add_apply, hx, hy, zero_add, add_zero]
    exact add_eq_zero_iff_eq_neg.mpr
      (sourceBilinear_baseChange_skew (originalTateWeilBilinear N p)
        (originalTateWeilPairing_skew N p) y x)

theorem originalRationalWeilBilinear_hecke (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    (x y : originalRationalTateModule N p) :
    originalRationalWeilBilinear N p
      ((TateModule.tateMap p (originalHeckePicard Qbar N ℓ)).baseChange ℚ_[p] x) y =
    originalRationalWeilBilinear N p x
      ((TateModule.tateMap p (originalHeckePicard Qbar N ℓ)).baseChange ℚ_[p] y) :=
  sourceBilinear_baseChange_adjoint (originalTateWeilBilinear N p)
    (originalTateHecke N ℓ p) (originalTateWeilPairing_hecke_self_adjoint N p ℓ hℓN) x y

theorem originalRationalWeilBilinear_cyclotomic (σ : Qbar ≃ₐ[ℚ] Qbar)
    (x y : originalRationalTateModule N p) :
    originalRationalWeilBilinear N p (originalRationalTateGaloisRep N p σ x)
      (originalRationalTateGaloisRep N p σ y) =
      algebraMap ℤ_[p] ℚ_[p] (cyclotomicCharacter Qbar p σ.toRingEquiv : ℤ_[p]) •
        originalRationalWeilBilinear N p x y :=
  sourceBilinear_baseChange_multiplier (originalTateWeilBilinear N p)
    (originalTateGaloisRep N p σ) _ (originalTateWeilPairing_cyclotomic p N σ) x y

end
end Dubon2026.SourceFunctionField
