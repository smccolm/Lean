import Dubon2026.SourceOriginalRationalTate
import Dubon2026.SourceOriginalHeckeArithmetic
import Dubon2026.SourceOriginalTateGalois

/-! DUB-17/18 -> original rank-two Hecke Galois realization -> actual
rational Tate action. Scalar extension of the existing arithmetic Tate
representation preserves its group law. The proved original Picard
commutation passes through the Tate functor and scalar extension, giving
commutation with every literal rational prime Hecke operator. -/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
variable (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime]
local notation "Qbar" => AlgebraicClosure ℚ

/-- The genuine original arithmetic Galois action after rational Tate scalar extension. -/
def originalRationalTateGaloisRep : (Qbar ≃ₐ[ℚ] Qbar) →*
    Module.End ℚ_[p] (originalRationalTateModule N p) :=
  (Module.End.baseChangeHom ℤ_[p] ℚ_[p] (TateModule p (originalJZero N))).toMonoidHom.comp
    (originalTateGaloisRep N p)

theorem originalRationalTateGaloisRep_apply (σ : Qbar ≃ₐ[ℚ] Qbar) :
    originalRationalTateGaloisRep N p σ = (originalTateGaloisRep N p σ).baseChange ℚ_[p] := rfl

private local instance (ell : Nat.Primes) : NeZero ell.val := ⟨ell.property.ne_zero⟩

theorem originalRationalTateGaloisRep_prime_commute (σ : Qbar ≃ₐ[ℚ] Qbar)
    (ell : Nat.Primes) :
    Commute (originalRationalTateGaloisRep N p σ)
      ((TateModule.tateMap p (originalHeckePicard Qbar N ell.val)).baseChange ℚ_[p]) := by
  have hc : Commute (originalArithmeticPicardRep N σ) (originalHeckePicard Qbar N ell.val) := by
    apply AddMonoidHom.ext
    intro x
    exact originalHeckePicard_arithmetic N ell.val σ x
  have ht := hc.map (TateModule.mapEnd p (originalJZero N))
  have hr := ht.map (Module.End.baseChangeHom ℤ_[p] ℚ_[p] (TateModule p (originalJZero N)))
  exact hr

end
end Dubon2026.SourceFunctionField.OriginalChart
