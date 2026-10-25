import Dubon2026.SourceOriginalWeilPairingDescent

/-! DUB-17/18 -> original Tate pairing -> compatibility between
torsion levels. Scale both divisors by m while retaining their principal
functions: an (n*m)-datum becomes an n-datum, and its ratio is raised to m. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilDatum
noncomputable section
open SourceCurve
variable {N : ℕ} [NeZero N] {L : Type*} [Field L] [Algebra ℚ L]
variable {n m : ℕ}

/-- The actual lower-order representatives obtained by multiplying both divisors. -/
def lower (d : OriginalWeilDatum N L (n * m)) : OriginalWeilDatum N L n where
  D₁ := m • d.D₁
  D₂ := m • d.D₂
  f₁ := d.f₁
  f₂ := d.f₂
  f₁_ne_zero := d.f₁_ne_zero
  f₂_ne_zero := d.f₂_ne_zero
  ord_f₁ v := by rw [d.ord_f₁, Finsupp.smul_apply, nsmul_eq_mul, Nat.cast_mul, mul_assoc]
  ord_f₂ v := by rw [d.ord_f₂, Finsupp.smul_apply, nsmul_eq_mul, Nat.cast_mul, mul_assoc]
  disjoint v := by
    rcases d.disjoint v with h | h
    · left; rw [Finsupp.smul_apply, h, smul_zero]
    · right; rw [Finsupp.smul_apply, h, smul_zero]

theorem lower_pairing [IsAlgClosed L] (d : OriginalWeilDatum N L (n * m)) :
    d.lower.pairing = d.pairing ^ m := by
  change originalDivisorEval N L d.f₁ (m • d.D₂) /
    originalDivisorEval N L d.f₂ (m • d.D₁) = _
  rw [originalDivisorEval_nsmul, originalDivisorEval_nsmul, ← div_pow]
  rfl

theorem lower_classLeft [NeZero n] [NeZero m] (d : OriginalWeilDatum N L (n * m)) :
    d.lower.classLeft.val = m • d.classLeft.val := by
  exact Pic0.mk.map_nsmul m ⟨d.D₁, d.degree_first⟩

theorem lower_classRight [NeZero n] [NeZero m] (d : OriginalWeilDatum N L (n * m)) :
    d.lower.classRight.val = m • d.classRight.val := by
  exact Pic0.mk.map_nsmul m ⟨d.D₂, d.degree_second⟩

end
end Dubon2026.SourceFunctionField.OriginalWeilDatum
