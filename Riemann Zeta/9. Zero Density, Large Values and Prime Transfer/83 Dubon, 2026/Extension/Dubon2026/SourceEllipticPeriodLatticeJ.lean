import Dubon2026.SourceEllipticPeriodModularCurve
import Dubon2026.SourcePeriodEisensteinInvariants
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange

/-! Lattice equality and scaling identify the actual period-curve j-value.
These reuse the already proved Eisenstein scaling formulas and the native
variable-change invariant. The downstream explicit kernel-lattice calculation
uses these identities to identify actual odd quotient j-values on the
DUB-17/18 modular-polynomial product dependency chain. -/

namespace Dubon2026.SourceEllipticPeriod
open WeierstrassCurve SourceFunctionField SourceFunctionField.JOrbitSeparation

theorem periodCurve_eq_of_lattice_eq {L M : PeriodPair} (h : L.lattice = M.lattice) :
    periodCurve L = periodCurve M := by
  have hG (k : ℕ) : L.G k = M.G k := by
    unfold PeriodPair.G
    rw [h]
  have h2 : L.g₂ = M.g₂ := by rw [PeriodPair.g₂, PeriodPair.g₂, hG]
  have h3 : L.g₃ = M.g₃ := by rw [PeriodPair.g₃, PeriodPair.g₃, hG]
  simp only [periodCurve, h2, h3]

theorem periodCurve_scale (L : PeriodPair) (α : ℂˣ) :
    periodCurve (PeriodLattice.scale L α) =
      (⟨α, 0, 0, 0⟩ : VariableChange ℂ) • periodCurve L := by
  ext <;> simp only [periodCurve, variableChange_a₁, variableChange_a₂,
    variableChange_a₃, variableChange_a₄, variableChange_a₆, g₂_scale, g₃_scale,
    zero_mul, mul_zero, add_zero, sub_zero, zero_pow (by decide : 2 ≠ 0),
    zero_pow (by decide : 3 ≠ 0), Units.val_inv_eq_inv_val, inv_pow] <;> ring

instance periodCurve_scale_isElliptic (L : PeriodPair) [(periodCurve L).IsElliptic]
    (α : ℂˣ) : (periodCurve (PeriodLattice.scale L α)).IsElliptic := by
  rw [periodCurve_scale]
  infer_instance

theorem periodCurve_scale_j (L : PeriodPair) [(periodCurve L).IsElliptic] (α : ℂˣ) :
    (periodCurve (PeriodLattice.scale L α)).j = (periodCurve L).j := by
  simp only [periodCurve_scale, variableChange_j]

theorem periodCurve_j_eq_of_scaled_lattice_eq (L M : PeriodPair)
    [(periodCurve L).IsElliptic] [(periodCurve M).IsElliptic]
    (α : ℂˣ) (h : L.lattice = (PeriodLattice.scale M α).lattice) :
    (periodCurve L).j = (periodCurve M).j := by
  simpa only [periodCurve_eq_of_lattice_eq h] using periodCurve_scale_j M α

end Dubon2026.SourceEllipticPeriod
