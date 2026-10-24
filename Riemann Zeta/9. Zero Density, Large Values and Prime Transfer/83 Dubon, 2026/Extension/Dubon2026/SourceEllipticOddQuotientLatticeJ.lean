import Dubon2026.SourceEllipticOddQuotientPeriodKernel
import Dubon2026.SourceEllipticPeriodLatticeJ
import Dubon2026.SourceEllipticOddQuotientJ

/-! Identify the j-value of the actual odd quotient from its computed
cyclic-kernel preimage lattice. The actual scalar compatibility and target
period model supply the comparison; a quotient j-value is never postulated.
SourceEllipticStandardOddQuotientJ consumes the explicit standard lattices
for the DUB-17/18 prime quotient-product identity. -/

namespace Dubon2026.SourceEllipticPeriod
open WeierstrassCurve SourceFunctionField SourceFunctionField.JOrbitSeparation
open SourceEllipticVelu.OddDiscriminant

theorem oddQuotientJ_eq_periodCurve_j_of_kernel_lattice
    (L N : PeriodPair) [(periodCurve L).IsElliptic] [(periodCurve N).IsElliptic]
    (C : VariableChange ℂ) {Q : (C • periodCurve L).toAffine.Point} {n : ℕ}
    (hQ : addOrderOf Q = 2 * n + 1)
    (hker : ∀ z, periodModelHom L C z ∈ AddSubgroup.zmultiples Q ↔ z ∈ N.lattice) :
    oddQuotientJ (C • periodCurve L) hQ = (periodCurve N).j := by
  obtain ⟨σ, D, hD, α, -, hα⟩ := exists_odd_quotient_period_model L C hQ
  let M := PeriodLattice.ofTau σ
  have hlat : M.lattice = (PeriodLattice.scale N α).lattice := by
    ext z
    rw [mem_scale_lattice]
    constructor
    · intro hz
      have hz' : (α : ℂ)⁻¹ * z ∈ N.lattice := (hker _).mp ((hα _).mp (by
        simpa only [mul_inv_cancel_left₀ α.ne_zero] using hz))
      obtain ⟨a, b, hab⟩ := PeriodPair.mem_lattice.mp hz'
      refine ⟨a, b, ?_⟩
      rw [hab, mul_inv_cancel_left₀ α.ne_zero]
    · rintro ⟨a, b, rfl⟩
      exact (hα _).mpr ((hker _).mpr (PeriodPair.mem_lattice.mpr ⟨a, b, rfl⟩))
  calc
    oddQuotientJ (C • periodCurve L) hQ = (periodCurve M).j := by
      simp only [oddQuotientJ, hD, variableChange_j, M]
    _ = (periodCurve N).j := periodCurve_j_eq_of_scaled_lattice_eq M N α hlat

end Dubon2026.SourceEllipticPeriod
