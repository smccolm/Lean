import Dubon2026.SourceEllipticOddQuotientLatticeJ

/-! The actual odd quotient j-value depends on the cyclic subgroup,
independently of its chosen generator. The proved actual norm scalar maps
identify the same preimage lattice. This supplies generator-independent
transport of the complex quotient product before field descent, DUB-17/18. -/

namespace Dubon2026.SourceEllipticPeriod
open WeierstrassCurve SourceFunctionField SourceFunctionField.JOrbitSeparation
open SourceEllipticVelu.OddDiscriminant

theorem mem_scaled_lattice_iff (L : PeriodPair) (α : ℂˣ) (z : ℂ) :
    z ∈ (PeriodLattice.scale L α).lattice ↔ (α : ℂ)⁻¹ * z ∈ L.lattice := by
  rw [mem_scale_lattice, PeriodPair.mem_lattice]
  constructor
  · rintro ⟨a, b, rfl⟩
    exact ⟨a, b, (inv_mul_cancel_left₀ α.ne_zero _).symm⟩
  · rintro ⟨a, b, hab⟩
    exact ⟨a, b, by rw [hab, mul_inv_cancel_left₀ α.ne_zero]⟩

theorem oddQuotientJ_eq_of_zmultiples_eq_period_model
    (L : PeriodPair) [(periodCurve L).IsElliptic] (C : VariableChange ℂ)
    {Q R : (C • periodCurve L).toAffine.Point} {n m : ℕ}
    (hQ : addOrderOf Q = 2 * n + 1) (hR : addOrderOf R = 2 * m + 1)
    (hQR : AddSubgroup.zmultiples Q = AddSubgroup.zmultiples R) :
    oddQuotientJ (C • periodCurve L) hQ = oddQuotientJ (C • periodCurve L) hR := by
  obtain ⟨σ, D, hD, α, -, hα⟩ := exists_odd_quotient_period_model L C hR
  let M := PeriodLattice.ofTau σ
  have hker : ∀ z, periodModelHom L C z ∈ AddSubgroup.zmultiples Q ↔
      z ∈ (PeriodLattice.scale M α⁻¹).lattice := by
    intro z
    rw [hQR, mem_scaled_lattice_iff, Units.val_inv_eq_inv_val, inv_inv]
    exact (hα z).symm
  calc
    oddQuotientJ (C • periodCurve L) hQ = (periodCurve (PeriodLattice.scale M α⁻¹)).j :=
      oddQuotientJ_eq_periodCurve_j_of_kernel_lattice L _ C hQ hker
    _ = (periodCurve M).j := periodCurve_scale_j M α⁻¹
    _ = oddQuotientJ (C • periodCurve L) hR := by
      simp only [oddQuotientJ, hD, variableChange_j, M]

theorem oddQuotientJ_eq_of_zmultiples_eq (W : WeierstrassCurve ℂ) [W.IsElliptic]
    {Q R : W.toAffine.Point} {n m : ℕ}
    (hQ : addOrderOf Q = 2 * n + 1) (hR : addOrderOf R = 2 * m + 1)
    (hQR : AddSubgroup.zmultiples Q = AddSubgroup.zmultiples R) :
    oddQuotientJ W hQ = oddQuotientJ W hR := by
  obtain ⟨τ, C, hC⟩ := exists_complex_period_model W
  subst W
  exact oddQuotientJ_eq_of_zmultiples_eq_period_model _ C hQ hR hQR

end Dubon2026.SourceEllipticPeriod
