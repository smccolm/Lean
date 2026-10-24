import Dubon2026.SourceEllipticComplexUniformization

/-! Compute the inverse image of a genuine cyclic point subgroup through
the actual period-model map. Its exact kernel supplies the lattice term.
This is used only to compute the standard prime quotient lattices for the
DUB-17/18 odd-prime modular-polynomial product identity. -/

namespace Dubon2026.SourceEllipticPeriod
open WeierstrassCurve

theorem periodModelHom_mem_zmultiples_iff (L : PeriodPair)
    [(periodCurve L).IsElliptic] (C : VariableChange ℂ) (z w : ℂ) :
    periodModelHom L C z ∈ AddSubgroup.zmultiples (periodModelHom L C w) ↔
      ∃ m : ℤ, z - m * w ∈ L.lattice := by
  rw [AddSubgroup.mem_zmultiples_iff]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    change z - m * w ∈ L.lattice.toAddSubgroup
    rw [← ker_periodModelHom L C, AddMonoidHom.mem_ker, ← zsmul_eq_mul,
      map_sub, map_zsmul, hm, sub_self]
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    have hz : periodModelHom L C (z - m * w) = 0 := by
      rw [← AddMonoidHom.mem_ker, ker_periodModelHom]
      exact hm
    rw [← zsmul_eq_mul, map_sub, map_zsmul, sub_eq_zero] at hz
    exact hz.symm

end Dubon2026.SourceEllipticPeriod
