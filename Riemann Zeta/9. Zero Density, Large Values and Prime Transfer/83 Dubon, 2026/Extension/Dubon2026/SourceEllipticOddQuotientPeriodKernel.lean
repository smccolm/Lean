import Dubon2026.SourceEllipticOddQuotientScalar
import Dubon2026.SourceEllipticOddKernelGeometry

/-! The scalar preimage lattice is precisely the inverse image of the
actual cyclic kernel. This identifies the lattice of the odd quotient,
rather than assuming an unrelated analytic isogeny. It is the next input
to the DUB-17/18 odd-prime modular-polynomial product identity. -/

namespace Dubon2026.SourceEllipticPeriod
open WeierstrassCurve SourceEllipticVariableChange SourceEllipticFunctionField
open SourceEllipticVelu

theorem oddPointNorm_periodModel_scalar_kernel
    (L M : PeriodPair) [(periodCurve L).IsElliptic] [(periodCurve M).IsElliptic]
    (C D : VariableChange ℂ) {Q : (C • periodCurve L).toAffine.Point} {n : ℕ}
    (hQ : addOrderOf Q = 2 * n + 1)
    (hD : veluQuotient (C • periodCurve L)
      (oddOrderSummingSet (C • periodCurve L) Q n) = D • periodCurve M) :
    ∃ α : ℂˣ, (∀ l ∈ L.lattice, (α : ℂ) * l ∈ M.lattice) ∧
      (∀ z, periodModelHom M D ((α : ℂ) * z) =
        AddEquiv.cast (M := fun E : WeierstrassCurve ℂ => E.toAffine.Point) hD
          (oddPointNorm (C • periodCurve L) hQ (periodModelHom L C z))) ∧
      ∀ z, (α : ℂ) * z ∈ M.lattice ↔ periodModelHom L C z ∈ AddSubgroup.zmultiples Q := by
  obtain ⟨α, hαL, hα⟩ := oddPointNorm_periodModel_scalar L M C D hQ hD
  refine ⟨α, hαL, hα, fun z => ?_⟩
  have hker : (α : ℂ) * z ∈ M.lattice ↔ periodModelHom M D ((α : ℂ) * z) = 0 := by
    rw [← AddMonoidHom.mem_ker, ker_periodModelHom]
    rfl
  rw [hker, hα,
    map_eq_zero_iff _ (AddEquiv.cast (M := fun E : WeierstrassCurve ℂ => E.toAffine.Point) hD).injective,
    ← AddMonoidHom.mem_ker, ker_oddPointNorm]

theorem exists_odd_quotient_period_model
    (L : PeriodPair) [(periodCurve L).IsElliptic] (C : VariableChange ℂ)
    {Q : (C • periodCurve L).toAffine.Point} {n : ℕ}
    (hQ : addOrderOf Q = 2 * n + 1) :
    ∃ (σ : UpperHalfPlane) (D : VariableChange ℂ),
      ∃ hD : veluQuotient (C • periodCurve L)
        (oddOrderSummingSet (C • periodCurve L) Q n) =
          D • periodCurve (SourceFunctionField.PeriodLattice.ofTau σ),
        ∃ α : ℂˣ,
          (∀ z, periodModelHom (SourceFunctionField.PeriodLattice.ofTau σ) D ((α : ℂ) * z) =
            AddEquiv.cast (M := fun E : WeierstrassCurve ℂ => E.toAffine.Point) hD
              (oddPointNorm (C • periodCurve L) hQ (periodModelHom L C z))) ∧
          (∀ z, (α : ℂ) * z ∈ (SourceFunctionField.PeriodLattice.ofTau σ).lattice ↔
            periodModelHom L C z ∈ AddSubgroup.zmultiples Q) := by
  letI := SourceEllipticVelu.OddDiscriminant.odd_quotient_isElliptic (C • periodCurve L) Q hQ
  obtain ⟨σ, D, hD⟩ := exists_complex_period_model
    (veluQuotient (C • periodCurve L) (oddOrderSummingSet (C • periodCurve L) Q n))
  obtain ⟨α, -, hα, hker⟩ := oddPointNorm_periodModel_scalar_kernel L
    (SourceFunctionField.PeriodLattice.ofTau σ) C D hQ hD.symm
  exact ⟨σ, D, hD.symm, α, hα, hker⟩

end Dubon2026.SourceEllipticPeriod
