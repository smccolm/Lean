import Dubon2026.SourceEllipticPeriodQuotientGerm

/-! Actual complex odd quotient maps are induced by nonzero complex
scalars on period lattices. The affine-germ condition is proved from the
literal norm formulas rather than retained as a hypothesis. This is the
quotient-compatibility input to the odd-prime product identity, required by
the DUB-17/18 cyclic-root and good-reduction dependency chain. -/

namespace Dubon2026.SourceEllipticPeriod
open WeierstrassCurve SourceEllipticVariableChange SourceEllipticFunctionField
open SourceEllipticVelu

variable (L M : PeriodPair) [(periodCurve L).IsElliptic] [(periodCurve M).IsElliptic]
variable (C D : VariableChange ℂ) {Q : (C • periodCurve L).toAffine.Point} {n : ℕ}
variable (hQ : addOrderOf Q = 2 * n + 1)
variable (hD : veluQuotient (C • periodCurve L)
  (oddOrderSummingSet (C • periodCurve L) Q n) = D • periodCurve M)

theorem periodOddNorm_scalar :
    ∃ α : ℂˣ, (∀ l ∈ L.lattice, (α : ℂ) * l ∈ M.lattice) ∧
      ∀ z, periodHom M ((α : ℂ) * z) = periodOddNorm L M C D hQ hD (periodHom L z) := by
  obtain ⟨z₀, U, hU, X, Y, hX, hY, hcoord⟩ :=
    exists_periodOddNorm_affine_germ L M C D hQ hD
  exact scalar_map_of_affine_germ L M (periodOddNorm L M C D hQ hD)
    (periodOddNorm_surjective L M C D hQ hD) z₀ hU X Y hX hY hcoord

theorem oddPointNorm_periodModel_scalar :
    ∃ α : ℂˣ, (∀ l ∈ L.lattice, (α : ℂ) * l ∈ M.lattice) ∧
      ∀ z, periodModelHom M D ((α : ℂ) * z) =
        AddEquiv.cast (M := fun E : WeierstrassCurve ℂ => E.toAffine.Point) hD
          (oddPointNorm (C • periodCurve L) hQ (periodModelHom L C z)) := by
  obtain ⟨α, hαL, hα⟩ := periodOddNorm_scalar L M C D hQ hD
  refine ⟨α, hαL, fun z => ?_⟩
  apply (variableChangeAddEquiv D (periodCurve M).toAffine).injective
  simpa only [periodModelHom, AddMonoidHom.comp_apply, AddEquiv.toAddMonoidHom_eq_coe,
    AddMonoidHom.coe_coe, AddEquiv.apply_symm_apply] using hα z

end Dubon2026.SourceEllipticPeriod
