import Dubon2026.SourceJointChartLocalizations
import Dubon2026.SourceValuationModuleTorsionBound

/-! DUB-17/18 -> Kummer genus inequality -> common residue-chart constants.
The overlap modulo the sum of the two localized charts is the exact module
needed by the idempotent-gluing theorem. Finite generation of this module is
an explicit, still unresolved upstream input. Once supplied, the proved
valuation-module torsion theorem gives one annihilator for its whole torsion
submodule, with no torsion-annihilation certificate assumed. -/
namespace Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
noncomputable section
open IsLocalRing

variable {L F : Type*} [Field L] {A : ValuationSubring L} [Field F] [Algebra L F]
  {ι : Type*} {Fb : ι → Type*} [∀ i, Field (Fb i)]
  [∀ i, Algebra (ResidueField A) (Fb i)]

/-- The two localized charts, viewed as relations inside their common overlap. -/
def overlapRelations (R : ∀ i, RegularProlongation A F (Fb i)) (f : F)
    (hf : ∀ i, f ∈ (R i).integers) (hfi : ∀ i, f⁻¹ ∈ (R i).integers) :
    Submodule A (Ppp R f hf) :=
  ((Pg R f hf).toSubmodule ⊔ (Pg R f⁻¹ hfi).toSubmodule).comap
    (Ppp R f hf).val.toLinearMap

/-- The actual chart-overlap quotient whose finite generation is still required. -/
abbrev overlapQuotient (R : ∀ i, RegularProlongation A F (Fb i)) (f : F)
    (hf : ∀ i, f ∈ (R i).integers) (hfi : ∀ i, f⁻¹ ∈ (R i).integers) :=
  Ppp R f hf ⧸ overlapRelations R f hf hfi

theorem exists_chart_torsion_annihilator
    (R : ∀ i, RegularProlongation A F (Fb i)) (f : F)
    (hf : ∀ i, f ∈ (R i).integers) (hfi : ∀ i, f⁻¹ ∈ (R i).integers)
    [Module.Finite A (overlapQuotient R f hf hfi)] :
    ∃ a : A, a ≠ 0 ∧ ∀ y : F, y ∈ Ppp R f hf → ∀ c : A, c ≠ 0 →
      c • y ∈ (Pg R f hf).toSubmodule ⊔ (Pg R f⁻¹ hfi).toSubmodule →
      a • y ∈ (Pg R f hf).toSubmodule ⊔ (Pg R f⁻¹ hfi).toSubmodule := by
  let N := overlapRelations R f hf hfi
  obtain ⟨a, ha0, ha⟩ := exists_uniform_torsion_annihilator
    (R := A) (M := overlapQuotient R f hf hfi)
  refine ⟨a, ha0, fun y hy c hc0 hcy => ?_⟩
  have h1 : c • N.mkQ ⟨y, hy⟩ = 0 := by
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hcy
  have h2 := ha _ ⟨c, hc0, h1⟩
  rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h2
  exact h2

end
end Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
