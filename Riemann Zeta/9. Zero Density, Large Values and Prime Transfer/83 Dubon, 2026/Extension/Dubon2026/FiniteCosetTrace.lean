import Dubon2026.PrincipalCuspAction
import Mathlib.NumberTheory.ModularForms.Bounds

/-! # Genuine finite traces of subgroup-invariant functions -/

namespace Dubon2026

noncomputable section

variable {G X E : Type*} [Group G] [MulAction G X] (H : Subgroup G)

/-- The actual translate of a subgroup-invariant function, descended to the left coset space. -/
def invariantCosetFunction (F : X → E)
    (hF : ∀ g ∈ H, ∀ x, F (g • x) = F x) (x : X) : G ⧸ H → E :=
  Quotient.lift (fun g => F (g⁻¹ • x)) (by
    intro g h hgh
    obtain ⟨j, hj, rfl⟩ : ∃ j ∈ H, h = g * j := by
      rw [← Quotient.eq_iff_equiv, Quotient.eq, QuotientGroup.leftRel_apply] at hgh
      exact ⟨g⁻¹ * h, hgh, (mul_inv_cancel_left g h).symm⟩
    simp [mul_smul, hF j⁻¹ (H.inv_mem hj)])

/-- Evaluation at any integral representative gives the original translated value. -/
theorem invariantCosetFunction_mk (F : X → E)
    (hF : ∀ g ∈ H, ∀ x, F (g • x) = F x) (x : X) (g : G) :
    invariantCosetFunction H F hF x (QuotientGroup.mk g) = F (g⁻¹ • x) := rfl

/-- Choosing a representative introduces no change to the descended function. -/
theorem invariantCosetFunction_out (F : X → E)
    (hF : ∀ g ∈ H, ∀ x, F (g • x) = F x) (x : X) (q : G ⧸ H) :
    invariantCosetFunction H F hF x q = F (q.out⁻¹ • x) := by
  have he := invariantCosetFunction_mk H F hF x q.out
  simpa only [Quotient.out_eq] using he

/-- Simultaneous translation of the point and the coset leaves the actual function unchanged. -/
theorem invariantCosetFunction_smul (F : X → E)
    (hF : ∀ g ∈ H, ∀ x, F (g • x) = F x) (x : X) (g : G) (q : G ⧸ H) :
    invariantCosetFunction H F hF (g • x) (g • q) = invariantCosetFunction H F hF x q := by
  induction q using QuotientGroup.induction_on
  simp [invariantCosetFunction, mul_smul]

variable [AddCommMonoid E] [Fintype (G ⧸ H)]

/-- The literal finite sum over the full coset space, with its actual multiplicities. -/
def finiteCosetTrace (F : X → E) (x : X) : E := ∑ q : G ⧸ H, F (q.out⁻¹ • x)

/-- A finite coset trace of a subgroup-invariant function is invariant under the whole group. -/
theorem finiteCosetTrace_invariant (F : X → E)
    (hF : ∀ g ∈ H, ∀ x, F (g • x) = F x) (g : G) (x : X) :
    finiteCosetTrace H F (g • x) = finiteCosetTrace H F x := by
  simp only [finiteCosetTrace, ← invariantCosetFunction_out H F hF]
  exact (Fintype.sum_equiv (MulAction.toPerm g) _ _
    (fun q => (invariantCosetFunction_smul H F hF x g q).symm)).symm

end
end Dubon2026
