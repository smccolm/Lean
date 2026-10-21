import Dubon2026.SourceCurveAdeleCore
import Dubon2026.SourceCurveLSpaceFiniteStep

/-! DUB-17/18 -> regular differential dimension -> the unresolved original
function-field Riemann--Roch theorem. Its index calculation needs the exact
local quotient dimension. The scaled residue map is proved surjective,
with kernel the bound decreased by one. Adapted from the selected local
quotient in S_AlgebraicCurve_finiteDimensional_lSpace,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2. Only finite residue is needed
for the dimension corollary; it is already proved for all original places.
-/
namespace Dubon2026.SourceCurve
noncomputable section
open Module
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem Place.adicValuation_eq_exp_neg_ord (v : Place K F) {f : F} (hf : f ≠ 0) :
    v.adicValuation f = WithZero.exp (-v.ord f) := by
  rw [Place.ord, neg_neg, WithZero.exp_log (v.adicValuation_ne_zero hf)]

/-- One step in the local divisor bound has exactly the actual residue field as quotient. -/
def adeleBddQuotSingleEquivResidueField (D : Divisor K F) (P : Place K F) :
    (adeleBdd D ⧸ (adeleBdd (D - Finsupp.single P 1)).comap (adeleBdd D).subtype)
      ≃ₗ[K] P.ResidueField := by
  classical
  set E : Divisor K F := D - Finsupp.single P 1 with hE
  have hEP : E P = D P - 1 := by rw [hE, Finsupp.sub_apply, Finsupp.single_eq_same]
  have hEv : ∀ v, v ≠ P → E v = D v := by
    intro v hv; rw [hE, Finsupp.sub_apply, Finsupp.single_eq_of_ne hv, sub_zero]

  let π : P.toValuationSubring :=
    (IsDiscreteValuationRing.exists_irreducible P.toValuationSubring).choose
  have hπ : Irreducible π :=
    (IsDiscreteValuationRing.exists_irreducible P.toValuationSubring).choose_spec
  set t : F := (π : F) with ht
  have ht0 : t ≠ 0 := by simpa [ht, ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero
  have ht1 : P.ord t = 1 := P.ord_coe_irreducible hπ
  have htn0 : t ^ (D P) ≠ 0 := zpow_ne_zero _ ht0

  have hordmul : ∀ {g : F}, g ≠ 0 → P.ord (t ^ (D P) * g) = D P + P.ord g := fun {g} hg => by
    rw [P.ord_mul htn0 hg, P.ord_zpow, ht1, mul_one]

  have hmem : ∀ α : Place K F → F, α ∈ adeleBdd D → t ^ (D P) * α P ∈ P.toValuationSubring := by
    intro α hα
    rcases eq_or_ne (α P) 0 with hg0 | hg0
    · simp [hg0]
    · refine P.mem_of_ord_nonneg ?_
      rw [hordmul hg0]
      have h := hα P
      rw [P.adicValuation_eq_exp_neg_ord hg0, WithZero.exp_le_exp] at h
      linarith

  let ψ : adeleBdd D →ₗ[K] P.toValuationSubring :=
    { toFun := fun α => ⟨t ^ (D P) * (α : Place K F → F) P, hmem _ α.2⟩
      map_add' := by
        intro α β; apply Subtype.ext
        simp only [Submodule.coe_add, Pi.add_apply]
        push_cast; ring
      map_smul' := by
        intro c α; apply Subtype.ext
        simp only [RingHom.id_apply, SetLike.val_smul, Algebra.smul_def, MulMemClass.coe_mul,
          Place.coe_algebraMap, Pi.smul_apply]
        ring }
  have hψ_apply : ∀ α : adeleBdd D,
      (ψ α : F) = t ^ (D P) * (α : Place K F → F) P := fun α => rfl

  let res : P.toValuationSubring →ₗ[K] P.ResidueField :=
    (Algebra.linearMap P.toValuationSubring P.ResidueField).restrictScalars K
  have hres : ∀ x : P.toValuationSubring, res x = IsLocalRing.residue _ x := by
    intro x
    show (Algebra.linearMap P.toValuationSubring P.ResidueField).restrictScalars K x = _
    rw [LinearMap.restrictScalars_apply, Algebra.linearMap_apply,
      IsLocalRing.ResidueField.algebraMap_eq]
  let φ : adeleBdd D →ₗ[K] P.ResidueField := res ∘ₗ ψ

  have hphi : ∀ α : adeleBdd D, φ α = 0 ↔
      (⟨t ^ (D P) * (α : Place K F → F) P, hmem _ α.2⟩ : P.toValuationSubring)
        ∈ IsLocalRing.maximalIdeal P.toValuationSubring := fun α => by
    rw [show φ α = IsLocalRing.residue P.toValuationSubring
            ⟨t ^ (D P) * (α : Place K F → F) P, hmem _ α.2⟩ from hres (ψ α),
      IsLocalRing.residue_eq_zero_iff]

  have hker : LinearMap.ker φ = (adeleBdd E).comap (adeleBdd D).subtype := by
    ext α
    simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.coe_subtype]
    rw [hphi α, P.mk_mem_maximalIdeal_iff, mem_adeleBdd]
    have hαD := α.2
    constructor
    · rintro (h | h) v
      ·
        have hα0 : (α : Place K F → F) P = 0 := by
          rcases mul_eq_zero.mp h with h' | h'
          · exact absurd h' htn0
          · exact h'
        by_cases hv : v = P
        · subst v; rw [hα0, Valuation.map_zero]; exact zero_le'
        · rw [hEv v hv]; exact hαD v
      · by_cases hv : v = P
        · subst v
          rcases eq_or_ne ((α : Place K F → F) P) 0 with hα0 | hα0
          · rw [hα0, Valuation.map_zero]; exact zero_le'
          · rw [P.adicValuation_eq_exp_neg_ord hα0, WithZero.exp_le_exp, hEP]
            rw [hordmul hα0] at h; omega
        · rw [hEv v hv]; exact hαD v
    · intro h
      rcases eq_or_ne ((α : Place K F → F) P) 0 with hα0 | hα0
      · left; rw [hα0, mul_zero]
      · right
        have hP := h P
        rw [P.adicValuation_eq_exp_neg_ord hα0, WithZero.exp_le_exp, hEP] at hP
        rw [hordmul hα0]; omega

  have hsurj : Function.Surjective φ := by
    intro c

    obtain ⟨cl, hcl⟩ := IsLocalRing.residue_surjective (R := P.toValuationSubring) c

    set f : F := (cl : F) * t ^ (-(D P)) with hf
    have hαD : Pi.single P f ∈ adeleBdd D := by
      intro v
      by_cases hv : v = P
      · subst v
        simp only [Pi.single_eq_same]
        rcases eq_or_ne (cl : F) 0 with hc0 | hc0
        · rw [hf, hc0, zero_mul, Valuation.map_zero]; exact zero_le'
        · have hf0 : f ≠ 0 := by rw [hf]; exact mul_ne_zero hc0 (zpow_ne_zero _ ht0)
          rw [P.adicValuation_eq_exp_neg_ord hf0, WithZero.exp_le_exp]
          rw [hf, P.ord_mul hc0 (zpow_ne_zero _ ht0), P.ord_zpow, ht1, mul_one]
          have hclnn := P.ord_nonneg_of_mem cl.2
          linarith
      · rw [Pi.single_eq_of_ne hv, Valuation.map_zero]; exact zero_le'
    refine ⟨⟨Pi.single P f, hαD⟩, ?_⟩

    show res (ψ ⟨Pi.single P f, hαD⟩) = c
    rw [hres]
    rw [show (ψ ⟨Pi.single P f, hαD⟩ : P.toValuationSubring) = cl from ?_, hcl]
    apply Subtype.ext
    rw [hψ_apply]
    show t ^ (D P) * (Pi.single P f : Place K F → F) P = (cl : F)
    rw [show (Pi.single P f : Place K F → F) P = f from Pi.single_eq_same _ _, hf,
      mul_comm (cl : F), ← mul_assoc, ← zpow_add₀ ht0, add_neg_cancel, zpow_zero, one_mul]

  exact (Submodule.Quotient.equiv _ _ (LinearEquiv.refl K _) (by rw [← hker]; simp)).trans
    (φ.quotKerEquivOfSurjective hsurj)

theorem finrank_adeleBdd_quotient_single (D : Divisor K F) (P : Place K F)
    [Module.Finite K P.ResidueField] :
    Module.Finite K
        (adeleBdd D ⧸ (adeleBdd (D - Finsupp.single P 1)).comap (adeleBdd D).subtype) ∧
      finrank K
          (adeleBdd D ⧸ (adeleBdd (D - Finsupp.single P 1)).comap (adeleBdd D).subtype)
        = Module.finrank K P.ResidueField := by
  exact ⟨Module.Finite.equiv (adeleBddQuotSingleEquivResidueField D P).symm,
    (adeleBddQuotSingleEquivResidueField D P).finrank_eq⟩


end
end Dubon2026.SourceCurve
