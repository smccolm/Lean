import Dubon2026.SourceModularSmoothCover
import Dubon2026.ModularPeterssonLevel

/-! Adapted from anthropics/fermats-last-theorem (Apache-2.0), frozen primary
Def_ModularCurve_SmoothedFundamental and
S_ModularCurve_contDiff_and_finsum_smoothedFundamental_eq_one;
exact hashes are recorded in modular-smooth-partition-route-875.json.
DUB-17/18 -> actual Gamma1 Picard/H1 -> Abel-Jacobi converse ->
analytic reciprocity -> winding-period limit -> compact smooth modular
partition. The native group/coset equivalence preserves the exact chosen
coset representatives; no separate bijection or orbit-sum assumption is
introduced. The integral normalization remains a separate obligation. -/
namespace Dubon2026.SourceSmoothedFundamental
noncomputable section
open UpperHalfPlane hiding I coe_smul
open Filter Complex MulAction Set
open scoped MatrixGroups Topology ContDiff Pointwise
local notation "𝕌" => UpperHalfPlane.upperHalfPlaneSet

section Support

variable (Γ : Subgroup SL(2, ℤ)) (T : ℝ)

theorem im_pos_of_puCut_mob_ne_zero {T : ℝ} {σ : SL(2, ℤ)} {z : ℂ} (h : puCut T (mob σ z) ≠ 0) :
    0 < z.im :=
  im_pos_of_im_mob_pos σ (im_pos_of_bump_ne_zero (support_pu_subset T (left_ne_zero_of_mul h)))

/-- Inverse modular translate of the cutoff rectangle, viewed in C. -/
def piece (T : ℝ) (σ : SL(2, ℤ)) : Set ℂ := ((↑) : ℍ → ℂ) '' (σ⁻¹ • boxH T)

theorem isCompact_piece (σ : SL(2, ℤ)) : IsCompact (piece T σ) :=
  ((isCompact_boxH T).smul σ⁻¹).image continuous_coe

theorem piece_subset (σ : SL(2, ℤ)) : piece T σ ⊆ 𝕌 := by
  rintro _ ⟨τ, -, rfl⟩; exact τ.im_pos

theorem mem_piece_of_ne_zero {T : ℝ} {σ : SL(2, ℤ)} {z : ℂ} (h : puCut T (mob σ z) ≠ 0) :
    z ∈ piece T σ := by
  have hz := im_pos_of_puCut_mob_ne_zero h
  refine ⟨⟨z, hz⟩, ?_, rfl⟩
  rw [Set.mem_inv_smul_set_iff]
  show ((σ • (⟨z, hz⟩ : ℍ) : ℍ) : ℂ) ∈ box T
  rw [coe_smul]
  exact support_puCut_subset T h

theorem puCut_mob_contDiff (σ : SL(2, ℤ)) (n : ℕ∞) : ContDiff ℝ n fun z => puCut T (mob σ z) := by
  refine contDiff_iff_contDiffAt.2 fun z => ?_
  rcases lt_or_ge 0 z.im with hz | hz
  · exact (puCut_contDiff T n).contDiffAt.comp z (mob_contDiffAt σ hz n)
  · have hzK : z ∉ piece T σ := fun h => absurd (piece_subset T σ h) (not_lt.2 hz)
    have hev : (fun w => puCut T (mob σ w)) =ᶠ[𝓝 z] fun _ => 0 := by
      filter_upwards [(isCompact_piece T σ).isClosed.isOpen_compl.mem_nhds hzK] with w hw
      by_contra h
      exact hw (mem_piece_of_ne_zero h)
    exact contDiffAt_const.congr_of_eventuallyEq hev

variable [Γ.FiniteIndex]

/-- Finite coset type of the actual finite-index subgroup. -/
scoped instance quotientFintype : Fintype (SL(2, ℤ) ⧸ Γ) := Fintype.ofFinite _

/-- Finite union of inverse translates indexed by the actual subgroup cosets. -/
def carrier : Set ℂ := ⋃ q : SL(2, ℤ) ⧸ Γ, piece T (Quotient.out q)

theorem isCompact_carrier : IsCompact (carrier Γ T) :=
  isCompact_iUnion fun q => isCompact_piece T q.out

omit [Γ.FiniteIndex] in
theorem carrier_subset : carrier Γ T ⊆ 𝕌 :=
  Set.iUnion_subset fun q => piece_subset T q.out

theorem mem_carrier_of_ne_zero {z : ℂ} (h : smoothedFundamental Γ T z ≠ 0) :
    z ∈ carrier Γ T := by
  rw [smoothedFundamental_eq_sum] at h
  obtain ⟨q, -, hq⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  exact Set.mem_iUnion.2 ⟨q, mem_piece_of_ne_zero hq⟩

theorem eq_zero_of_notMem_carrier {z : ℂ} (h : z ∉ carrier Γ T) :
    smoothedFundamental Γ T z = 0 := by
  by_contra h'; exact h (mem_carrier_of_ne_zero Γ T h')

theorem hasCompactSupport : HasCompactSupport (smoothedFundamental Γ T) :=
  HasCompactSupport.intro (isCompact_carrier Γ T) fun _ hz => eq_zero_of_notMem_carrier Γ T hz

theorem tsupport_subset : tsupport (smoothedFundamental Γ T) ⊆ 𝕌 :=
  (closure_minimal (fun _ hz => mem_carrier_of_ne_zero Γ T hz)
    (isCompact_carrier Γ T).isClosed).trans (carrier_subset Γ T)

theorem contDiff (n : ℕ∞) : ContDiff ℝ n (smoothedFundamental Γ T) := by
  have : smoothedFundamental Γ T =
      fun z => ∑ q : SL(2, ℤ) ⧸ Γ, puCut T (mob (Quotient.out q) z) :=
    funext (smoothedFundamental_eq_sum Γ T)
  rw [this]
  exact ContDiff.sum fun q _ => puCut_mob_contDiff T _ n

end Support


end
end Dubon2026.SourceSmoothedFundamental
