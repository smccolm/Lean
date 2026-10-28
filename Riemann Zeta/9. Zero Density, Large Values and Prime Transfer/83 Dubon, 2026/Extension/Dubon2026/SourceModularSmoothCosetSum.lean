import Mathlib

/-! Adapted from anthropics/fermats-last-theorem (Apache-2.0), frozen primary
Def_ModularCurve_SmoothedFundamental and
S_ModularCurve_contDiff_and_finsum_smoothedFundamental_eq_one;
exact hashes are recorded in modular-smooth-partition-route-875.json.
DUB-17/18 -> actual Gamma1 Picard/H1 -> Abel-Jacobi converse ->
analytic reciprocity -> winding-period limit -> compact smooth modular
partition. The exact chosen-representative coset decomposition is proved explicitly.
Native groupEquivQuotientProdSubgroup was checked; its opaque subtype casts
make the required representative formula less direct than this short proof. The integral normalization remains a separate obligation. -/
namespace Dubon2026.SourceSmoothedFundamental
noncomputable section
open UpperHalfPlane hiding I coe_smul
open Filter Complex MulAction Set
open scoped MatrixGroups Topology ContDiff Pointwise
local notation "𝕌" => UpperHalfPlane.upperHalfPlaneSet

variable {G : Type*} [Group G] (Γ : Subgroup G)

/-- Exact chosen-representative coset decomposition used by the finite orbit sum. -/
def cosetEquiv : (G ⧸ Γ) × Γ ≃ G where
  toFun p := p.1.out * p.2
  invFun g := ((g : G ⧸ Γ), ⟨(Quotient.out (g : G ⧸ Γ))⁻¹ * g,
    QuotientGroup.eq.1 (QuotientGroup.out_eq' (g : G ⧸ Γ))⟩)
  left_inv p := by
    obtain ⟨q, γ⟩ := p
    have hq : ((q.out * (γ : G) : G) : G ⧸ Γ) = q := by
      rw [QuotientGroup.mk_mul_of_mem _ γ.2, QuotientGroup.out_eq']
    ext
    · exact hq
    · simp only
      rw [hq, inv_mul_cancel_left]
  right_inv g := by
    simp only
    rw [mul_inv_cancel_left]

theorem finsum_sum_coset [Fintype (G ⧸ Γ)] {M : Type*} [AddCommMonoid M] (f : G → M)
    (hf : Function.HasFiniteSupport f) :
    ∑ᶠ γ : Γ, ∑ q : G ⧸ Γ, f (q.out * γ) = ∑ᶠ g : G, f g := by
  have hinj : ∀ q : G ⧸ Γ, Function.HasFiniteSupport fun γ : Γ => f (q.out * γ) := by
    intro q
    refine (hf.preimage (f := fun γ : Γ => q.out * (γ : G)) ?_)
    exact (fun a _ b _ h => Subtype.ext (mul_left_cancel h))
  rw [finsum_sum_comm _ (fun (γ : Γ) (q : G ⧸ Γ) => f (q.out * γ)) fun q _ => hinj q]
  have hF : Function.HasFiniteSupport fun p : (G ⧸ Γ) × Γ => f (cosetEquiv Γ p) :=
    hf.preimage (cosetEquiv Γ).injective.injOn
  rw [← finsum_comp_equiv (cosetEquiv Γ) (f := f), finsum_curry _ hF, finsum_eq_sum_of_fintype]
  rfl


end
end Dubon2026.SourceSmoothedFundamental
