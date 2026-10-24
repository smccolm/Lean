import Dubon2026.SourceJointChartOrderSpaces

/-! DUB-17/18 -> Picard torsion injectivity -> original-field Kummer
power lifting -> genus inequality -> two-chart dimension comparison.
These helpers identify the actual residue chart windows with products of
pole spaces. Adapted from Apache-2.0 FLT commit
6e837e75355538c7f80bab5b956861e86c4eacc2. Existing valuation-ring closure
replaces separate order-addition and scalar-order lemmas. -/
namespace Dubon2026.SourceCurve.RegularProlongation.JointChartAssembly
noncomputable section
open Polynomial
universe u v w

section Window

variable {k : Type u} [Field k] {ι : Type v} {Fb : ι → Type w} [∀ i, Field (Fb i)]
  [∀ i, Algebra k (Fb i)]

/-- The residue coordinate chart, defined by its nonnegative orders. -/
def Bsub (u : ∀ i, Fb i) : Submodule k (∀ i, Fb i) := ordSub fun i w => 0 ≤ w.ord (u i)

/-- The residue inverse-coordinate chart. -/
def Bsub' (u : ∀ i, Fb i) : Submodule k (∀ i, Fb i) := ordSub fun i w => w.ord (u i) ≤ 0

theorem mem_Bsub {u h : ∀ i, Fb i} :
    h ∈ Bsub (k := k) u ↔ ∀ i (w : Place k (Fb i)), 0 ≤ w.ord (u i) → 0 ≤ w.ord (h i) := Iff.rfl

theorem mem_Bsub' {u h : ∀ i, Fb i} :
    h ∈ Bsub' (k := k) u ↔ ∀ i (w : Place k (Fb i)), w.ord (u i) ≤ 0 → 0 ≤ w.ord (h i) := Iff.rfl

theorem Bsub_inv (u : ∀ i, Fb i) : Bsub (k := k) u⁻¹ = Bsub' u := by
  ext h
  simp only [mem_Bsub, mem_Bsub', Pi.inv_apply, Place.ord_inv, neg_nonneg]

theorem Bsub'_inv (u : ∀ i, Fb i) : Bsub' (k := k) u⁻¹ = Bsub u := by
  rw [← Bsub_inv, inv_inv]

theorem Bsub_map_le (u : ∀ i, Fb i) (hu : ∀ i, u i ≠ 0) :
    (Bsub u).map (mulEquiv (k := k) u hu : (∀ i, Fb i) →ₗ[k] (∀ i, Fb i)) ≤ Bsub u := by
  rintro _ ⟨h, hh, rfl⟩ i w hw
  change 0 ≤ w.ord ((u * h) i)
  rcases eq_or_ne (h i) 0 with h0 | h0
  · rw [Pi.mul_apply, h0, mul_zero, Place.ord_zero]
  rw [Pi.mul_apply, Place.ord_mul _ (hu i) h0]
  exact add_nonneg hw (hh i w hw)

theorem nsmul_divisor_apply (D : ∀ i, Divisor k (Fb i)) (M : ℕ) (i : ι) (w : Place k (Fb i)) :
    (M • D i) w = (M : ℤ) * D i w := by
  rw [Finsupp.smul_apply, nsmul_eq_mul]

theorem window_eq (u : ∀ i, Fb i) (hu : ∀ i, u i ≠ 0) (D : ∀ i, Divisor k (Fb i))
    (hD : ∀ i (w : Place k (Fb i)), D i w = max 0 (-w.ord (u i))) (M : ℕ) :
    Bsub u ⊓ (Bsub' u).map ((mulEquiv (k := k) u hu : (∀ i, Fb i) →ₗ[k] (∀ i, Fb i)) ^ M) =
      Submodule.pi Set.univ fun i => LSpace (M • D i) := by
  ext h
  simp only [Submodule.mem_inf, Submodule.mem_map, Submodule.mem_pi, Set.mem_univ, true_implies,
    mulEquiv_pow_apply]
  constructor
  · rintro ⟨hB, g, hg, rfl⟩ i
    rw [mem_lSpace_iff_ord]
    rcases eq_or_ne (g i) 0 with h0 | h0
    · left; simp [h0]
    right
    intro w
    rw [nsmul_divisor_apply, hD i w]
    rcases le_or_gt 0 (w.ord (u i)) with hw | hw
    · rw [max_eq_left (neg_nonpos.mpr hw), mul_zero, neg_zero]
      exact hB i w hw
    · rw [max_eq_right (neg_nonneg.mpr hw.le), Pi.mul_apply, Pi.pow_apply,
        Place.ord_mul _ (pow_ne_zero _ (hu i)) h0, ord_pow']
      have := hg i w hw.le
      linarith
  · intro hh
    refine ⟨fun i w hw => ?_, ⟨(u ^ M)⁻¹ * h, fun i w hw => ?_, ?_⟩⟩
    · rcases (mem_lSpace_iff_ord.mp (hh i)) with h0 | h1
      · rw [h0, Place.ord_zero]
      · have := h1 w
        rw [nsmul_divisor_apply, hD i w, max_eq_left (neg_nonpos.mpr hw), mul_zero,
          neg_zero] at this
        exact this
    · rcases eq_or_ne (h i) 0 with h0 | h0
      · rw [Pi.mul_apply, h0, mul_zero, Place.ord_zero]
      rcases (mem_lSpace_iff_ord.mp (hh i)) with h0' | h1
      · exact absurd h0' h0
      have := h1 w
      rw [nsmul_divisor_apply, hD i w, max_eq_right (neg_nonneg.mpr hw)] at this
      rw [Pi.mul_apply, Pi.inv_apply, Pi.pow_apply,
        Place.ord_mul _ (inv_ne_zero (pow_ne_zero _ (hu i))) h0, Place.ord_inv, ord_pow']
      linarith
    · ext i
      simp [hu i]

end Window

end
end Dubon2026.SourceCurve.RegularProlongation.JointChartAssembly
