import Dubon2026.FiniteGroupProjection

/-! # Commutation and compression of genuine finite-group projections -/

namespace Dubon2026

noncomputable section

section Algebra
variable {G H V : Type*} [Group G] [Group H] [Fintype G] [Fintype H]
  [AddCommGroup V] [Module ℂ V]

/-- Commuting with every group operator implies commuting with its literal average. -/
theorem finiteGroupProjection_commute_operator (ρ : Representation ℂ G V)
    (A : V →ₗ[ℂ] V) (hA : ∀ g, Commute A (ρ g)) :
    Commute A (finiteGroupProjection ρ) := by
  rw [finiteGroupProjection_eq]
  exact (Commute.sum_right Finset.univ ρ A (fun g _ => hA g)).smul_right _

/-- Commuting finite group actions have commuting orthogonal averages. -/
theorem finiteGroupProjection_commute (ρ : Representation ℂ G V) (σ : Representation ℂ H V)
    (h : ∀ g h, Commute (ρ g) (σ h)) :
    Commute (finiteGroupProjection ρ) (finiteGroupProjection σ) := by
  apply finiteGroupProjection_commute_operator
  intro h'
  exact (finiteGroupProjection_commute_operator ρ (σ h') (fun g => (h g h').symm)).symm

omit [Fintype G] in
/-- Averaging an independent commuting action preserves actual fixed vectors. -/
theorem finiteGroupProjection_preserves_invariants (ρ : Representation ℂ G V)
    (σ : Representation ℂ H V) (h : ∀ g h, Commute (ρ g) (σ h))
    (x : V) (hx : ∀ g, ρ g x = x) (g : G) :
    ρ g (finiteGroupProjection σ x) = finiteGroupProjection σ x := by
  have hc := finiteGroupProjection_commute_operator σ (ρ g) (h g)
  rw [← Module.End.mul_apply, hc.eq, Module.End.mul_apply, hx g]

end Algebra

section InnerProduct
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- Symmetric compression remains symmetric without assuming that the compressed operators commute. -/
theorem symmetric_compression {e A : V →ₗ[ℂ] V} (he : e.IsSymmetric)
    (hA : A.IsSymmetric) : (e * A * e).IsSymmetric := by
  intro x y
  simp only [Module.End.mul_apply]
  rw [he, hA, he]

/-- On the actual range of an idempotent symmetric operator, compressed projection-complement
kernels are exactly fixed vectors of the uncompressed orthogonal projection. -/
theorem symmetric_compression_kernel_range {e p : V →ₗ[ℂ] V}
    (he : e.IsSymmetricProjection) (hp : p.IsSymmetricProjection) :
    LinearMap.ker (e * (1 - p) * e) ⊓ LinearMap.range e =
      LinearMap.ker (1 - p) ⊓ LinearMap.range e := by
  apply le_antisymm
  · rintro x ⟨hx, hxe⟩
    have hex : e x = x := by
      obtain ⟨y, rfl⟩ := hxe
      exact LinearMap.congr_fun he.isIdempotentElem y
    have hzero : e (x - p x) = 0 := by
      change e (e x - p (e x)) = 0 at hx
      simpa only [hex] using hx
    have hpx := symmetric_projection_compression_kernel he.isSymmetric hp x hex hzero
    exact ⟨show x - p x = 0 by rw [hpx, sub_self], hxe⟩
  · rintro x ⟨hx, hxe⟩
    have hex : e x = x := by
      obtain ⟨y, rfl⟩ := hxe
      exact LinearMap.congr_fun he.isIdempotentElem y
    refine ⟨?_, hxe⟩
    change e (e x - p (e x)) = 0
    rw [hex, show x - p x = 0 from hx, map_zero]

end InnerProduct
end
end Dubon2026
