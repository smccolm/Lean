import Dubon2026.FiniteProjectionCommutation

/-! # Finite symmetric kernel decomposition inside a common invariant range -/

namespace Dubon2026

noncomputable section

variable {V I : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- Project a commuting symmetric kernel decomposition into an actual common invariant range. -/
theorem symmetric_product_kernel_inf_range [FiniteDimensional ℂ V]
    (s : Finset I) (A : I → V →ₗ[ℂ] V) (E : V →ₗ[ℂ] V)
    (hc : Set.Pairwise (↑s) (fun i j => Commute (A i) (A j)))
    (hA : ∀ i ∈ s, (A i).IsSymmetric) (hE : IsIdempotentElem E)
    (hAE : ∀ i ∈ s, Commute (A i) E) :
    LinearMap.ker (s.noncommProd A hc) ⊓ LinearMap.range E ≤
      ⨆ i ∈ s, LinearMap.ker (A i) ⊓ LinearMap.range E := by
  have hmap : (LinearMap.ker (s.noncommProd A hc)).map E ≤
      ⨆ i ∈ s, LinearMap.ker (A i) ⊓ LinearMap.range E := by
    rw [symmetric_ker_noncommProd s A hc hA]
    simp only [Submodule.map_iSup]
    apply iSup_le
    intro i
    apply iSup_le
    intro hi
    apply le_trans _ (le_iSup_of_le i (le_iSup_of_le hi le_rfl))
    rintro x ⟨y, hy, rfl⟩
    refine ⟨?_, ⟨y, rfl⟩⟩
    change A i (E y) = 0
    rw [← Module.End.mul_apply, (hAE i hi).eq, Module.End.mul_apply,
      show A i y = 0 from hy, map_zero]
  rintro x ⟨hx, hxE⟩
  apply hmap
  refine ⟨x, hx, ?_⟩
  obtain ⟨y, rfl⟩ := hxE
  exact LinearMap.congr_fun hE y

/-- A common-range vector killed by one symmetric compression is fixed by its actual projection. -/
theorem compressed_kernel_common_range {e p E : V →ₗ[ℂ] V}
    (he : e.IsSymmetric) (hp : p.IsSymmetricProjection) (heE : e * E = E) :
    LinearMap.ker (e * (1 - p) * e) ⊓ LinearMap.range E ≤
      LinearMap.ker (1 - p) ⊓ LinearMap.range E := by
  rintro x ⟨hx, hxE⟩
  have hex : e x = x := by
    obtain ⟨y, rfl⟩ := hxE
    exact LinearMap.congr_fun heE y
  have hz : e (x - p x) = 0 := by
    change e (e x - p (e x)) = 0 at hx
    simpa only [hex] using hx
  have hpx := symmetric_projection_compression_kernel he hp x hex hz
  exact ⟨show x - p x = 0 by rw [hpx, sub_self], hxE⟩

end
end Dubon2026
