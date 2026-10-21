import Dubon2026.SourcePrimeHeckeNaturality

/-! The actual invariant represented by a nonzero native H1 inclusion kernel.
DUB-17/18 -> residual modular Galois association -> character-to-weight-two
reduction -> survival of the function-flag eigenclass or the Eisenstein
exception -> the original coefficient primitive of a class killed by inclusion.
The cocycle calculation is adapted from anthropics/fermats-last-theorem,
revision 6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_HeckeEis_isEigensystemH1_or_of_isEigensystemH1_of_injective.lean.txt
(Apache-2.0; retained LICENSE and NOTICE), using native Rep and native H1.
-/

namespace Dubon2026
noncomputable section
open CategoryTheory groupCohomology

variable {F G : Type} [Field F] [Group G] (A B : Rep F G) (f : A ⟶ B)

/-- The range of an actual equivariant coefficient morphism is invariant. -/
theorem sourceNativeCoefficient_range_stable (g : G) {x : B}
    (hx : x ∈ LinearMap.range f.hom.toLinearMap) :
    B.ρ g x ∈ LinearMap.range f.hom.toLinearMap := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨A.ρ g y, LinearMap.congr_fun (f.hom.isIntertwining' g) y⟩

/-- A nonzero native H1 class killed by an actual coefficient inclusion
has a primitive with a nonzero component in the specified invariant quotient.
The quotient's spanning condition is the narrower coefficient input. -/
theorem sourceNativeH1_kernel_representative (hf : Function.Injective f)
    (q : B)
    (hq : ∀ v : B, (∀ g : G, B.ρ g v - v ∈ LinearMap.range f.hom.toLinearMap) →
      ∃ r : F, v - r • q ∈ LinearMap.range f.hom.toLinearMap)
    (c : cocycles₁ A)
    (hzero : ((groupCohomology.functor F G 1).map f) (H1π A c) = 0)
    (hne : H1π A c ≠ 0) :
    ∃ (v : B) (r : F), r ≠ 0 ∧
      (∀ g : G, B.ρ g v - v = f (c g)) ∧
      v - r • q ∈ LinearMap.range f.hom.toLinearMap ∧
      ∀ g : G, B.ρ g q - q ∈ LinearMap.range f.hom.toLinearMap := by
  change groupCohomology.map (MonoidHom.id G) f 1 (H1π A c) = 0 at hzero
  rw [H1π_comp_map_apply, H1π_eq_zero_iff] at hzero
  obtain ⟨v, hv⟩ := hzero
  have hvg : ∀ g : G, B.ρ g v - v = f (c g) := fun g => congrFun hv g
  obtain ⟨r, hr⟩ := hq v (fun g => ⟨c g, (hvg g).symm⟩)
  have hr0 : r ≠ 0 := by
    intro h
    rw [h, zero_smul, sub_zero] at hr
    obtain ⟨a, ha⟩ := hr
    apply hne
    apply (H1π_eq_zero_iff c).mpr
    refine ⟨a, funext fun g => ?_⟩
    change A.ρ g a - a = c g
    apply hf
    change f.hom.toLinearMap (A.ρ g a - a) = f.hom.toLinearMap (c g)
    have hfa : f.hom.toLinearMap (A.ρ g a) = B.ρ g (f.hom.toLinearMap a) :=
      LinearMap.congr_fun (f.hom.isIntertwining' g) a
    rw [map_sub, hfa, ha]
    exact hvg g
  refine ⟨v, r, hr0, hvg, hr, fun g => ?_⟩
  have hmem : B.ρ g (v - r • q) - (v - r • q) ∈ LinearMap.range f.hom.toLinearMap :=
    Submodule.sub_mem _ (sourceNativeCoefficient_range_stable A B f g hr) hr
  have hz : B.ρ g v - v ∈ LinearMap.range f.hom.toLinearMap := ⟨c g, (hvg g).symm⟩
  have he : r • (B.ρ g q - q) =
      (B.ρ g v - v) - (B.ρ g (v - r • q) - (v - r • q)) := by
    simp only [map_sub, map_smul, smul_sub]
    abel
  have hs : r • (B.ρ g q - q) ∈ LinearMap.range f.hom.toLinearMap := by
    rw [he]
    exact Submodule.sub_mem _ hz hmem
  have h := Submodule.smul_mem _ r⁻¹ hs
  rwa [smul_smul, inv_mul_cancel₀ hr0, one_smul] at h

/-- Original group action preserves a prescribed invariant quotient component. -/
theorem sourceNativeCoefficient_range_congr (q : B)
    (hq : ∀ g : G, B.ρ g q - q ∈ LinearMap.range f.hom.toLinearMap)
    (g : G) (s : F) {x : B} (hx : x - s • q ∈ LinearMap.range f.hom.toLinearMap) :
    B.ρ g x - s • q ∈ LinearMap.range f.hom.toLinearMap := by
  have he : B.ρ g x - s • q = B.ρ g (x - s • q) + s • (B.ρ g q - q) := by
    simp only [map_sub, map_smul, smul_sub]
    abel
  rw [he]
  exact Submodule.add_mem _ (sourceNativeCoefficient_range_stable A B f g hx)
    (Submodule.smul_mem _ s (hq g))

end
end Dubon2026
