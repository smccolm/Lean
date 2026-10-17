import Dubon2026.OriginalClassFullOrderFromInfiniteKernel
import Dubon2026.OriginalClassH2InvariantFromGenerator

/-! # The normalized class invariant on original ideles with zero infinite image

The native full-order generator constructs the injective class invariant.
For any other original idele with zero infinite localizations, subtract a
multiple of the same normalized witness. Exactness makes the difference
principal and the proved infinite-kernel condition identifies its finite
total. This supplies the class-zero test needed to transfer DUB-17's
constructed cyclic witness to an arbitrary enlarged original stage.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance 1100] Rep.hV2

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- The constructed normalized class invariant agrees with the finite
total on every original idele class with zero original infinite localization. -/
theorem originalIdeleClass_exists_invariant_on_infinite_kernel
    (n : ℕ) (hdegree : Module.finrank K L = n)
    (total : groupCohomology (originalFullIdeleRep K L) 2 →+ AddCircle (1 : ℚ))
    (hkill : ∀ y : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2,
      (∀ v : NumberField.InfinitePlace L, originalGlobalInfiniteH2 K L v y = 0) →
      total ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalFullPrincipalRepHom K L) y) = 0)
    (hwitness : ∃ x₀ : groupCohomology (originalFullIdeleRep K L) 2,
      total x₀ = (↑((1 : ℚ) / n) : AddCircle (1 : ℚ)) ∧
      ∀ v : NumberField.InfinitePlace L, originalFullIdeleInfiniteH2 K L v x₀ = 0) :
    ∃ invG : groupCohomology (originalIdeleClassRep K L) 2 →+ AddCircle (1 : ℚ),
      Function.Injective invG ∧
      (∀ t : AddCircle (1 : ℚ), t ∈ invG.range ↔ n • t = 0) ∧
      ∀ x : groupCohomology (originalFullIdeleRep K L) 2,
        (∀ v : NumberField.InfinitePlace L, originalFullIdeleInfiniteH2 K L v x = 0) →
        invG ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalFullClassRepHom K L) x) = total x := by
  subst n
  obtain ⟨x₀, hn, h₀⟩ := hwitness
  let cl := ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalFullClassRepHom K L)).hom
  let pr := ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalFullPrincipalRepHom K L)).hom
  have ho := originalIdeleClass_full_order_of_infinite_kernel K L total hkill x₀ hn h₀
  obtain ⟨invG, hInj, hRange, hNorm, _⟩ := originalIdeleClass_exists_invariants_of_full_order K L (cl x₀) ho
  have hgen := originalIdeleClass_full_order_generates K L (cl x₀) ho
  refine ⟨invG, hInj, hRange, ?_⟩
  intro x hx
  obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp (hgen (cl x))
  have hk : x - m • x₀ ∈ LinearMap.ker cl := by
    change cl (x - m • x₀) = 0
    exact (map_sub cl x (m • x₀)).trans
      ((congrArg (fun t => cl x - t) (map_zsmul cl m x₀)).trans
        ((congrArg (fun t => cl x - t) hm).trans (sub_self _)))
  have hr : x - m • x₀ ∈ LinearMap.range pr := by
    rw [← originalFullClassH2_ker_eq_principal_range K L]
    exact hk
  obtain ⟨y, hy⟩ := hr
  have hyi (v : NumberField.InfinitePlace L) : originalGlobalInfiniteH2 K L v y = 0 := by
    rw [← originalFullIdeleInfiniteH2_principal K L v y]
    change originalFullIdeleInfiniteH2 K L v (pr y) = 0
    rw [hy, map_sub, map_zsmul, hx v, h₀ v, zsmul_zero, sub_self]
  have ht := hkill y hyi
  change total (pr y) = 0 at ht
  rw [hy, map_sub, map_zsmul, sub_eq_zero] at ht
  change invG (cl x) = total x
  rw [← hm, map_zsmul, hNorm, ht, hn]

end
end Dubon2026
