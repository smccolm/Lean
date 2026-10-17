import Dubon2026.OriginalIdeleInfiniteH2
import Dubon2026.OriginalCyclicClassH2Surjectivity
import Dubon2026.OriginalIdeleClassFiniteGaloisCohomology
import Mathlib.Topology.Instances.AddCircle.Defs

/-! # Full order from the actual principal kernel and infinite vanishing

Test a multiple of the same normalized finite-idele witness in the exact
original class-map kernel. Its principal preimage has zero original
infinite localization, so the proved finite-total kernel condition detects
that multiple. The original class-card bound supplies the reverse
divisibility. This avoids an auxiliary extension of a real functional on
DUB-17's same-stage full-order class chain.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- A normalized original idele witness with zero infinite coordinates
has full-order class image when the finite total kills the actual
principal kernel with zero original infinite localization. -/
theorem originalIdeleClass_full_order_of_infinite_kernel
    (total : groupCohomology (originalFullIdeleRep K L) 2 →+ AddCircle (1 : ℚ))
    (hkill : ∀ y : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2,
      (∀ v : NumberField.InfinitePlace L, originalGlobalInfiniteH2 K L v y = 0) →
      total ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalFullPrincipalRepHom K L) y) = 0)
    (x : groupCohomology (originalFullIdeleRep K L) 2)
    (hx : total x = (↑((1 : ℚ) / Module.finrank K L) : AddCircle (1 : ℚ)))
    (hi : ∀ v : NumberField.InfinitePlace L, originalFullIdeleInfiniteH2 K L v x = 0) :
    addOrderOf ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalFullClassRepHom K L) x) =
      Module.finrank K L := by
  let cl := ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalFullClassRepHom K L)).hom
  let pr := ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalFullPrincipalRepHom K L)).hom
  let u := cl x
  let n := addOrderOf u
  have hk : n • x ∈ LinearMap.ker cl := by
    change cl (n • x) = 0
    exact (map_nsmul cl n x).trans (addOrderOf_nsmul_eq_zero u)
  have hr : n • x ∈ LinearMap.range pr := by
    rw [← originalFullClassH2_ker_eq_principal_range K L]
    exact hk
  obtain ⟨y, hy⟩ := hr
  have hyi (v : NumberField.InfinitePlace L) : originalGlobalInfiniteH2 K L v y = 0 := by
    rw [← originalFullIdeleInfiniteH2_principal K L v y]
    change originalFullIdeleInfiniteH2 K L v (pr y) = 0
    rw [hy, map_nsmul, hi v, nsmul_zero]
  have hn : n • (↑((1 : ℚ) / Module.finrank K L) : AddCircle (1 : ℚ)) = 0 := by
    have ht := hkill y hyi
    change total (pr y) = 0 at ht
    rw [hy, map_nsmul, hx] at ht
    exact ht
  have ho : addOrderOf (↑((1 : ℚ) / Module.finrank K L) : AddCircle (1 : ℚ)) =
      Module.finrank K L := by
    letI : Fact (0 < (1 : ℚ)) := ⟨by norm_num⟩
    exact AddCircle.addOrderOf_period_div (p := (1 : ℚ)) (Module.finrank_pos (R := K) (M := L))
  have hlo : Module.finrank K L ∣ n := ho ▸ addOrderOf_dvd_of_nsmul_eq_zero hn
  have hhi : n ∣ Module.finrank K L :=
    (addOrderOf_dvd_natCard u).trans (originalIdeleClass_finiteGalois_second_card_dvd K L).2
  exact Nat.dvd_antisymm hhi hlo

end
end Dubon2026
