import Dubon2026.OriginalLocalNormUnitProducts

/-! # The original idele norm for one selected infinite place per fiber

When an original idele has unit coordinate one at the other upper primes
over a base place, evaluating its actual Galois product leaves exactly the
local decomposition-group norm at the selected prime. This is the norm
identity needed by DUB-17's actual restricted-product preimage assembly.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

attribute [-instance] UniformSpace.Completion.instSMul in
/-- If other original upper coordinates over the actual base prime are one, the original idele norm component is the selected actual local norm. -/
theorem originalIdeleNorm_infiniteComponent_of_onePlace (w : InfinitePlace L)
    (a : (AdeleRing (𝓞 L) L)ˣ)
    (ha : ∀ u : InfinitePlace L, u.comap (algebraMap K L) = w.comap (algebraMap K L) →
      u ≠ w → numberFieldIdeleInfiniteComponent L u a = 1) :
    numberFieldIdeleInfiniteComponent K (w.comap (algebraMap K L)) (originalIdeleNorm K L a) =
      originalInfiniteLocalNorm K L w (numberFieldIdeleInfiniteComponent L w a) := by
  let D := OriginalInfiniteDecompositionGroup K L w
  let f (σ : Gal(L/K)) := numberFieldIdeleInfiniteComponent L w (numberFieldIdeleGaloisMap K L σ a)
  have hout (σ : {σ : Gal(L/K) // σ ∉ D}) : f σ.val = 1 := by
    let u := σ.val⁻¹ • w
    have hu : σ.val • u = w := smul_inv_smul σ.val w
    have hb : u.comap (algebraMap K L) = w.comap (algebraMap K L) :=
      ((InfinitePlace.mem_orbit_iff (k := K) (K := L)).mp ⟨σ.val⁻¹, rfl⟩).symm
    have hn : u ≠ w := by
      intro h
      apply σ.property
      change σ.val • w = w
      simpa only [h] using hu
    have hv := congrArg Units.val (ha u hb hn)
    change a.val.1 u = 1 at hv
    apply Units.ext
    change numberFieldInfiniteAdeleGaloisMap K L σ.val a.val.1 w = 1
    rw [numberFieldInfiniteAdeleGaloisMap_apply K L σ.val a.val.1 u w hu, hv, map_one]
  have hp : (∏ σ : Gal(L/K), f σ) = ∏ τ : D, f τ.val := by
    have h := Fintype.prod_subtype_mul_prod_subtype (fun σ : Gal(L/K) => σ ∈ D) f
    have hother : (∏ σ : {σ : Gal(L/K) // σ ∉ D}, f σ.val) = 1 := by
      apply Finset.prod_eq_one
      intro σ _
      exact hout σ
    rw [hother, mul_one] at h
    exact h.symm
  apply Units.map_injective (originalInfiniteCompletionBaseChange K L w).injective
  rw [← originalIdeleBaseChangeMap_infiniteComponent, originalIdeleBaseChangeMap_norm, map_prod,
    originalInfiniteLocalNorm_baseChange]
  exact hp.trans (Finset.prod_congr rfl (fun τ _ => originalIdeleInfiniteComponent_decomposition K L w τ a))

end
end Dubon2026
