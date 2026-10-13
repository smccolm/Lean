import Dubon2026.OriginalIdeleNorm
import Dubon2026.OriginalInfiniteNormGaloisProduct
import Dubon2026.SupportedIdeleCoordinates
import Mathlib.GroupTheory.Coset.Card

/-! # Actual local norm preimages from archimedean decomposition cosets

Evaluating the original full Galois product at an actual infinite place
and grouping the factors by its actual decomposition subgroup gives a
local decomposition-group norm. This is the concrete component comparison
needed for local norm containment in DUB-17's norm-index upper-bound chain.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
attribute [local instance] IsCyclic.commGroup
variable (w : InfinitePlace L)

omit [NumberField K] [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)] in
/-- Evaluation at an original prime intertwines its actual decomposition-group action. -/
theorem originalIdeleInfiniteComponent_decomposition
    (σ : OriginalInfiniteDecompositionGroup K L w) (a : (AdeleRing (𝓞 L) L)ˣ) :
    numberFieldIdeleInfiniteComponent L w (numberFieldIdeleGaloisMap K L σ.val a) =
      Units.map (numberFieldGaloisArchimedeanTransport K L σ.val w w σ.property).toMonoidHom
        (numberFieldIdeleInfiniteComponent L w a) := by
  apply Units.ext
  exact numberFieldInfiniteAdeleGaloisMap_apply K L σ.val a.val.1 w w σ.property

/-- The actual product of transported coset components in the original local unit group. -/
def originalIdeleInfiniteOrbitNormPreimage (a : (AdeleRing (𝓞 L) L)ˣ) : (w.Completion)ˣ :=
  ∏ q : Gal(L/K) ⧸ OriginalInfiniteDecompositionGroup K L w,
    numberFieldIdeleInfiniteComponent L w (numberFieldIdeleGaloisMap K L q.out a)

omit [NumberField K] [IsGalois K L] in
/-- Grouping the actual original Galois components by decomposition cosets gives the local group norm. -/
theorem originalIdeleInfiniteOrbitNormPreimage_product (a : (AdeleRing (𝓞 L) L)ˣ) :
    (∏ σ : Gal(L/K), numberFieldIdeleInfiniteComponent L w (numberFieldIdeleGaloisMap K L σ a)) =
      ∏ τ : OriginalInfiniteDecompositionGroup K L w,
        Units.map (numberFieldGaloisArchimedeanTransport K L τ.val w w τ.property).toMonoidHom
          (originalIdeleInfiniteOrbitNormPreimage K L w a) := by
  let D := OriginalInfiniteDecompositionGroup K L w
  let f (σ : Gal(L/K)) := numberFieldIdeleInfiniteComponent L w (numberFieldIdeleGaloisMap K L σ a)
  have hq (p : (Gal(L/K) ⧸ D) × D) : (QuotientGroup.mk (p.1.out * p.2.val) : Gal(L/K) ⧸ D) = p.1 := by
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff p.2.val).mpr p.2.property, mul_one]
    exact Quotient.out_eq' p.1
  let e : (Gal(L/K) ⧸ D) × D ≃ Gal(L/K) := {
    toFun p := p.1.out * p.2.val
    invFun σ := (QuotientGroup.mk σ, ⟨(QuotientGroup.mk σ : Gal(L/K) ⧸ D).out⁻¹ * σ,
      QuotientGroup.eq.mp (Quotient.out_eq' (QuotientGroup.mk σ : Gal(L/K) ⧸ D))⟩)
    left_inv p := by
      apply Prod.ext (hq p)
      apply Subtype.ext
      change (QuotientGroup.mk (p.1.out * p.2.val) : Gal(L/K) ⧸ D).out⁻¹ *
        (p.1.out * p.2.val) = p.2.val
      rw [hq, inv_mul_cancel_left]
    right_inv σ := mul_inv_cancel_left _ _ }
  have he : (∏ p : (Gal(L/K) ⧸ D) × D, f (p.1.out * p.2.val)) = ∏ σ : Gal(L/K), f σ :=
    Fintype.prod_equiv e _ _ (fun _ => rfl)
  have hf (q : Gal(L/K) ⧸ D) (τ : D) :
      f (q.out * τ.val) = Units.map
        (numberFieldGaloisArchimedeanTransport K L τ.val w w τ.property).toMonoidHom (f q.out) := by
    dsimp [f]
    rw [mul_comm q.out τ.val, numberFieldIdeleGaloisMap_mul]
    exact originalIdeleInfiniteComponent_decomposition K L w τ _
  change (∏ σ : Gal(L/K), f σ) = _
  rw [← he, Fintype.prod_prod_type]
  simp_rw [hf]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro τ _
  exact (map_prod (Units.map
    (numberFieldGaloisArchimedeanTransport K L τ.val w w τ.property).toMonoidHom) _ _).symm

end
end Dubon2026
