import Dubon2026.OriginalIdeleClassBaseChange
import Mathlib.RingTheory.Norm.Transitivity

/-! # The actual original idele norm by Galois descent

The product of all actual original Galois conjugates descends uniquely to
an original base idele. Its principal values are the actual field norm.
This is the native class-norm comparison required for DUB-17's norm-index
lower bound and subsequent reciprocity/global duality dependency chain.
-/

namespace Dubon2026
noncomputable section
open NumberField
open scoped NumberField
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

omit [NumberField K] [IsGalois K L] in
/-- The product of the actual original Galois conjugates is fixed. -/
theorem originalIdeleGaloisProduct_fixed (a : (AdeleRing (𝓞 L) L)ˣ) (τ : Gal(L/K)) :
    numberFieldIdeleGaloisMap K L τ (∏ σ : Gal(L/K), numberFieldIdeleGaloisMap K L σ a) =
      ∏ σ : Gal(L/K), numberFieldIdeleGaloisMap K L σ a := by
  rw [map_prod]
  simp_rw [← numberFieldIdeleGaloisMap_mul]
  exact Fintype.prod_equiv (Equiv.mulLeft τ) _ _ (fun _ => rfl)

/-- The unique descended Galois product defines the actual original idele norm. -/
def originalIdeleNorm : (AdeleRing (𝓞 L) L)ˣ →* (AdeleRing (𝓞 K) K)ˣ := by
  let f (a : (AdeleRing (𝓞 L) L)ˣ) :=
    (originalIdeleBaseChangeMap_surjective_fixed K L _ (originalIdeleGaloisProduct_fixed K L a)).choose
  have hf (a) : originalIdeleBaseChangeMap K L (f a) =
      ∏ σ : Gal(L/K), numberFieldIdeleGaloisMap K L σ a :=
    (originalIdeleBaseChangeMap_surjective_fixed K L _ (originalIdeleGaloisProduct_fixed K L a)).choose_spec
  exact {
    toFun := f
    map_one' := by
      apply originalIdeleBaseChangeMap_injective K L
      rw [hf, map_one]
      simp only [map_one, Finset.prod_const_one]
    map_mul' := by
      intro a b
      apply originalIdeleBaseChangeMap_injective K L
      rw [hf, map_mul, hf, hf]
      simp only [map_mul, Finset.prod_mul_distrib]
  }

/-- The actual original idele norm has exactly the original Galois-product image. -/
theorem originalIdeleBaseChangeMap_norm (a : (AdeleRing (𝓞 L) L)ˣ) :
    originalIdeleBaseChangeMap K L (originalIdeleNorm K L a) =
      ∏ σ : Gal(L/K), numberFieldIdeleGaloisMap K L σ a :=
  (originalIdeleBaseChangeMap_surjective_fixed K L _ (originalIdeleGaloisProduct_fixed K L a)).choose_spec

/-- On original principal ideles the norm is the actual original extension-field norm. -/
theorem originalIdeleNorm_principal (x : Lˣ) :
    originalIdeleNorm K L (numberFieldPrincipalIdele L x) =
      numberFieldPrincipalIdele K (Units.map (Algebra.norm K (S := L)) x) := by
  apply originalIdeleBaseChangeMap_injective K L
  rw [originalIdeleBaseChangeMap_norm, originalIdeleBaseChangeMap_principal]
  simp_rw [numberFieldPrincipalIdele_galois]
  rw [← map_prod]
  congr 1
  apply Units.ext
  change (∏ σ : Gal(L/K), (σ • x : Lˣ)).val = algebraMap K L (Algebra.norm K x.val)
  rw [Units.coe_prod]
  exact (Algebra.norm_eq_prod_automorphisms K x.val).symm

/-- The norm of an original base idele is its extension-degree power. -/
theorem originalIdeleNorm_baseChange (a : (AdeleRing (𝓞 K) K)ˣ) :
    originalIdeleNorm K L (originalIdeleBaseChangeMap K L a) = a ^ Module.finrank K L := by
  apply originalIdeleBaseChangeMap_injective K L
  rw [originalIdeleBaseChangeMap_norm, map_pow]
  simp_rw [originalIdeleBaseChangeMap_fixed]
  rw [Finset.prod_const, Finset.card_univ, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]

end
end Dubon2026
