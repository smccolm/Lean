import Dubon2026.NumberFieldIdeleClassGaloisAction
import Dubon2026.NumberFieldSUnitGaloisAction

/-! # Original Galois-equivariant supported-idele maps

Stability of the actual support preserves the original supported ideles.
The original principal S-unit and quotient maps intertwine the actual
actions, supplying the equivariant sequence needed by DUB-17's norm index.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
variable (S : Set (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)
include hS

/-- The actual Galois maps preserve the original supported ideles for stable S. -/
theorem numberFieldSupportedIdele_galois_mem (σ : Gal(L/K))
    (a : (AdeleRing (𝓞 L) L)ˣ) (ha : a ∈ numberFieldSupportedIdeles L S) :
    numberFieldIdeleGaloisMap K L σ a ∈ numberFieldSupportedIdeles L S := by
  simp only [numberFieldSupportedIdeles, Subgroup.mem_iInf, Subgroup.mem_comap,
    HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one] at ha ⊢
  intro w hw
  let v := (numberFieldGaloisPlaceEquiv K L σ).symm w
  have hvw : numberFieldGaloisPlaceEquiv K L σ v = w :=
    (numberFieldGaloisPlaceEquiv K L σ).apply_symm_apply w
  have hv : v ∉ S := fun hv => hw (hvw ▸ (hS σ v).mp hv)
  have h := numberFieldIdeleGaloisMap_finite_valuation K L σ a v
  rw [hvw] at h
  exact h.trans (ha v hv)

/-- The original Galois map restricted to the original supported-idele subgroup. -/
def numberFieldSupportedIdeleGaloisMap (σ : Gal(L/K)) :
    numberFieldSupportedIdeles L S →* numberFieldSupportedIdeles L S where
  toFun a := ⟨numberFieldIdeleGaloisMap K L σ a.val,
    numberFieldSupportedIdele_galois_mem K L S hS σ a.val a.property⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ a.val b.val)

/-- The actual Galois action on the original supported ideles. -/
@[reducible]
def numberFieldSupportedIdeleGaloisAction :
    MulDistribMulAction Gal(L/K) (numberFieldSupportedIdeles L S) where
  smul σ a := numberFieldSupportedIdeleGaloisMap K L S hS σ a
  one_smul a := Subtype.ext (numberFieldIdeleGaloisMap_one K L a.val)
  mul_smul σ τ a := Subtype.ext (numberFieldIdeleGaloisMap_mul K L σ τ a.val)
  smul_one σ := map_one (numberFieldSupportedIdeleGaloisMap K L S hS σ)
  smul_mul σ := map_mul (numberFieldSupportedIdeleGaloisMap K L S hS σ)

/-- The original principal S-unit map is equivariant for the actual original actions. -/
theorem numberFieldSupportedPrincipalIdele_galois :
    letI := numberFieldSUnitGaloisAction K L S hS
    letI := numberFieldSupportedIdeleGaloisAction K L S hS
    ∀ (σ : Gal(L/K)) (x : S.unit L),
      numberFieldSupportedPrincipalIdele L S (σ • x) =
        σ • numberFieldSupportedPrincipalIdele L S x := by
  intro σ x
  apply Subtype.ext
  exact (numberFieldPrincipalIdele_galois K L σ x.val).symm

/-- The original supported class map is equivariant for the actual original actions. -/
theorem numberFieldSupportedIdeleClassMap_galois :
    letI := numberFieldSupportedIdeleGaloisAction K L S hS
    letI := numberFieldIdeleClassGaloisAction K L
    ∀ (σ : Gal(L/K)) (a : numberFieldSupportedIdeles L S),
      numberFieldSupportedIdeleClassMap L S (σ • a) =
        σ • numberFieldSupportedIdeleClassMap L S a := by
  intro σ a
  exact (numberFieldIdeleClassGaloisMap_mk K L σ a.val).symm

end
end Dubon2026
