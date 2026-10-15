import Dubon2026.ArithmeticSUnitKummerSequence
import Mathlib.Algebra.Module.Submodule.Equiv

/-! # Actual root-valued Hom coefficients and arithmetic S-units

For original coefficients killed by q, every integer-linear map into the
actual S-units factors uniquely through the original root inclusion. This
identifies the Hom coefficient in the global Ext route with the root-valued
dual coefficient, retaining evaluation and the actual conjugate Galois action.
It does not identify positive Ext with continuous cohomology.
-/

namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance 1100] Rep.hV2

variable (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
  (a : 𝓞 K) (ha : a ≠ 0) (q : ℕ) [Fact q.Prime]

omit [Fact q.Prime] in
/-- The actual S-unit q-power coefficient map is multiplication by the original integer q. -/
theorem originalArithmeticSUnitPower_eq_zsmul
    (x : originalArithmeticSUnitRepresentation K Ω a ha) :
    (originalArithmeticSUnitPower K Ω a ha q).hom x = (q : ℤ) • x := by
  rw [natCast_zsmul]
  rfl

variable (A : Rep ℤ Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K))
  (hqA : ∀ x : A, (q : ℤ) • x = 0)

include hqA in
/-- The literal values of every map from q-torsion coefficients are in the actual root image. -/
theorem originalArithmeticSUnitHom_mem_root_range
    (f : A →ₗ[ℤ] originalArithmeticSUnitRepresentation K Ω a ha) (x : A) :
    f x ∈ LinearMap.range (originalArithmeticSUnitKummerInclusion K Ω a ha q).hom.toLinearMap := by
  rw [originalArithmeticSUnitKummerCoefficient_exact]
  change (originalArithmeticSUnitPower K Ω a ha q).hom (f x) = 0
  rw [originalArithmeticSUnitPower_eq_zsmul]
  calc
    (q : ℤ) • f x = f ((q : ℤ) • x) := (f.toAddMonoidHom.map_zsmul (q : ℤ) x).symm
    _ = 0 := by rw [hqA, map_zero]

/-- Factor an actual integer-linear S-unit-valued map through the original root inclusion. -/
def originalArithmeticSUnitHomRootLift
    (f : A →ₗ[ℤ] originalArithmeticSUnitRepresentation K Ω a ha) :
    A →ₗ[ℤ] galoisRootOfUnityRepresentation (K := K)
      (Ω := originalUnramifiedGaloisUnion (Ω := Ω) a) q :=
  LinearMap.codRestrictOfInjective f
    (originalArithmeticSUnitKummerInclusion K Ω a ha q).hom.toLinearMap
    (originalArithmeticSUnitKummerInclusion_injective K Ω a ha q)
    (originalArithmeticSUnitHom_mem_root_range K Ω a ha q A hqA f)

/-- The lifted original root map recovers every original S-unit value exactly. -/
theorem originalArithmeticSUnitHomRootLift_evaluation
    (f : A →ₗ[ℤ] originalArithmeticSUnitRepresentation K Ω a ha) (x : A) :
    (originalArithmeticSUnitKummerInclusion K Ω a ha q).hom
      (originalArithmeticSUnitHomRootLift K Ω a ha q A hqA f x) = f x :=
  LinearMap.codRestrictOfInjective_comp_apply _ _ _ _ x

/-- Original postcomposition with root inclusion is the integer-linear map on Hom coefficients. -/
def originalArithmeticRootHomToSUnitHom :
    (A →ₗ[ℤ] galoisRootOfUnityRepresentation (K := K)
      (Ω := originalUnramifiedGaloisUnion (Ω := Ω) a) q) →ₗ[ℤ]
        (A →ₗ[ℤ] originalArithmeticSUnitRepresentation K Ω a ha) where
  toFun f := (originalArithmeticSUnitKummerInclusion K Ω a ha q).hom.toLinearMap.comp f
  map_add' f g := by
    ext x
    exact (originalArithmeticSUnitKummerInclusion K Ω a ha q).hom.map_add (f x) (g x)
  map_smul' n f := by
    ext x
    exact (originalArithmeticSUnitKummerInclusion K Ω a ha q).hom.map_smul n (f x)

/-- The original Cartier Hom coefficient is identified with actual S-unit-valued Hom,
using the derived root range and unique lifting rather than an assumed Hom comparison. -/
def originalArithmeticSUnitCartierHomEquiv :
    (A →ₗ[ℤ] galoisRootOfUnityRepresentation (K := K)
      (Ω := originalUnramifiedGaloisUnion (Ω := Ω) a) q) ≃ₗ[ℤ]
        (A →ₗ[ℤ] originalArithmeticSUnitRepresentation K Ω a ha) :=
  LinearEquiv.ofBijective (originalArithmeticRootHomToSUnitHom K Ω a ha q A) ⟨by
    intro f g h
    ext x
    apply originalArithmeticSUnitKummerInclusion_injective K Ω a ha q
    exact LinearMap.congr_fun h x, by
    intro f
    refine ⟨originalArithmeticSUnitHomRootLift K Ω a ha q A hqA f, ?_⟩
    ext x
    exact originalArithmeticSUnitHomRootLift_evaluation K Ω a ha q A hqA f x⟩

/-- The Hom identification is literal evaluation followed by the original root inclusion. -/
theorem originalArithmeticSUnitCartierHomEquiv_apply
    (f : A →ₗ[ℤ] galoisRootOfUnityRepresentation (K := K)
      (Ω := originalUnramifiedGaloisUnion (Ω := Ω) a) q) (x : A) :
    originalArithmeticSUnitCartierHomEquiv K Ω a ha q A hqA f x =
      (originalArithmeticSUnitKummerInclusion K Ω a ha q).hom (f x) := rfl

/-- The actual Hom coefficient identification preserves the original conjugate Galois action. -/
theorem originalArithmeticSUnitCartierHomEquiv_equivariant
    (g : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K))
    (f : A →ₗ[ℤ] galoisRootOfUnityRepresentation (K := K)
      (Ω := originalUnramifiedGaloisUnion (Ω := Ω) a) q) :
    originalArithmeticSUnitCartierHomEquiv K Ω a ha q A hqA
      (Representation.linHom A.ρ (galoisRootOfUnityRepresentation (K := K)
        (Ω := originalUnramifiedGaloisUnion (Ω := Ω) a) q).ρ g f) =
      Representation.linHom A.ρ (originalArithmeticSUnitRepresentation K Ω a ha).ρ g
        (originalArithmeticSUnitCartierHomEquiv K Ω a ha q A hqA f) := by
  ext x
  exact LinearMap.congr_fun
    ((originalArithmeticSUnitKummerInclusion K Ω a ha q).hom.isIntertwining' g)
    (f (A.ρ g⁻¹ x))

end
end Dubon2026
