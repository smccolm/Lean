import Dubon2026.GaloisKummerCoefficientSequence
import Mathlib.Algebra.Module.Submodule.Equiv

/-! # Actual root-valued Hom coefficients and local Galois units

This is the local coefficient edge for the finite relation route to reverse
localization. The native Kummer coefficient sequence identifies Hom into roots
with Hom into the original extension-field units whenever the source is killed
by the same integer. The map retains literal evaluation and Galois action.
-/

namespace Dubon2026
noncomputable section
attribute [local instance 1100] Rep.hV2

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (q : ℕ)

/-- The actual extension-field unit q-power coefficient map is multiplication by the original integer q. -/
theorem galoisUnitPower_eq_zsmul
    (x : Rep.ofAlgebraAutOnUnits K Ω) :
    (galoisKummerPower (K := K) (Ω := Ω) q).hom x = (q : ℤ) • x := by
  rw [natCast_zsmul]
  rfl

variable (A : Rep ℤ Gal(Ω/K))
  (hqA : ∀ x : A, (q : ℤ) • x = 0)

include hqA in
/-- The literal values of every map from q-torsion coefficients are in the actual root image. -/
theorem galoisUnitHom_mem_root_range
    (f : A →ₗ[ℤ] Rep.ofAlgebraAutOnUnits K Ω) (x : A) :
    f x ∈ LinearMap.range (galoisKummerInclusion (K := K) (Ω := Ω) q).hom.toLinearMap := by
  rw [galoisKummerCoefficient_exact]
  change (galoisKummerPower (K := K) (Ω := Ω) q).hom (f x) = 0
  rw [galoisUnitPower_eq_zsmul]
  calc
    (q : ℤ) • f x = f ((q : ℤ) • x) := (f.toAddMonoidHom.map_zsmul (q : ℤ) x).symm
    _ = 0 := by rw [hqA, map_zero]

/-- Factor an actual integer-linear extension-field unit-valued map through the original root inclusion. -/
def galoisUnitHomRootLift
    (f : A →ₗ[ℤ] Rep.ofAlgebraAutOnUnits K Ω) :
    A →ₗ[ℤ] galoisRootOfUnityRepresentation (K := K)
      (Ω := Ω) q :=
  LinearMap.codRestrictOfInjective f
    (galoisKummerInclusion (K := K) (Ω := Ω) q).hom.toLinearMap
    (galoisKummerInclusion_injective (K := K) (Ω := Ω) q)
    (galoisUnitHom_mem_root_range K Ω q A hqA f)

/-- The lifted original root map recovers every original extension-field unit value exactly. -/
theorem galoisUnitHomRootLift_evaluation
    (f : A →ₗ[ℤ] Rep.ofAlgebraAutOnUnits K Ω) (x : A) :
    (galoisKummerInclusion (K := K) (Ω := Ω) q).hom
      (galoisUnitHomRootLift K Ω q A hqA f x) = f x :=
  LinearMap.codRestrictOfInjective_comp_apply _ _ _ _ x

/-- Original postcomposition with root inclusion is the integer-linear map on Hom coefficients. -/
def galoisRootHomToUnitHom :
    (A →ₗ[ℤ] galoisRootOfUnityRepresentation (K := K)
      (Ω := Ω) q) →ₗ[ℤ]
        (A →ₗ[ℤ] Rep.ofAlgebraAutOnUnits K Ω) where
  toFun f := (galoisKummerInclusion (K := K) (Ω := Ω) q).hom.toLinearMap.comp f
  map_add' f g := by
    ext x
    exact (galoisKummerInclusion (K := K) (Ω := Ω) q).hom.map_add (f x) (g x)
  map_smul' n f := by
    ext x
    exact (galoisKummerInclusion (K := K) (Ω := Ω) q).hom.map_smul n (f x)

/-- The original Cartier Hom coefficient is identified with actual extension-field unit-valued Hom,
using the derived root range and unique lifting rather than an assumed Hom comparison. -/
def galoisUnitCartierHomEquiv :
    (A →ₗ[ℤ] galoisRootOfUnityRepresentation (K := K)
      (Ω := Ω) q) ≃ₗ[ℤ]
        (A →ₗ[ℤ] Rep.ofAlgebraAutOnUnits K Ω) :=
  LinearEquiv.ofBijective (galoisRootHomToUnitHom K Ω q A) ⟨by
    intro f g h
    ext x
    apply galoisKummerInclusion_injective (K := K) (Ω := Ω) q
    exact LinearMap.congr_fun h x, by
    intro f
    refine ⟨galoisUnitHomRootLift K Ω q A hqA f, ?_⟩
    ext x
    exact galoisUnitHomRootLift_evaluation K Ω q A hqA f x⟩

/-- The Hom identification is literal evaluation followed by the original root inclusion. -/
theorem galoisUnitCartierHomEquiv_apply
    (f : A →ₗ[ℤ] galoisRootOfUnityRepresentation (K := K)
      (Ω := Ω) q) (x : A) :
    galoisUnitCartierHomEquiv K Ω q A hqA f x =
      (galoisKummerInclusion (K := K) (Ω := Ω) q).hom (f x) := rfl

/-- The actual Hom coefficient identification preserves the original conjugate Galois action. -/
theorem galoisUnitCartierHomEquiv_equivariant
    (g : Gal(Ω/K))
    (f : A →ₗ[ℤ] galoisRootOfUnityRepresentation (K := K)
      (Ω := Ω) q) :
    galoisUnitCartierHomEquiv K Ω q A hqA
      (Representation.linHom A.ρ (galoisRootOfUnityRepresentation (K := K)
        (Ω := Ω) q).ρ g f) =
      Representation.linHom A.ρ (Rep.ofAlgebraAutOnUnits K Ω).ρ g
        (galoisUnitCartierHomEquiv K Ω q A hqA f) := by
  ext x
  exact LinearMap.congr_fun
    ((galoisKummerInclusion (K := K) (Ω := Ω) q).hom.isIntertwining' g)
    (f (A.ρ g⁻¹ x))

end
end Dubon2026
