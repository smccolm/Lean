import Dubon2026.SupportedIdeleLocalFactorEquiv
import Dubon2026.SupportedIdeleCoordinateAction
import Dubon2026.SupportedIdeleRepresentations

/-! # Equivariant decomposition of the original supported-idele representation

The proved literal local-coordinate formulas intertwine the original
supported-idele Galois action and the actual completion/integer-unit
transports. Thus the original cohomology functor applies to the actual
local-factor decomposition required by DUB-17's global norm-index chain.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical
attribute [local instance 1100] Rep.hV2
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)

/-- The actual unrestricted and outside-support original local factors as a product representation. -/
def supportedIdeleLocalFactorRep : Rep ℤ Gal(L/K) :=
  Rep.of ((supportedUnrestrictedUnitRep K L S hS).ρ.prod (supportedOutsideUnitRep K L S hS).ρ)

/-- The original supported-idele representation is isomorphic to its actual transported local factors. -/
def supportedIdeleLocalFactorRepIso :
    originalSupportedIdeleRep K L S hS ≅ supportedIdeleLocalFactorRep K L S hS := by
  letI := sUnitStableFinitePlaceAction K L S hS
  letI := supportedOutsidePlaceAction K L S hS
  apply Rep.mkIso
  refine Representation.Equiv.mk (supportedIdeleLocalFactorLinearEquiv L S) ?_
  intro σ
  apply LinearMap.ext
  intro a
  apply Prod.ext
  · funext p
    cases p with
    | inl w =>
      exact numberFieldSupportedIdeleCoordinate_infinite_galois K L S hS σ a.toMul
        (σ⁻¹ • w) w (smul_inv_smul σ w)
    | inr w =>
      exact numberFieldSupportedIdeleCoordinate_finite_galois K L S hS σ a.toMul
        (σ⁻¹ • w).val w.val (congrArg Subtype.val (smul_inv_smul σ w))
  · funext w
    apply Units.ext
    apply Subtype.ext
    exact numberFieldFiniteAdeleGaloisMap_apply K L σ a.toMul.val.val.2
      (σ⁻¹ • w).val w.val (congrArg Subtype.val (smul_inv_smul σ w))

/-- The representation isomorphism retains the actual original local-coordinate linear equivalence. -/
theorem supportedIdeleLocalFactorRepIso_hom_apply
    (a : Additive (numberFieldSupportedIdeles L S)) :
    (supportedIdeleLocalFactorRepIso K L S hS).hom.hom a =
      supportedIdeleLocalFactorLinearEquiv L S a := rfl

/-- Original supported-idele cohomology is that of the actual transported local-factor representation. -/
def supportedIdeleLocalFactorCohomologyIso (n : ℕ) :
    groupCohomology (originalSupportedIdeleRep K L S hS) n ≅
      groupCohomology (supportedIdeleLocalFactorRep K L S hS) n :=
  (groupCohomology.functor ℤ Gal(L/K) n).mapIso (supportedIdeleLocalFactorRepIso K L S hS)

end
end Dubon2026
