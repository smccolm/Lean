/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
import Dubon2026.SourcePeriodPairing

/-! The actual complex-linear period map on the existing integral modular symbols.
Adapted from TauCetiProject/TauCeti 199786c594817a82fdd2fab04d3ae4cc5eb837d5.
DUB-17/18 -> modular Galois association -> integral Hecke finiteness ->
injective, Hecke-adjoint period pairing. The diagonal-action invariance is derived
from the analytic substitution law and the original coefficient representation.
Injectivity and original Hecke adjointness are proved in SourcePeriodInjective and SourceHeckePrimeAdjoint.
-/

namespace Dubon2026.SourceModularSymbols
noncomputable section
open Matrix.SpecialLinearGroup MonoidAlgebra MvPolynomial OnePoint Representation TensorProduct
open scoped MatrixGroups ModularForm

variable {R : Type*} [CommRing R] [Algebra R ℂ]
variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {k : ℤ} {w : ℕ}

/-- **Invariance of the raw pairing.** For a cusp form `f` of weight `w + 2` on `Γ` and `γ ∈ Γ`,
the raw pairing of `f` is invariant under the diagonal action of `γ` on
`Div⁰(ℙ¹(ℚ)) ⊗ Sym^w(R²)`: `⟪f, {γα, γβ} ⊗ (P ∣ γ⁻¹)⟫ = ⟪f, {α, β} ⊗ P⟫`. -/
theorem rawPairing_comp_symbolRep {F : Type*} [FunLike F UpperHalfPlane ℂ]
    [CuspFormClass F (Γ.map (mapGL ℝ)) k] (f : F) (hk : k = w + 2) {γ : SL(2, ℤ)} (hγ : γ ∈ Γ) :
    rawPairing R f hk ∘ₗ symbolRep R w γ = rawPairing R f hk := by
  refine hom_ext_unimodular fun g P ↦ ?_
  rw [LinearMap.comp_apply, symbolRep_tmul, degreeZeroRep_apply,
    degreeZeroGLRep_single_sub_single, rawPairing_single_sub_single_tmul,
    rawPairing_single_sub_single_tmul, sourceCuspIntegral_periodIntegrand_mapGL_smul_of_mem f hk _ hγ,
    sourceModularBinaryFormRep_left_cancel]

/-- The descent of the raw pairing of `f` to `𝕄_w(Γ; R)`, the underlying function of the period
map. -/
private def periodFunctional (hk : k = w + 2) (f : CuspForm (Γ.map (mapGL ℝ)) k) :
    SourceModularSymbols R Γ w →ₗ[R] ℂ :=
  Coinvariants.lift _ (rawPairing R f hk) fun γ ↦ by
    rw [MonoidHom.comp_apply, Subgroup.coe_subtype, rawPairing_comp_symbolRep f hk γ.2]

-- Stated through `periodFunctional` so that it can be rewritten with: the linear maps produced by
-- `Coinvariants.lift` carry the additive structure of `ℂ` as an `AddCommGroup`, which does not
-- match `rawPairing` up to reducible defeq.
private theorem periodFunctional_mk (hk : k = w + 2) (f : CuspForm (Γ.map (mapGL ℝ)) k)
    (x : degreeZero R ⊗[R] homogeneousSubmodule (Fin 2) R w) :
    periodFunctional (R := R) hk f (Coinvariants.mk _ x) = rawPairing R f hk x :=
  Coinvariants.lift_mk _ _ _ x

variable (R Γ) in
/-- The **period map** `S_k(Γ) →ₗ[ℂ] (𝕄_w(Γ; R) →ₗ[R] ℂ)` for `k = w + 2`: a cusp form `f` on
`Γ` is sent to the `R`-linear functional on the modular symbols induced by its raw period
pairing, so that `{α, β} ⊗ P ↦ ∫_β^α f(z) P(z, 1) dz`. For `R = ℤ` this is
the pairing of cusp forms with the integral modular symbols. -/
def periodMap (hk : k = w + 2) :
    CuspForm (Γ.map (mapGL ℝ)) k →ₗ[ℂ] SourceModularSymbols R Γ w →ₗ[R] ℂ where
  toFun := periodFunctional (R := R) hk
  map_add' f g := Coinvariants.hom_ext <| LinearMap.ext fun x ↦ by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.add_apply, periodFunctional_mk,
      periodFunctional_mk, periodFunctional_mk, rawPairing_add, LinearMap.add_apply]
  map_smul' c f := Coinvariants.hom_ext <| LinearMap.ext fun x ↦ by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, RingHom.id_apply, LinearMap.smul_apply,
      periodFunctional_mk, periodFunctional_mk, rawPairing_smul, LinearMap.smul_apply]

/-- On the class of `x ∈ Div⁰(ℙ¹(ℚ)) ⊗ Sym^w(R²)`, the period map is the raw pairing. -/
@[simp]
theorem periodMap_mk (hk : k = w + 2) (f : CuspForm (Γ.map (mapGL ℝ)) k)
    (x : degreeZero R ⊗[R] homogeneousSubmodule (Fin 2) R w) :
    periodMap R Γ hk f (Coinvariants.mk _ x) = rawPairing R f hk x :=
  periodFunctional_mk hk f x

/-- On the symbol `{α, β} ⊗ P`, the period map is the period `∫_β^α f(z) P(z, 1) dz`. -/
theorem periodMap_symbol (hk : k = w + 2) (f : CuspForm (Γ.map (mapGL ℝ)) k) (α β : OnePoint ℚ)
    (P : homogeneousSubmodule (Fin 2) R w) :
    periodMap R Γ hk f (symbol (R := R) (w := w) Γ α β P) = sourceCuspIntegral (periodIntegrand f P) β α := by
  rw [symbol_apply, periodMap_mk, rawPairing_single_sub_single_tmul]

end
end Dubon2026.SourceModularSymbols
