import Dubon2026.SourceOriginalHeckeCosetPrimitiveDerivative
import Dubon2026.SourceComplexPrimitiveGluing
import Mathlib.Topology.LocallyConstant.Basic

/-! DUB-17/18 -> original Picard-period Hecke comparison -> identifying
the primitive coset trace with the actual analytic Hecke transform.
The proved weight-two slash trace gives equal derivatives. Existing
local primitive uniqueness and connectedness of the upper half-plane
then give equality of every endpoint difference, without a choice of
integration constants or a supplied Hecke compatibility assumption.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane CongruenceSubgroup Filter
open scoped Topology MatrixGroups
variable (N p : ℕ) [NeZero N] [NeZero p]

private local instance : Fintype (Gamma0 N ⧸ heckeUpperSubgroup N p) :=
  sourceHeckeUpperFintype N p

theorem originalHeckePrimitiveTrace_hasDerivAt (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f : CuspForm (Gamma0 N) 2) (τ : ℍ) :
    HasDerivAt (fun z : ℂ => ∑ q : Gamma0 N ⧸ heckeUpperSubgroup N p,
      sourceWeightTwoPrimitive 1 f (originalHeckeCosetPoint N p (ofComplex z) q))
      (cuspHeckePrime hp f τ) (τ : ℂ) := by
  have hd := HasDerivAt.fun_sum (u := Finset.univ)
    (fun q _ => originalHeckeCosetPrimitive_hasDerivAt N p hp f q τ)
  apply hd.congr_deriv
  simpa only [Finset.sum_apply] using congrFun (sourceWeightTwoHeckeCoset_sum hp hpN f) τ

theorem originalHeckePrimitiveTrace_difference (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f : CuspForm (Gamma0 N) 2) (τ₀ τ₁ : ℍ) :
    (∑ q : Gamma0 N ⧸ heckeUpperSubgroup N p,
      (sourceWeightTwoPrimitive 1 f (originalHeckeCosetPoint N p τ₁ q) -
        sourceWeightTwoPrimitive 1 f (originalHeckeCosetPoint N p τ₀ q))) =
      sourceWeightTwoPrimitive 1 (cuspHeckePrime hp f) τ₁ -
        sourceWeightTwoPrimitive 1 (cuspHeckePrime hp f) τ₀ := by
  let F : ℍ → ℂ := fun τ => ∑ q : Gamma0 N ⧸ heckeUpperSubgroup N p,
    sourceWeightTwoPrimitive 1 f (originalHeckeCosetPoint N p τ q)
  let G := sourceWeightTwoPrimitive 1 (cuspHeckePrime hp f)
  have hlc : IsLocallyConstant (fun τ : ℍ => F τ - G τ) := by
    apply (IsLocallyConstant.iff_eventually_eq _).mpr
    intro τ
    have h₁ : ∀ᶠ z : ℂ in 𝓝 (τ : ℂ),
        HasDerivAt (F ∘ ofComplex) (cuspHeckePrime hp f (ofComplex z)) z := by
      filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos] with z hz
      have hd := originalHeckePrimitiveTrace_hasDerivAt N p hp hpN f (⟨z, hz⟩ : ℍ)
      simpa only [ofComplex_apply_of_im_pos hz] using hd
    have h₂ : ∀ᶠ z : ℂ in 𝓝 (τ : ℂ),
        HasDerivAt (G ∘ ofComplex) (cuspHeckePrime hp f (ofComplex z)) z := by
      filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos] with z hz
      have hd := sourceWeightTwoPrimitive_hasDerivAt (cuspHeckePrime hp f) (by norm_num)
        (ModularRatios.one_mem_strictPeriods N) (⟨z, hz⟩ : ℍ)
      simpa only [ofComplex_apply_of_im_pos hz] using hd
    have he := UpperHalfPlane.continuous_coe.continuousAt.eventually
      (OriginalPrimitiveGlue.eventually_sub_eq_of_hasDerivAt h₁ h₂)
    simpa only [Function.comp_apply, ofComplex_apply] using he
  have he := hlc.apply_eq_of_preconnectedSpace τ₁ τ₀
  change F τ₁ - G τ₁ = F τ₀ - G τ₀ at he
  rw [Finset.sum_sub_distrib]
  change F τ₁ - F τ₀ = G τ₁ - G τ₀
  linear_combination he

end
end Dubon2026.SourceFunctionField
