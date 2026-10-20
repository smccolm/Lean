/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import Dubon2026.SourceIntegralHeckeAction

/-! The actual integral prime Hecke operators on original Gamma0 modular symbols.
The finite permutation proofs reuse `HeckePrimeOrbits` and `HeckePrimeReindex`,
including bad primes. This discharges the integral quotient descent needed for
Hecke adjointness, then finite integral Hecke algebra on the DUB-17/DUB-18
modular Galois association route. Adjointness and all-index assembly follow.
-/

namespace Dubon2026
namespace SourceModularSymbols

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup HeckePrimeReindex
open MvPolynomial Representation TensorProduct
open scoped MatrixGroups
noncomputable section

variable {R : Type*} [CommRing R] {w Q p : ℕ} [NeZero p]

private theorem triangularSymbolSum_comp (σ : SL(2, ℤ)) :
    (∑ b : Fin p, triangularSymbolMap R w (Gamma0 Q) 1 p b.val) ∘ₗ symbolRep R w σ =
      ∑ b : Fin p, triangularSymbolMap R w (Gamma0 Q) 1 p b.val ∘ₗ symbolRep R w σ := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, LinearMap.sum_apply]

/-- When the lower entry is divisible by p, the original upper symbol maps permute. -/
theorem triangularSymbolSum_comp_of_lower_dvd (hp : Nat.Prime p)
    (σ : SL(2, ℤ)) (hσ : σ ∈ Gamma0 Q) (hC : (p : ℤ) ∣ σ.val 1 0) :
    (∑ b : Fin p, triangularSymbolMap R w (Gamma0 Q) 1 p b.val) ∘ₗ symbolRep R w σ =
      ∑ b : Fin p, triangularSymbolMap R w (Gamma0 Q) 1 p b.val := by
  rw [triangularSymbolSum_comp]
  refine Finset.sum_equiv (Equiv.ofBijective _
    (Finite.injective_iff_bijective.mp (moebiusFin_injective p hp σ.val σ.prop)))
    (fun _ => ⟨fun _ => Finset.mem_univ _, fun _ => Finset.mem_univ _⟩) ?_
  intro b _
  exact triangularSymbolMap_factor (Gamma0 Q) b.val
    (moebiusFin p hp σ.val b).val σ (heckePrime_upper_factor hp σ hσ b
      (not_dvd_topLeft_add_of_dvd_botLeft p hp σ.val (sl2z_fin_two_det_eq_one σ) hC b.val))

/-- The canonical pole exchanges one upper symbol map with the diagonal map. -/
theorem primeSymbolSum_comp_of_lower_not_dvd (hp : Nat.Prime p)
    (σ : SL(2, ℤ)) (hσ : σ ∈ Gamma0 Q) (hC : ¬(p : ℤ) ∣ σ.val 1 0) :
    ((∑ b : Fin p, triangularSymbolMap R w (Gamma0 Q) 1 p b.val) +
        triangularSymbolMap R w (Gamma0 Q) p 1 0) ∘ₗ symbolRep R w σ =
      (∑ b : Fin p, triangularSymbolMap R w (Gamma0 Q) 1 p b.val) +
        triangularSymbolMap R w (Gamma0 Q) p 1 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  let b₀ : Fin p := ⟨(-(σ.val 0 0 : ZMod p) * (σ.val 1 0 : ZMod p)⁻¹).val, ZMod.val_lt _⟩
  have hb₀ : (p : ℤ) ∣ σ.val 0 0 + b₀.val * σ.val 1 0 :=
    dvd_topLeft_add_canonicalIndex p hp σ.val
      (fun h => hC ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h))
  have hupper (b : Fin p) :
      triangularSymbolMap R w (Gamma0 Q) 1 p b.val ∘ₗ symbolRep R w σ =
        if (p : ℤ) ∣ σ.val 0 0 + b.val * σ.val 1 0 then
          triangularSymbolMap R w (Gamma0 Q) p 1 0 else
          triangularSymbolMap R w (Gamma0 Q) 1 p (moebiusFin p hp σ.val b).val := by
    split_ifs with h
    · exact triangularSymbolMap_factor (Gamma0 Q) b.val 0 σ
        (heckePrime_upper_pole_factor σ hσ b h)
    · exact triangularSymbolMap_factor (Gamma0 Q) b.val _ σ
        (heckePrime_upper_factor hp σ hσ b h)
  have hlower :
      triangularSymbolMap R w (Gamma0 Q) p 1 0 ∘ₗ symbolRep R w σ =
        triangularSymbolMap R w (Gamma0 Q) 1 p (moebiusFin p hp σ.val b₀).val := by
    have hm : (moebiusFin p hp σ.val b₀).val =
        ((σ.val 1 1 : ZMod p) * (σ.val 1 0 : ZMod p)⁻¹).val := by
      simp only [moebiusFin, (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hb₀, if_true]
    rw [hm]
    exact triangularSymbolMap_factor (Gamma0 Q) 0 _ σ (heckePrime_lower_factor hp σ hσ hC)
  rw [LinearMap.add_comp, triangularSymbolSum_comp]
  simp_rw [hupper]
  rw [hlower]
  exact sum_ite_swap_eq (fun b : Fin p => triangularSymbolMap R w (Gamma0 Q) 1 p b.val)
    (triangularSymbolMap R w (Gamma0 Q) p 1 0) (moebiusFin p hp σ.val)
    (Finite.injective_iff_bijective.mp (moebiusFin_injective p hp σ.val σ.prop)) b₀ _
    (dvd_topLeft_add_iff_eq_canonicalIndex p hp σ.val σ.prop b₀ hb₀)

variable (R w Q p)

/-- The literal finite sum of integral symbol maps at the prime index. -/
def primeSymbolPreMap :
    degreeZero R ⊗[R] homogeneousSubmodule (Fin 2) R w →ₗ[R]
      SourceModularSymbols R (Gamma0 Q) w :=
  (∑ b : Fin p, triangularSymbolMap R w (Gamma0 Q) 1 p b.val) +
    if Nat.Coprime p Q then triangularSymbolMap R w (Gamma0 Q) p 1 0 else 0

variable {R w Q p}

/-- The actual prime sum respects the original Gamma0 relation, also at primes dividing Q. -/
theorem primeSymbolPreMap_comp (hp : Nat.Prime p)
    (σ : SL(2, ℤ)) (hσ : σ ∈ Gamma0 Q) :
    primeSymbolPreMap R w Q p ∘ₗ symbolRep R w σ = primeSymbolPreMap R w Q p := by
  unfold primeSymbolPreMap
  by_cases hpQ : Nat.Coprime p Q
  · simp only [if_pos hpQ]
    by_cases hC : (p : ℤ) ∣ σ.val 1 0
    · rw [LinearMap.add_comp, triangularSymbolSum_comp_of_lower_dvd hp σ hσ hC,
        triangularSymbolMap_factor (Gamma0 Q) 0 0 σ
          (heckePrime_lower_div_factor hpQ σ hσ hC)]
    · exact primeSymbolSum_comp_of_lower_not_dvd hp σ hσ hC
  · simp only [if_neg hpQ, add_zero]
    have hpQdvd : p ∣ Q := by
      by_contra h
      exact hpQ (hp.coprime_iff_not_dvd.mpr h)
    have hC : (p : ℤ) ∣ σ.val 1 0 := dvd_trans
      (Int.natCast_dvd_natCast.mpr hpQdvd)
      ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hσ))
    exact triangularSymbolSum_comp_of_lower_dvd hp σ hσ hC

variable (R w Q)

/-- The original prime Hecke action is a genuine endomorphism of integral modular symbols. -/
def integralHeckePrime (hp : Nat.Prime p) :
    Module.End R (SourceModularSymbols R (Gamma0 Q) w) := by
  unfold SourceModularSymbols Coinvariants
  refine Submodule.liftQ _ (primeSymbolPreMap R w Q p) ?_
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨σ, x⟩, rfl⟩
  change primeSymbolPreMap R w Q p (symbolRep R w σ.val x - x) = 0
  rw [map_sub, sub_eq_zero]
  exact congrArg (fun L => L x) (primeSymbolPreMap_comp (R := R) (w := w) hp σ.val σ.property)

variable {R w Q}

/-- The quotient endomorphism is represented by the literal original prime sum. -/
theorem integralHeckePrime_mk (hp : Nat.Prime p)
    (x : degreeZero R ⊗[R] homogeneousSubmodule (Fin 2) R w) :
    integralHeckePrime R w Q hp
        (Coinvariants.mk (V := degreeZero R ⊗[R] homogeneousSubmodule (Fin 2) R w)
          ((symbolRep R w).comp (Gamma0 Q).subtype) x) =
      primeSymbolPreMap R w Q p x := rfl

end
end SourceModularSymbols
end Dubon2026
