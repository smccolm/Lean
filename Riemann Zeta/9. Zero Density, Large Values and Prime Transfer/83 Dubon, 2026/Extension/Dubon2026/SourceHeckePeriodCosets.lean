import Dubon2026.SourceHeckeSymbolTrace
import Dubon2026.SourceHeckeCohomology

/-! The original analytic periods as an exact Hecke coset sum.
DUB-17/18 -> residual modular Galois association -> original H1 Hecke
compatibility. The already proved integral-symbol trace identity supplies
the analytic sum. No new integration or convergence assumption is used.
-/

namespace Dubon2026
noncomputable section
open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup SourceModularSymbols
open MvPolynomial TensorProduct MulOpposite
open scoped MatrixGroups

variable {p Q : ℕ} [NeZero p]

/-- The genuine rational matrix attached to each original Hecke coset. -/
def sourceHeckeCuspRepresentative (q : Gamma0 Q ⧸ heckeUpperSubgroup Q p) :
    GL (Fin 2) ℚ :=
  heckeTriangularRat 1 p 0 * mapGL ℚ q.out.val⁻¹

/-- The cusp representatives satisfy the actual conjugation-transition identity. -/
theorem sourceHeckeCuspRepresentative_transition (hp : Nat.Prime p)
    (γ : Gamma0 Q) (q : Gamma0 Q ⧸ heckeUpperSubgroup Q p) :
    sourceHeckeCuspRepresentative (γ • q) * mapGL ℚ γ.val =
      mapGL ℚ (sourceHeckeConjugation hp (cosetTransition (heckeUpperSubgroup Q p) γ q)).val *
        sourceHeckeCuspRepresentative q := by
  have ht : (γ • q).out⁻¹ * γ =
      (cosetTransition (heckeUpperSubgroup Q p) γ q).val * q.out⁻¹ := by
    change _ = ((γ • q).out⁻¹ * (γ * q.out)) * q.out⁻¹
    group
  have hm := congrArg (fun g : Gamma0 Q => mapGL ℚ g.val) ht
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul] at hm
  calc
    _ = heckeTriangularRat 1 p 0 *
        (mapGL ℚ (γ • q).out.val⁻¹ * mapGL ℚ γ.val) := mul_assoc _ _ _
    _ = heckeTriangularRat 1 p 0 *
        (mapGL ℚ (cosetTransition (heckeUpperSubgroup Q p) γ q).val.val *
          mapGL ℚ q.out.val⁻¹) := congrArg (heckeTriangularRat 1 p 0 * ·) hm
    _ = (heckeTriangularRat 1 p 0 *
        mapGL ℚ (cosetTransition (heckeUpperSubgroup Q p) γ q).val.val) *
          mapGL ℚ q.out.val⁻¹ := (mul_assoc _ _ _).symm
    _ = (mapGL ℚ (sourceHeckeConjugation hp (cosetTransition (heckeUpperSubgroup Q p) γ q)).val *
        heckeTriangularRat 1 p 0) * mapGL ℚ q.out.val⁻¹ :=
      congrArg (· * mapGL ℚ q.out.val⁻¹)
        (sourceHeckeConjugation_integral hp (cosetTransition (heckeUpperSubgroup Q p) γ q)).1
    _ = _ := mul_assoc _ _ _

variable [NeZero Q] {k : ℤ} {w : ℕ}

/-- One genuine symbol-coset term is the actual transformed cusp period. -/
theorem sourceHeckeSymbolCoset_period (hp : Nat.Prime p)
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : k = w + 2)
    (q : Gamma0 Q ⧸ heckeUpperSubgroup Q p) (α β : OnePoint ℚ)
    (P : homogeneousSubmodule (Fin 2) ℂ w) :
    periodMap ℂ (Gamma0 Q) hk f
        (sourceHeckeSymbolCoset ℂ w Q hp q
          (⟨_, single_sub_single_mem_degreeZero α β⟩ ⊗ₜ P)) =
      ((sourcePeriodDualRep (Gamma0 Q) w).ρ q.out
        (sourceHeckeDualDiagonal w p
          (sourcePeriodBetween f hk
            (sourceHeckeCuspRepresentative q • α) (sourceHeckeCuspRepresentative q • β)))) P := by
  rw [sourceHeckeSymbolCoset_out, LinearMap.comp_apply, symbolRep_tmul,
    degreeZeroRep_apply, degreeZeroGLRep_single_sub_single]
  change periodMap ℂ (Gamma0 Q) hk f (Representation.Coinvariants.mk _
    ((TensorProduct.map (degreeZeroGLRep ℂ (heckeTriangularRat 1 p 0))
      (sourceModularBinaryFormAdjugateRep ℂ w (integralTriangularMatrix 1 p 0))) _)) = _
  rw [TensorProduct.map_tmul, degreeZeroGLRep_single_sub_single, periodMap_mk,
    rawPairing_single_sub_single_tmul, sourcePeriodDualRep_apply]
  change _ = sourcePeriodBetween f hk _ _
    (sourceModularBinaryFormAdjugateRep ℂ w (integralTriangularMatrix 1 p 0)
      (sourceModularBinaryFormRep ℂ w (op (q.out.val : Matrix (Fin 2) (Fin 2) ℤ)) P))
  rw [sourcePeriodBetween_apply, sourceModularBinaryFormSLRep_apply, inv_inv]
  simp only [sourceHeckeCuspRepresentative, mul_smul]

private local instance sourceHeckePeriodCosetsFintype :
    Fintype (Gamma0 Q ⧸ heckeUpperSubgroup Q p) :=
  sourceHeckeUpperFintype Q p

/-- The actual periods of the original analytic Hecke transform are the genuine coset trace. -/
theorem sourcePeriodBetween_hecke (hp : Nat.Prime p) (hpQ : Nat.Coprime p Q)
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : k = w + 2)
    (α β : OnePoint ℚ) :
    sourcePeriodBetween (cuspHeckePrime hp f) hk α β =
      ∑ q : Gamma0 Q ⧸ heckeUpperSubgroup Q p,
        (sourcePeriodDualRep (Gamma0 Q) w).ρ q.out
          (sourceHeckeDualDiagonal w p
            (sourcePeriodBetween f hk
              (sourceHeckeCuspRepresentative q • α) (sourceHeckeCuspRepresentative q • β))) := by
  apply LinearMap.ext
  intro P
  change periodMap ℂ (Gamma0 Q) hk (cuspHeckePrime hp f)
    (symbolQuotientMap ℂ w (Gamma0 Q)
      (⟨_, single_sub_single_mem_degreeZero α β⟩ ⊗ₜ P)) = _
  rw [sourcePeriodMap_heckeCosetTrace ℂ w Q hp hpQ, LinearMap.sum_apply]
  exact Finset.sum_congr rfl (fun q _ => sourceHeckeSymbolCoset_period hp f hk q α β P)

end
end Dubon2026
