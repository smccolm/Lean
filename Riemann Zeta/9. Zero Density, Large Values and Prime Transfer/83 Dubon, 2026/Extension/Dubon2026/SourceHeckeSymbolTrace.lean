import Dubon2026.SourceHeckeSymbolCosets
import Dubon2026.SourceHeckePrimeAdjoint

/-! Exact agreement of the original coset sum and prime symbol operator.
DUB-17/18 -> residual modular Galois association -> original H1 Hecke
compatibility. The proved Gamma0 transversal and triangular factorizations
identify the actual finite correspondence with the already proved integral
Hecke action, hence with the analytic operator under the original period map.
-/

namespace Dubon2026.SourceModularSymbols
noncomputable section
open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open MvPolynomial TensorProduct
open scoped MatrixGroups

variable (R : Type) [CommRing R] (w Q : ℕ) {p : ℕ} [NeZero p]

/-- The original upper transversal gives the literal upper triangular symbol maps. -/
theorem sourceHeckeSymbolCoset_some (hp : Nat.Prime p) (hpQ : Nat.Coprime p Q)
    (x : ZMod p) :
    sourceHeckeSymbolCoset R w Q hp (heckeUpperCoset p Q hpQ (some x)) =
      triangularSymbolMap R w (Gamma0 Q) 1 p x.val := by
  change sourceHeckeSymbolCoset R w Q hp
    (QuotientGroup.mk (heckeUpperRepresentative p Q hpQ (some x))⁻¹) = _
  rw [sourceHeckeSymbolCoset_mk]
  simp only [Subgroup.coe_inv, inv_inv]
  apply triangularSymbolMap_factor
  refine ⟨1, one_mem _, ?_⟩
  simpa only [map_one, one_mul] using heckeUpperMatrix_some hpQ x

/-- The complementary original coset gives the actual diagonal symbol map. -/
theorem sourceHeckeSymbolCoset_none (hp : Nat.Prime p) (hpQ : Nat.Coprime p Q) :
    sourceHeckeSymbolCoset R w Q hp (heckeUpperCoset p Q hpQ none) =
      triangularSymbolMap R w (Gamma0 Q) p 1 0 := by
  change sourceHeckeSymbolCoset R w Q hp
    (QuotientGroup.mk (heckeUpperRepresentative p Q hpQ none)⁻¹) = _
  rw [sourceHeckeSymbolCoset_mk]
  simp only [Subgroup.coe_inv, inv_inv]
  exact triangularSymbolMap_factor (Gamma0 Q) 0 0 _ (heckeUpperMatrix_none hpQ)

variable (hp : Nat.Prime p) (hpQ : Nat.Coprime p Q)

private local instance sourceHeckeSymbolTraceFintype :
    Fintype (Gamma0 Q ⧸ heckeUpperSubgroup Q p) :=
  sourceHeckeUpperFintype Q p

include hpQ

/-- The full genuine coset sum is exactly the original prime symbol action before descent. -/
theorem sourceHeckeSymbolCoset_sum :
    (∑ q : Gamma0 Q ⧸ heckeUpperSubgroup Q p, sourceHeckeSymbolCoset R w Q hp q) =
      primeSymbolPreMap R w Q p := by
  rw [← (heckeUpperCosetEquiv hp hpQ).sum_comp, Fintype.sum_option]
  change sourceHeckeSymbolCoset R w Q hp (heckeUpperCoset p Q hpQ none) +
    (∑ x : ZMod p, sourceHeckeSymbolCoset R w Q hp (heckeUpperCoset p Q hpQ (some x))) = _
  simp_rw [sourceHeckeSymbolCoset_none R w Q hp hpQ,
    sourceHeckeSymbolCoset_some R w Q hp hpQ]
  rw [primeSymbolPreMap, if_pos hpQ, add_comm]
  congr 1
  rw [← (ZMod.finEquiv p).toEquiv.sum_comp]
  apply Finset.sum_congr rfl
  intro x _
  have hx : ((ZMod.finEquiv p) x).val = x.val := by
    cases p with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ n => rfl
  change triangularSymbolMap R w (Gamma0 Q) 1 p ((ZMod.finEquiv p) x).val = _
  rw [hx]

/-- The actual original period map identifies this coset trace with the analytic prime action. -/
theorem sourcePeriodMap_heckeCosetTrace [Algebra R ℂ] [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : k = w + 2)
    (x : degreeZero R ⊗[R] homogeneousSubmodule (Fin 2) R w) :
    periodMap R (Gamma0 Q) hk (cuspHeckePrime hp f) (symbolQuotientMap R w (Gamma0 Q) x) =
      ∑ q : Gamma0 Q ⧸ heckeUpperSubgroup Q p,
        periodMap R (Gamma0 Q) hk f (sourceHeckeSymbolCoset R w Q hp q x) := by
  rw [periodMap_integralHeckePrime]
  change periodMap R (Gamma0 Q) hk f
    (integralHeckePrime R w Q hp (Representation.Coinvariants.mk _ x)) = _
  rw [integralHeckePrime_mk, ← sourceHeckeSymbolCoset_sum R w Q hp hpQ,
    LinearMap.sum_apply, map_sum]

end
end Dubon2026.SourceModularSymbols
