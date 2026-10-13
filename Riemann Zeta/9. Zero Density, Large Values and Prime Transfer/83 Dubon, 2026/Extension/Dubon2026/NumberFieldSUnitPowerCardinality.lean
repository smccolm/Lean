import Dubon2026.NumberFieldSUnitRank
import Dubon2026.SUnitPowerTorsion
import Dubon2026.FiniteGeneratedAbelianPowerIndex

/-! # Cardinality of the actual number-field S-unit power quotient

The original S-unit rank and the actual roots-of-unity kernel discharge
both factors in the pinned group-theoretic index calculation. This is the
power-index input for global Kummer preparation and the cyclic idele-class
norm index, then global reciprocity and the DUB-17 Selmer/automorphy chain.
-/

namespace Dubon2026
noncomputable section
open IsDedekindDomain
open scoped NumberField

/-- The original S-unit quotient by nth powers has precisely the source cardinality,
including its actual roots-of-unity factor and every infinite place. -/
theorem numberField_sUnit_powerQuotient_card
    (K : Type*) [Field K] [NumberField K]
    (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite)
    (n : ℕ) (hn : n ≠ 0) (ζ : K) (hζ : IsPrimitiveRoot ζ n) :
    Nat.card (S.unit K ⧸ (powMonoidHom (α := S.unit K) n).range) =
      n ^ (Fintype.card (NumberField.InfinitePlace K) + S.ncard) := by
  letI := numberField_sUnit_fg K S hS
  have h := finiteGeneratedAbelian_nsmul_index (Additive (S.unit K)) n hn
  change Nat.card (S.unit K ⧸ (powMonoidHom (α := S.unit K) n).range) =
    n ^ Module.finrank ℤ (Additive (S.unit K)) *
      Nat.card (powMonoidHom (α := S.unit K) n).ker at h
  rw [sUnitPowerKernel_card S n hn ζ hζ, numberField_sUnit_finrank K S hS,
    ← pow_succ] at h
  have hp : 0 < Fintype.card (NumberField.InfinitePlace K) := Fintype.card_pos
  have hr : NumberField.Units.rank K + S.ncard + 1 =
      Fintype.card (NumberField.InfinitePlace K) + S.ncard := by
    unfold NumberField.Units.rank
    omega
  exact h.trans (congrArg (n ^ ·) hr)

end
end Dubon2026
