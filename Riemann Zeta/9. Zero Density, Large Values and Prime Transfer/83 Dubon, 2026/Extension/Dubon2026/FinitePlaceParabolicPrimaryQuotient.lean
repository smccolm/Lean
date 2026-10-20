import Dubon2026.FinitePlaceParabolicQuotient
import Dubon2026.FiniteCyclicPrimaryQuotient
import Mathlib.Data.Nat.ModEq
import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-! # The source auxiliary primary quotient at an original finite place

For DUB-17 through BLGG Sections 3.2 and 3.6, the auxiliary group is the
maximal coefficient-primary quotient of the literal last-row U0/U1.
The multiplication below is the original quotient multiplication. The
residue-field equivalence proves commutativity and cyclicity rather than
replacing that group by a chosen cyclic model.
-/

namespace Dubon2026

noncomputable section

open NumberField IsDedekindDomain
open scoped NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- The actual last-row quotient at the original number-field place. -/
abbrev FinitePlaceParabolicQuotient (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :=
  parabolicResidueLevelZero (Valued.integer (v.adicCompletion K)) (Fin.last n) ⧸
    (parabolicResidueLevelOneAmbient (Valued.integer (v.adicCompletion K)) (Fin.last n)).subgroupOf
      (parabolicResidueLevelZero (Valued.integer (v.adicCompletion K)) (Fin.last n))

/-- Arithmetic residue finiteness supplies finiteness of the original quotient. -/
instance finitePlaceParabolicQuotient_finiteInstance
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    Finite (FinitePlaceParabolicQuotient K v n) :=
  finitePlaceParabolicQuotient_finite K v n

/-- The original quotient multiplication is commutative. -/
instance finitePlaceParabolicQuotientCommGroup
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    CommGroup (FinitePlaceParabolicQuotient K v n) :=
  { (inferInstance : Group (FinitePlaceParabolicQuotient K v n)) with
    mul_comm := fun x y => (finitePlaceParabolicQuotientEquiv K v n).injective
      (((finitePlaceParabolicQuotientEquiv K v n).map_mul x y).trans
        ((mul_comm _ _).trans ((finitePlaceParabolicQuotientEquiv K v n).map_mul y x).symm)) }

/-- The actual quotient is cyclic because it is a finite field's unit group. -/
instance finitePlaceParabolicQuotient_isCyclic
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    IsCyclic (FinitePlaceParabolicQuotient K v n) := by
  letI : Finite (𝓞 K ⧸ v.asIdeal) :=
    Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  exact isCyclic_of_injective (finitePlaceParabolicQuotientEquiv K v n).toMonoidHom
    (finitePlaceParabolicQuotientEquiv K v n).injective

/-- Delta is the actual maximal primary quotient of the original last-row quotient. -/
abbrev FinitePlaceParabolicDelta (v : HeightOneSpectrum (𝓞 K)) (n q : ℕ) :=
  FiniteCommutativePrimaryQuotient (FinitePlaceParabolicQuotient K v n) q

/-- The original auxiliary quotient has the source residue-unit cardinality. -/
theorem finitePlaceParabolicQuotient_card (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    Nat.card (FinitePlaceParabolicQuotient K v n) = Nat.card (𝓞 K ⧸ v.asIdeal) - 1 := by
  let e := originalRingOfIntegersQuotientEquivAdicResidueField K v
  rw [Nat.card_congr (finitePlaceParabolicQuotientEquiv K v n).toEquiv,
    Nat.card_congr (Units.mapEquiv e.toMulEquiv).toEquiv,
    Nat.card_units, Nat.card_congr e.toEquiv]

/-- Delta has the entire coefficient-primary part of the actual residue-unit order. -/
theorem finitePlaceParabolicDelta_card (v : HeightOneSpectrum (𝓞 K)) (n q : ℕ)
    [Fact q.Prime] :
    Nat.card (FinitePlaceParabolicDelta K v n q) =
      q ^ (Nat.card (𝓞 K ⧸ v.asIdeal) - 1).factorization q := by
  rw [finiteCyclicPrimaryQuotient_card, finitePlaceParabolicQuotient_card]

/-- The original Delta is a coefficient-primary group. -/
theorem finitePlaceParabolicDelta_isPGroup (v : HeightOneSpectrum (𝓞 K)) (n q : ℕ)
    : IsPGroup q (FinitePlaceParabolicDelta K v n q) :=
  finiteCommutativePrimaryQuotient_isPGroup (FinitePlaceParabolicQuotient K v n) q

/-- The source congruence order at an auxiliary place survives in Delta. -/
theorem finitePlaceParabolicDelta_card_dvd (v : HeightOneSpectrum (𝓞 K)) (n q level : ℕ)
    [Fact q.Prime] (h : q ^ level ∣ Nat.card (𝓞 K ⧸ v.asIdeal) - 1) :
    q ^ level ∣ Nat.card (FinitePlaceParabolicDelta K v n q) := by
  apply finiteCyclicPrimaryQuotient_card_dvd
  rwa [finitePlaceParabolicQuotient_card]

/-- The printed norm congruence gives the required order in the actual local Delta. -/
theorem finitePlaceParabolicDelta_card_dvd_of_norm_modEq
    (v : HeightOneSpectrum (𝓞 K)) (n q level : ℕ) [Fact q.Prime]
    (h : v.asIdeal.absNorm ≡ 1 [MOD q ^ level]) :
    q ^ level ∣ Nat.card (FinitePlaceParabolicDelta K v n q) := by
  letI : Finite (𝓞 K ⧸ v.asIdeal) :=
    Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  apply finitePlaceParabolicDelta_card_dvd
  exact (Nat.modEq_iff_dvd' (Nat.card_pos : 0 < Nat.card (𝓞 K ⧸ v.asIdeal))).mp h.symm

/-- Every coefficient-primary action of the original U0/U1 factors uniquely through Delta. -/
theorem finitePlaceParabolicDelta_unique_factor (v : HeightOneSpectrum (𝓞 K)) (n q : ℕ)
    [Fact q.Prime] {H : Type*} [Group H] (hH : IsPGroup q H)
    (θ : FinitePlaceParabolicQuotient K v n →* H) :
    ∃! η : FinitePlaceParabolicDelta K v n q →* H,
      η.comp (QuotientGroup.mk'
        (finiteCommutativePrimaryKernel (FinitePlaceParabolicQuotient K v n) q)) = θ :=
  finiteCommutativePrimaryQuotient_unique_factor (FinitePlaceParabolicQuotient K v n) q hH θ

end
end Dubon2026
