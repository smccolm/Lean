import Dubon2026.SourceEtaNormLaurent
import Dubon2026.SourceDeltaNormBookkeeping
import Dubon2026.SourceLaurentTwistMonomials

/-! DUB-17/18 -> original Frobenius/inertia -> good reduction -> exact
residue-field degree -> prime j nonmembership -> discriminant norm identity.
These proofs establish the literal product of root-of-unity twists of the eta
series, regrouping divisible and nondivisible indices. Only the topology and
product identities required for this exact norm calculation are selected.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_StarBank_deltaNorm. The existing q-substitution/power-series
identity is reused; repeated first-coefficient proofs are omitted. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open scoped PowerSeries.WithPiTopology

theorem deltaNorm {K : Type*} [Field K] (p : ℕ) [Fact p.Prime] (ζ : Kˣ)
    (hζ : IsPrimitiveRoot (ζ : K) p) :
    (∏ b ∈ Finset.range p, qTwist (ζ ^ b)
        (HahnSeries.single (1 : ℤ) (1 : K) *
          HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24)) *
      qExpand K (p * p) (HahnSeries.single (1 : ℤ) (1 : K) *
          HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24) =
    HahnSeries.C (((∏ b ∈ Finset.range p, ζ ^ b : Kˣ) : K)) *
      qExpand K p (HahnSeries.single (1 : ℤ) (1 : K) *
          HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24) ^
        (p + 1) := by
  have hN := etaNorm p ζ hζ
  have hT : ∀ b ∈ Finset.range p,
      qTwist (ζ ^ b) (HahnSeries.single (1 : ℤ) (1 : K) *
          HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24) =
        HahnSeries.single (1 : ℤ) ((ζ ^ b : Kˣ) : K) *
          qTwist (ζ ^ b)
            (HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd)) ^ 24 :=
    fun b _ => by rw [map_mul, map_pow, qTwist_single, zpow_one, mul_one]
  rw [Finset.prod_congr rfl hT, Finset.prod_mul_distrib, Finset.prod_pow,
    prod_single_one, Finset.card_range, ← Units.coe_prod, map_mul, map_pow,
    qExpand_single, mul_one, map_mul, map_pow, qExpand_single, mul_one]
  exact delta_bookkeeping p _ _ _ _ hN


end
end Dubon2026.SourceFunctionField
