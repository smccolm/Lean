import Dubon2026.SourceEtaNormPowerSeries

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

theorem etaNorm {K : Type*} [Field K] (p : ℕ) [Fact p.Prime] (ζ : Kˣ)
    (hζ : IsPrimitiveRoot (ζ : K) p) :
    (∏ b ∈ Finset.range p,
        qTwist (ζ ^ b) (HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd))) *
      qExpand K (p * p) (HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd)) =
    qExpand K p (HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd)) ^
      (p + 1) := by
  rw [qExpand_ofPowerSeries_eq_expand, qExpand_ofPowerSeries_eq_expand,
    Finset.prod_congr rfl fun b _ => qTwist_ofPowerSeries (ζ ^ b) _,
    ← map_prod, ← map_mul, ← map_pow]
  simp only [Units.val_pow_eq_pow_val]
  exact congrArg _ (etaNorm_powerSeries hζ)


end
end Dubon2026.SourceFunctionField
