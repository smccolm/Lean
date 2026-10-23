import Dubon2026.SourceEtaCyclotomicProduct
import Dubon2026.SourceEtaProductRegrouping

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

theorem etaNorm_powerSeries {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) :
    (∏ b ∈ Finset.range p,
        PowerSeries.rescale (ζ ^ b) (PowerSeries.map (Int.castRingHom K) etaProd)) *
      PowerSeries.expand (p * p) (mul_ne_zero (NeZero.ne p) (NeZero.ne p))
        (PowerSeries.map (Int.castRingHom K) etaProd) =
    PowerSeries.expand p (NeZero.ne p) (PowerSeries.map (Int.castRingHom K) etaProd) ^ (p + 1) := by
  letI : TopologicalSpace K := ⊥
  haveI : DiscreteTopology K := ⟨rfl⟩
  have hp : p.Prime := Fact.out
  have hmult : ∀ b ∈ Finset.range p, Multipliable fun n : ℕ =>
      (1 : PowerSeries K) - PowerSeries.C ((ζ ^ b) ^ (n + 1)) * PowerSeries.X ^ (n + 1) :=
    fun b _ => multipliable_of_X_pow_dvd _ fun n => ⟨-PowerSeries.C ((ζ ^ b) ^ (n + 1)), by ring⟩
  rw [map_etaProd_eq_tprod K, expand_tprod_one_sub_X_pow, expand_tprod_one_sub_X_pow,
    Finset.prod_congr rfl fun b _ => rescale_tprod_one_sub_X_pow (ζ ^ b),
    ← Multipliable.tprod_finsetProd hmult, tprod_congr fun n => prod_twist_factor hζ (n + 1)]
  exact regroup K hp.pos


end
end Dubon2026.SourceFunctionField
