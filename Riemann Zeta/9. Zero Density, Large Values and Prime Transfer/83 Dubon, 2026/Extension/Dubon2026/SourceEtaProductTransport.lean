import Dubon2026.SourceIntegralPowerSeriesFrobenius
import Dubon2026.SourceLaurentRootTwist

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

theorem qTwist_ofPowerSeries {R : Type*} [CommRing R] (u : Rˣ) (f : PowerSeries R) :
    qTwist u (HahnSeries.ofPowerSeries ℤ R f) =
      HahnSeries.ofPowerSeries ℤ R (PowerSeries.rescale (u : R) f) := by
  ext k
  rw [qTwist_coeff]
  rcases le_or_gt 0 k with hk | hk
  · lift k to ℕ using hk
    rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff,
      PowerSeries.coeff_rescale, zpow_natCast, Units.val_pow_eq_pow_val]
  · rw [ofPowerSeries_coeff_of_neg _ hk, ofPowerSeries_coeff_of_neg _ hk, mul_zero]

theorem continuous_of_coeff {R S : Type*} [Semiring R] [Semiring S] [TopologicalSpace R]
    [TopologicalSpace S] (g : PowerSeries R → PowerSeries S)
    (h : ∀ d, Continuous fun φ => PowerSeries.coeff d (g φ)) : Continuous g :=
  continuous_iff_continuousAt.2 fun φ =>
    (PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto S g (nhds φ) (g φ)).2 fun d =>
      (h d).continuousAt

theorem continuous_map {R S : Type*} [Semiring R] [Semiring S] [TopologicalSpace R]
    [TopologicalSpace S] (f : R →+* S) (hf : Continuous f) :
    Continuous (PowerSeries.map f : PowerSeries R → PowerSeries S) :=
  continuous_of_coeff _ fun d => by
    simp only [PowerSeries.coeff_map]
    exact hf.comp (PowerSeries.WithPiTopology.continuous_coeff R d)

theorem continuous_rescale {R : Type*} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
    (a : R) : Continuous (PowerSeries.rescale a : PowerSeries R → PowerSeries R) :=
  continuous_of_coeff _ fun d => by
    simp only [PowerSeries.coeff_rescale]
    exact (continuous_of_discreteTopology (f := fun x : R => a ^ d * x)).comp
      (PowerSeries.WithPiTopology.continuous_coeff R d)

theorem continuous_expand {R : Type*} [CommRing R] [TopologicalSpace R] (N : ℕ) (hN : N ≠ 0) :
    Continuous (PowerSeries.expand N hN : PowerSeries R → PowerSeries R) :=
  continuous_of_coeff _ fun d => by
    simp only [PowerSeries.coeff_expand]
    split_ifs
    · exact PowerSeries.WithPiTopology.continuous_coeff R _
    · exact continuous_const

theorem multipliable_of_X_pow_dvd {R : Type*} [CommRing R] [TopologicalSpace R]
    (u : ℕ → PowerSeries R) (h : ∀ n, (PowerSeries.X : PowerSeries R) ^ (n + 1) ∣ u n - 1) :
    Multipliable u := by
  have hu : u = fun n => 1 + (u n - 1) := funext fun n => by ring
  rw [hu]
  apply PowerSeries.WithPiTopology.multipliable_one_add_of_tendsto_order_atTop_nhds_top
  refine ENat.tendsto_nhds_top_iff_natCast_lt.mpr fun n => Filter.eventually_atTop.mpr ⟨n, ?_⟩
  intro m hm
  have hle : ((m + 1 : ℕ) : ℕ∞) ≤ (u m - 1).order :=
    PowerSeries.nat_le_order _ _ fun i hi => PowerSeries.X_pow_dvd_iff.1 (h m) i hi
  exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_of_le hm) hle

theorem map_etaProd_eq_tprod (K : Type*) [CommRing K] [TopologicalSpace K] [T2Space K] :
    PowerSeries.map (Int.castRingHom K) etaProd =
      ∏' n : ℕ, ((1 : PowerSeries K) - PowerSeries.X ^ (n + 1)) := by
  rw [etaProd, (PowerSeries.WithPiTopology.multipliable_one_sub_X_pow ℤ).map_tprod
    (PowerSeries.map (Int.castRingHom K)) (continuous_map _ continuous_of_discreteTopology)]
  exact tprod_congr fun n => by rw [map_sub, map_one, map_pow, PowerSeries.map_X]

theorem rescale_tprod_one_sub_X_pow {K : Type*} [CommRing K] [TopologicalSpace K]
    [DiscreteTopology K] (a : K) :
    PowerSeries.rescale a (∏' n : ℕ, ((1 : PowerSeries K) - PowerSeries.X ^ (n + 1))) =
      ∏' n : ℕ, ((1 : PowerSeries K) - PowerSeries.C (a ^ (n + 1)) * PowerSeries.X ^ (n + 1)) := by
  rw [(PowerSeries.WithPiTopology.multipliable_one_sub_X_pow K).map_tprod (PowerSeries.rescale a)
    (continuous_rescale a)]
  exact tprod_congr fun n => by
    rw [map_sub, map_one, map_pow, PowerSeries.rescale_X, mul_pow, ← map_pow]

theorem expand_tprod_one_sub_X_pow {K : Type*} [CommRing K] [TopologicalSpace K] [T2Space K]
    (N : ℕ) (hN : N ≠ 0) :
    PowerSeries.expand N hN (∏' n : ℕ, ((1 : PowerSeries K) - PowerSeries.X ^ (n + 1))) =
      ∏' n : ℕ, ((1 : PowerSeries K) - PowerSeries.X ^ (N * (n + 1))) := by
  rw [(PowerSeries.WithPiTopology.multipliable_one_sub_X_pow K).map_tprod (PowerSeries.expand N hN)
    (continuous_expand N hN)]
  exact tprod_congr fun n => by rw [map_sub, map_one, map_pow, PowerSeries.expand_X, ← pow_mul]


end
end Dubon2026.SourceFunctionField
