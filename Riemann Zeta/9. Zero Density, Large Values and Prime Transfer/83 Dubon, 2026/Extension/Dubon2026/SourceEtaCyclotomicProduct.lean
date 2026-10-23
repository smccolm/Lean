import Dubon2026.SourceEtaProductTransport
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

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

theorem prod_one_sub_root_mul {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] {μ : K}
    (hμ : IsPrimitiveRoot μ p) (Y : PowerSeries K) :
    ∏ b ∈ Finset.range p, ((1 : PowerSeries K) - PowerSeries.C (μ ^ b) * Y) = 1 - Y ^ p := by
  classical
  have hp : p.Prime := Fact.out
  have hinj : Function.Injective (PowerSeries.C : K → PowerSeries K) := fun a b hab => by
    simpa using congrArg PowerSeries.constantCoeff hab
  have hμ' : IsPrimitiveRoot (PowerSeries.C μ) p := hμ.map_of_injective hinj
  have h := hμ'.pow_sub_pow_eq_prod_sub_mul 1 Y hp.pos
  rw [one_pow] at h
  rw [h]
  have hset : Polynomial.nthRootsFinset p (1 : PowerSeries K) =
      (Finset.range p).image fun b => PowerSeries.C μ ^ b := by
    ext x
    rw [Polynomial.mem_nthRootsFinset hp.pos, Finset.mem_image]
    constructor
    · intro hx
      obtain ⟨i, hi, rfl⟩ := hμ'.eq_pow_of_pow_eq_one hx
      exact ⟨i, Finset.mem_range.2 hi, rfl⟩
    · rintro ⟨i, -, rfl⟩
      rw [← pow_mul, mul_comm, pow_mul, hμ'.pow_eq_one, one_pow]
  rw [hset, Finset.prod_image fun i hi j hj hij =>
    hμ'.pow_inj (Finset.mem_range.1 hi) (Finset.mem_range.1 hj) hij]
  exact Finset.prod_congr rfl fun b _ => by rw [map_pow]

theorem prod_twist_factor {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (m : ℕ) :
    ∏ b ∈ Finset.range p,
        ((1 : PowerSeries K) - PowerSeries.C ((ζ ^ b) ^ m) * PowerSeries.X ^ m) =
      if p ∣ m then ((1 : PowerSeries K) - PowerSeries.X ^ m) ^ p
      else (1 : PowerSeries K) - PowerSeries.X ^ (p * m) := by
  have hp : p.Prime := Fact.out
  split_ifs with hd
  · obtain ⟨k, rfl⟩ := hd
    rw [Finset.prod_congr rfl fun b _ => show
        (1 : PowerSeries K) - PowerSeries.C ((ζ ^ b) ^ (p * k)) * PowerSeries.X ^ (p * k) =
          1 - PowerSeries.X ^ (p * k) by
      rw [← pow_mul, mul_left_comm b p k, pow_mul, hζ.pow_eq_one, one_pow, map_one, one_mul],
      Finset.prod_const, Finset.card_range]
  · have hμ : IsPrimitiveRoot (ζ ^ m) p :=
      hζ.pow_of_coprime m (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hd))
    rw [Finset.prod_congr rfl fun b _ => show
        (1 : PowerSeries K) - PowerSeries.C ((ζ ^ b) ^ m) * PowerSeries.X ^ m =
          1 - PowerSeries.C ((ζ ^ m) ^ b) * PowerSeries.X ^ m by rw [← pow_mul, mul_comm b m, pow_mul],
      prod_one_sub_root_mul hμ, ← pow_mul, mul_comm m p]


end
end Dubon2026.SourceFunctionField
