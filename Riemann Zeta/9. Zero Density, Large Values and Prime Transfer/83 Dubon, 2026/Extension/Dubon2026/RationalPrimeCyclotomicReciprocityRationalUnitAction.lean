import Dubon2026.RationalPrimeCyclotomicReciprocityQuotientAction
import Dubon2026.NormedFieldPowerSmallBall
import Dubon2026.RationalPrimeNormalizedValuation

/-! # Arbitrary rational-unit action on the actual cyclotomic closure stage

This module closes the sign and prime-power gap left after the positive
natural-quotient reciprocity calculation. Positive rationals are dense in the
actual rational-prime completion: after an arbitrary rational approximation,
adding a sufficiently large positive multiple of a sufficiently small prime
power preserves local closeness. A positive rational of local norm one is
then its literal reduced positive-natural quotient, with numerator and
denominator both prime to the local prime.

The proved small-ball power bijection makes the residual quotient a degree-th
power. Its scalar embedding has that quotient as its field norm. Transporting
the norm witness across the actual cyclotomic-stage equivalence kills the
residual reciprocity value. The normalized prime-power part is killed by the
existing exact norm of the cyclotomic root minus one. No claim that `-1` acts
trivially is used.
-/

namespace Dubon2026
noncomputable section

set_option maxHeartbeats 1200000

open IsDedekindDomain HeightOneSpectrum Metric
open scoped ValuativeRel

attribute [local instance] rationalPrimeWittPrime wittCyclotomicRootDomain
  wittCyclotomicRootFaithful wittCyclotomicFieldAlgebra wittCyclotomicFieldTower
  rationalPrimeWittOriginalAlgebra rationalPrimeWittCyclotomicAlgebra
  rationalPrimeWittCyclotomicTower rationalPrimeWittCyclotomicModule
  rationalPrimeWittCyclotomicMulAction

/-- Positive rational numbers remain dense in a rational prime completion.
The proof first uses ordinary completion density and then adds a sufficiently
large positive multiple of a sufficiently small power of the prime. -/
theorem rationalPrime_exists_positive_rational_norm_sub_lt
    (p : ℕ) (hp : p.Prime) (x : rationalPrimeLocalField p hp)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ q : ℚ, 0 < q ∧
      ‖algebraMap ℚ (rationalPrimeLocalField p hp) q - x‖ < ε := by
  let K := rationalPrimeLocalField p hp
  haveI : IsUltrametricDist K := inferInstance
  obtain ⟨q₀, hq₀⟩ :=
    ((rationalPrimePlace p hp).denseRange_algebraMap ℚ).exists_dist_lt x hε
  have hpnorm : ‖(p : K)‖ < 1 := by
    have hmem : (p : ℤ) ∈ (rationalPrimePlace p hp).asIdeal :=
      (rationalPrimePlace_nat_mem_iff p hp p).mpr (dvd_refl p)
    have h := (NumberField.FinitePlace.norm_lt_one_iff_mem
      (K := ℚ) (v := rationalPrimePlace p hp) (p : ℤ)).mpr hmem
    simpa only [map_intCast, map_natCast] using h
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε hpnorm
  have hpqpos : 0 < (p : ℚ) ^ N := pow_pos (by exact_mod_cast hp.pos) N
  obtain ⟨m, hm⟩ := exists_nat_gt (-q₀ / ((p : ℚ) ^ N))
  let q : ℚ := q₀ + (p : ℚ) ^ N * m
  have hqpos : 0 < q := by
    have hm' : -q₀ < (m : ℚ) * (p : ℚ) ^ N :=
      (div_lt_iff₀ hpqpos).mp hm
    dsimp only [q]
    rw [mul_comm ((p : ℚ) ^ N)]
    linarith
  refine ⟨q, hqpos, ?_⟩
  have hmnorm : ‖(m : K)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one K m
  have hshift : ‖algebraMap ℚ K (((p : ℚ) ^ N) * m)‖ < ε := by
    calc
      ‖algebraMap ℚ K (((p : ℚ) ^ N) * m)‖ = ‖(p : K)‖ ^ N * ‖(m : K)‖ := by
        rw [map_mul, map_pow, map_natCast, map_natCast, norm_mul, norm_pow]
      _ ≤ ‖(p : K)‖ ^ N := mul_le_of_le_one_right (pow_nonneg (norm_nonneg _) _) hmnorm
      _ < ε := hN
  change ‖algebraMap ℚ K q - x‖ < ε
  rw [show algebraMap ℚ K q = algebraMap ℚ K q₀ +
      algebraMap ℚ K (((p : ℚ) ^ N) * m) by simp only [q, map_add]]
  have hadd := IsUltrametricDist.norm_add_le_max
    (algebraMap ℚ K q₀ - x) (algebraMap ℚ K (((p : ℚ) ^ N) * m))
  have heq : algebraMap ℚ K q₀ + algebraMap ℚ K (((p : ℚ) ^ N) * m) - x =
      (algebraMap ℚ K q₀ - x) + algebraMap ℚ K (((p : ℚ) ^ N) * m) := by ring
  rw [heq]
  refine hadd.trans_lt (max_lt ?_ ?_)
  · simpa only [dist_eq_norm, norm_sub_rev] using hq₀
  · exact hshift

/-- A positive rational of local norm one is literally a quotient of positive
naturals whose numerator and denominator are both prime to the local prime. -/
theorem positiveRational_eq_coprimeNaturalQuotient
    (p : ℕ) (hp : p.Prime) (q : ℚ) (hq : 0 < q)
    (hnorm : ‖algebraMap ℚ (rationalPrimeLocalField p hp) q‖ = 1) :
    let a := q.num.natAbs
    let c := q.den
    0 < a ∧ 0 < c ∧ ¬p ∣ a ∧ ¬p ∣ c ∧ (a : ℚ) / c = q := by
  let K := rationalPrimeLocalField p hp
  let a := q.num.natAbs
  let c := q.den
  have hnumpos : 0 < q.num := Rat.num_pos.mpr hq
  have ha : 0 < a := Int.natAbs_pos.mpr hnumpos.ne'
  have hc : 0 < c := q.den_pos
  have hnum : (a : ℤ) = q.num := Int.natAbs_of_nonneg hnumpos.le
  have hcop : a.Coprime c := by
    exact q.reduced
  have hnotboth : ¬(p ∣ a ∧ p ∣ c) := by
    rintro ⟨hpa, hpc⟩
    have hpone : p ∣ 1 := by
      rw [← hcop.gcd_eq_one]
      exact Nat.dvd_gcd hpa hpc
    exact hp.not_dvd_one hpone
  have hnormquot :
      ‖algebraMap ℚ K (q.num : ℚ)‖ / ‖algebraMap ℚ K (c : ℚ)‖ = 1 := by
    calc
      ‖algebraMap ℚ K (q.num : ℚ)‖ / ‖algebraMap ℚ K (c : ℚ)‖ =
          ‖algebraMap ℚ K ((q.num : ℚ) / (c : ℚ))‖ := by
            rw [← norm_div]
            exact congrArg norm (map_div₀ (algebraMap ℚ K) (q.num : ℚ) (c : ℚ)).symm
      _ = ‖algebraMap ℚ K q‖ := by
        dsimp only [c]
        rw [q.num_div_den]
      _ = 1 := hnorm
  have hden0 : ‖algebraMap ℚ K (c : ℚ)‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    exact (algebraMap ℚ K).injective.ne (Nat.cast_ne_zero.mpr hc.ne')
  have hnormeq : ‖algebraMap ℚ K (q.num : ℚ)‖ = ‖algebraMap ℚ K (c : ℚ)‖ :=
    (div_eq_one_iff_eq hden0).mp hnormquot
  have hpa : ¬p ∣ a := by
    intro hpa
    have hpc : ¬p ∣ c := fun hpc => hnotboth ⟨hpa, hpc⟩
    have hnumMem : (q.num : ℤ) ∈ (rationalPrimePlace p hp).asIdeal := by
      rw [← hnum]
      exact (rationalPrimePlace_nat_mem_iff p hp a).mpr hpa
    have hdenNotMem : (c : ℤ) ∉ (rationalPrimePlace p hp).asIdeal := by
      simpa only [Int.natCast_dvd_natCast] using
        (not_congr (rationalPrimePlace_nat_mem_iff p hp c)).mpr hpc
    have hnumlt := (NumberField.FinitePlace.norm_lt_one_iff_mem
      (K := ℚ) (v := rationalPrimePlace p hp) q.num).mpr hnumMem
    have hdeneq := (NumberField.FinitePlace.norm_eq_one_iff_notMem
      (K := ℚ) (v := rationalPrimePlace p hp) (c : ℤ)).mpr hdenNotMem
    have hnumlt' : ‖algebraMap ℚ K (q.num : ℚ)‖ < 1 := by
      simpa only [NumberField.FinitePlace.embedding_apply,
        IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion,
        Function.comp_apply, Algebra.algebraMap_self_apply] using hnumlt
    have hdeneq' : ‖algebraMap ℚ K (c : ℚ)‖ = 1 := by
      simpa only [map_intCast, map_natCast] using hdeneq
    rw [hnormeq, hdeneq'] at hnumlt'
    exact (lt_irrefl 1) hnumlt'
  have hpc : ¬p ∣ c := by
    intro hpc
    have hpa' : ¬p ∣ a := fun hpa' => hnotboth ⟨hpa', hpc⟩
    have hnumNotMem : (q.num : ℤ) ∉ (rationalPrimePlace p hp).asIdeal := by
      rw [← hnum]
      simpa only [Int.natCast_dvd_natCast] using
        (not_congr (rationalPrimePlace_nat_mem_iff p hp a)).mpr hpa'
    have hdenMem : (c : ℤ) ∈ (rationalPrimePlace p hp).asIdeal :=
      (rationalPrimePlace_nat_mem_iff p hp c).mpr hpc
    have hnumeq := (NumberField.FinitePlace.norm_eq_one_iff_notMem
      (K := ℚ) (v := rationalPrimePlace p hp) q.num).mpr hnumNotMem
    have hdenlt := (NumberField.FinitePlace.norm_lt_one_iff_mem
      (K := ℚ) (v := rationalPrimePlace p hp) (c : ℤ)).mpr hdenMem
    have hnumeq' : ‖algebraMap ℚ K (q.num : ℚ)‖ = 1 := by
      simpa only [NumberField.FinitePlace.embedding_apply,
        IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion,
        Function.comp_apply, Algebra.algebraMap_self_apply] using hnumeq
    have hdenlt' : ‖algebraMap ℚ K (c : ℚ)‖ < 1 := by
      simpa only [map_intCast, map_natCast] using hdenlt
    rw [← hnormeq, hnumeq'] at hdenlt'
    exact (lt_irrefl 1) hdenlt'
  refine ⟨ha, hc, hpa, hpc, ?_⟩
  calc
    (a : ℚ) / c = (q.num : ℚ) / q.den := by
      congr 1
      exact_mod_cast hnum
    _ = q := q.num_div_den

/-- Elements sufficiently close to one are explicit norms from any positive
finite-dimensional extension: first take a degree-th root in the base field,
then norm its scalar embedding. -/
theorem finiteDimensional_exists_norm_near_one
    (K L : Type) [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (hd : (Module.finrank K L : K) ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ u : Kˣ,
      ‖(u : K) - 1‖ ≤ ‖(Module.finrank K L : K)‖ * r →
        ∃ v : Lˣ, Units.map (Algebra.norm K (S := L)) v = u := by
  obtain ⟨r, hr0, hr1, hballs⟩ :=
    normedField_power_small_closedBall K (Module.finrank K L) hd
  refine ⟨r, hr0, hr1, ?_⟩
  intro u hu
  have hutarget : (u : K) ∈ closedBall (1 : K) (‖(Module.finrank K L : K)‖ * r) := by
    simpa only [mem_closedBall, dist_eq_norm] using hu
  obtain ⟨x, hx, hxu⟩ := (hballs r hr0 (le_refl r)).surjOn hutarget
  have hxnorm : ‖x - 1‖ ≤ r := by
    simpa only [mem_closedBall, dist_eq_norm] using hx
  have hx0 : x ≠ 0 := by
    intro hxzero
    have : (1 : ℝ) ≤ r := by simpa only [hxzero, zero_sub, norm_neg, norm_one] using hxnorm
    exact (not_le_of_gt hr1) this
  let v : Lˣ := Units.map (algebraMap K L).toMonoidHom (Units.mk0 x hx0)
  refine ⟨v, ?_⟩
  apply Units.ext
  change Algebra.norm K (algebraMap K L x) = (u : K)
  rw [Algebra.norm_algebraMap]
  exact hxu

/-- Every norm-one local unit differs from a positive rational quotient away
from `p` by an actual norm from a prescribed finite extension. -/
theorem rationalPrime_exists_positive_quotient_norm_comparison
    (p : ℕ) (hp : p.Prime)
    (L : Type) [Field L] [Algebra (rationalPrimeLocalField p hp) L]
    [FiniteDimensional (rationalPrimeLocalField p hp) L]
    (u : (rationalPrimeLocalField p hp)ˣ)
    (hu : ‖(u : rationalPrimeLocalField p hp)‖ = 1) :
    ∃ (a c : ℕ) (ha : ¬p ∣ a) (hc : ¬p ∣ c),
      ∃ v : Lˣ, Units.map
        (Algebra.norm (rationalPrimeLocalField p hp) (S := L)) v =
          u / rationalPrimeNaturalQuotientUnit p hp a c ha hc := by
  let K := rationalPrimeLocalField p hp
  have hpNormLt : ‖(p : K)‖ < 1 := by
    have hmem : (p : ℤ) ∈ (rationalPrimePlace p hp).asIdeal :=
      (rationalPrimePlace_nat_mem_iff p hp p).mpr (dvd_refl p)
    have h := (NumberField.FinitePlace.norm_lt_one_iff_mem
      (K := ℚ) (v := rationalPrimePlace p hp) (p : ℤ)).mpr hmem
    simpa only [map_intCast, map_natCast] using h
  letI : NontriviallyNormedField K := NontriviallyNormedField.ofNormNeOne (by
    refine ⟨(p : K), ?_, hpNormLt.ne⟩
    have h := (algebraMap ℚ K).injective.ne
      (Nat.cast_ne_zero.mpr hp.ne_zero : (p : ℚ) ≠ 0)
    simpa only [map_natCast, map_zero] using h)
  haveI : IsUltrametricDist K := inferInstance
  have hd0 : (Module.finrank K L : K) ≠ 0 := by
    have h := (algebraMap ℚ K).injective.ne
      (Nat.cast_ne_zero.mpr (Module.finrank_pos.ne' : Module.finrank K L ≠ 0) :
        (Module.finrank K L : ℚ) ≠ 0)
    simpa only [map_natCast, map_zero] using h
  obtain ⟨r, hr0, hr1, hnormball⟩ :=
    finiteDimensional_exists_norm_near_one K L hd0
  have hdnorm : 0 < ‖(Module.finrank K L : K)‖ := norm_pos_iff.mpr
    hd0
  let ε : ℝ := ‖(Module.finrank K L : K)‖ * r
  have hε : 0 < ε := mul_pos hdnorm hr0
  have hεone : ε < 1 := by
    have hdle : ‖(Module.finrank K L : K)‖ ≤ 1 :=
      IsUltrametricDist.norm_natCast_le_one K (Module.finrank K L)
    exact (mul_le_of_le_one_left hr0.le hdle).trans_lt hr1
  obtain ⟨q, hqpos, hqclose⟩ :=
    rationalPrime_exists_positive_rational_norm_sub_lt p hp (u : K) ε hε
  have hq0 : q ≠ 0 := hqpos.ne'
  let qU : Kˣ := Units.map (algebraMap ℚ K).toMonoidHom (Units.mk0 q hq0)
  have hqclose' : ‖(qU : K) - (u : K)‖ < ε := by exact hqclose
  have hqcloseOne : ‖(qU : K) - (u : K)‖ < 1 := hqclose'.trans hεone
  have hqnorm : ‖(qU : K)‖ = 1 := by
    have hqle : ‖(qU : K)‖ ≤ 1 := by
      calc
        ‖(qU : K)‖ = ‖((qU : K) - (u : K)) + (u : K)‖ := by
          rw [sub_add_cancel]
        _ ≤ max ‖(qU : K) - (u : K)‖ ‖(u : K)‖ :=
          IsUltrametricDist.norm_add_le_max _ _
        _ ≤ 1 := max_le hqcloseOne.le (by rw [hu])
    have honele : 1 ≤ ‖(qU : K)‖ := by
      by_contra hnot
      have hqlt : ‖(qU : K)‖ < 1 := lt_of_not_ge hnot
      have hult : ‖(u : K)‖ < 1 := by
        calc
          ‖(u : K)‖ = ‖((u : K) - (qU : K)) + (qU : K)‖ := by
            rw [sub_add_cancel]
          _ ≤ max ‖(u : K) - (qU : K)‖ ‖(qU : K)‖ :=
            IsUltrametricDist.norm_add_le_max _ _
          _ < 1 := max_lt (by simpa only [norm_sub_rev] using hqcloseOne) hqlt
      rw [hu] at hult
      exact (lt_irrefl 1) hult
    exact le_antisymm hqle honele
  obtain ⟨ha0, hc0, ha, hc, hqeq⟩ :=
    positiveRational_eq_coprimeNaturalQuotient p hp q hqpos (by
      simpa only [qU, Units.coe_map, Units.val_mk0] using hqnorm)
  let a := q.num.natAbs
  let c := q.den
  let qN := rationalPrimeNaturalQuotientUnit p hp a c ha hc
  have hqUN : qU = qN := by
    apply Units.ext
    change algebraMap ℚ K q = (a : K) / c
    simpa only [map_div₀, map_natCast] using
      (congrArg (algebraMap ℚ K) hqeq).symm
  have hratio : ‖((u / qU : Kˣ) : K) - 1‖ ≤ ε := by
    have hval : ((u / qU : Kˣ) : K) - 1 = ((u : K) - (qU : K)) / (qU : K) := by
      simpa only [Units.val_div_eq_div_val] using
        (div_sub_one (a := (u : K)) (b := (qU : K)) qU.ne_zero)
    rw [hval, norm_div, hqnorm, div_one]
    exact le_of_lt (by simpa only [norm_sub_rev] using hqclose')
  obtain ⟨v, hv⟩ := hnormball (u / qU) hratio
  refine ⟨a, c, ha, hc, v, ?_⟩
  simpa only [hqUN] using hv

/-- Zero normalized local order is norm one for the canonical norm on the
actual rational-prime completion. -/
theorem rationalPrime_norm_eq_one_of_order_zero
    (p : ℕ) (hp : p.Prime) (u : (rationalPrimeLocalField p hp)ˣ)
    (hu : localFieldUnitOrder (rationalPrimeLocalField p hp)
      (Additive.ofMul u) = 0) :
    ‖(u : rationalPrimeLocalField p hp)‖ = 1 := by
  have hvrel := (localFieldUnitOrder_eq_zero_iff
    (rationalPrimeLocalField p hp) u).mp hu
  have hv : Valued.v (R := rationalPrimeLocalField p hp) u.val = 1 :=
    (ValuativeRel.isEquiv
      (ValuativeRel.valuation (rationalPrimeLocalField p hp))
      (Valued.v (R := rationalPrimeLocalField p hp))).eq_one_iff_eq_one.mp hvrel
  rw [NumberField.FinitePlace.norm_def, hv]
  norm_num

/-- Algebra equivalence transports a unit norm witness without changing its
base-field norm. -/
theorem algEquiv_unit_norm_transport
    {K L M : Type*} [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M] [FiniteDimensional K L]
    [FiniteDimensional K M] (e : L ≃ₐ[K] M) (v : Lˣ) :
    Units.map (Algebra.norm K (S := M))
        (Units.map e.toMonoidHom v) =
      Units.map (Algebra.norm K (S := L)) v := by
  apply Units.ext
  exact Algebra.norm_eq_of_algEquiv e v.val

/-- The literal image of a rational unit in the actual rational-prime local
field. -/
def rationalPrimeRationalUnit
    (p : ℕ) (hp : p.Prime) (q : ℚˣ) :
    (rationalPrimeLocalField p hp)ˣ :=
  Units.map (algebraMap ℚ (rationalPrimeLocalField p hp)).toMonoidHom q

/-- Arbitrary rational units have the same cyclotomic reciprocity action as
a constructed positive rational quotient away from `p`. The prime-power
part is killed by the already proved prime norm, while the residual quotient
is killed by the small-ball power/norm argument. -/
theorem rationalPrimeRationalUnit_exists_reciprocity_root_action
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (n : ℕ) (q : ℚˣ) :
    let K := rationalPrimeLocalField p hp
    let Ω := rationalPrimeLocalClosure p hp
    ∃ (a c : ℕ), 0 < a ∧ 0 < c ∧ ¬p ∣ c ∧
      ∃ ha : ¬p ∣ a, ∃ u : 𝒪[K]ˣ, ∃ hu : u.val = a, ∃ b d : ℕ,
        a.Coprime (p ^ (n + 1)) ∧ b.Coprime (p ^ (n + 1)) ∧
        c.Coprime (p ^ (n + 1)) ∧ d.Coprime (p ^ (n + 1)) ∧
        a * b ≡ 1 [MOD p ^ (n + 1)] ∧
        c * d ≡ 1 [MOD p ^ (n + 1)] ∧
        let L := rationalPrimeOriginalCyclotomicClosureStage p hp n a u hu ha
        letI : IsCyclic Gal(L/K) :=
          rationalPrimeOriginalCyclotomicClosureStage_isCyclic p hp hp2 n a u hu ha
        letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω) := ⊥
        letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω) := ⟨rfl⟩
        (localFieldFiniteCyclicReciprocity K Ω L
          (Additive.ofMul (rationalPrimeRationalUnit p hp q))).toMul
            (rationalPrimeOriginalCyclotomicClosureRoot p hp n a u hu ha) =
          (rationalPrimeOriginalCyclotomicClosureRoot p hp n a u hu ha) ^ (b * c) := by
  dsimp only
  let K := rationalPrimeLocalField p hp
  let Ω := rationalPrimeLocalClosure p hp
  let qK := rationalPrimeRationalUnit p hp q
  let π := rationalPrimePrimeUnit p hp
  let z := localFieldUnitOrder K (Additive.ofMul qK)
  let q₀ : Kˣ := qK / π ^ z
  have hπorder : localFieldUnitOrder K (Additive.ofMul π) = 1 := by
    exact rationalPrimeLocalField_prime_order p hp
  have hq₀order : localFieldUnitOrder K (Additive.ofMul q₀) = 0 := by
    change localFieldUnitOrder K
      (Additive.ofMul qK - z • Additive.ofMul π) = 0
    rw [map_sub, map_zsmul, hπorder, zsmul_eq_mul, mul_one]
    exact sub_self z
  have hq₀norm : ‖(q₀ : K)‖ = 1 :=
    rationalPrime_norm_eq_one_of_order_zero p hp q₀ hq₀order
  let L₀ := rationalPrimeOriginalCyclotomicStage p hp n
  obtain ⟨a, c, ha, hc, v₀, hv₀⟩ :=
    rationalPrime_exists_positive_quotient_norm_comparison p hp L₀ q₀ hq₀norm
  have ha0 : 0 < a := Nat.pos_of_ne_zero (fun ha0 => ha (by simp [ha0]))
  have hc0 : 0 < c := Nat.pos_of_ne_zero (fun hc0 => hc (by simp [hc0]))
  obtain ⟨u, hu, b, d, hca, hcb, hcc, hcd, hab, hcdinv, haction⟩ :=
    rationalPrimeNaturalQuotient_exists_reciprocity_root_action
      p hp hp2 n a c ha hc
  refine ⟨a, c, ha0, hc0, hc, ha, u, hu, b, d,
    hca, hcb, hcc, hcd, hab, hcdinv, ?_⟩
  let L := rationalPrimeOriginalCyclotomicClosureStage p hp n a u hu ha
  letI : IsCyclic Gal(L/K) :=
    rationalPrimeOriginalCyclotomicClosureStage_isCyclic p hp hp2 n a u hu ha
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω) := ⟨rfl⟩
  let e := rationalPrimeOriginalCyclotomicClosureEquiv p hp n a u hu ha
  let v : Lˣ := Units.map e.toMonoidHom v₀
  have hv : Units.map (Algebra.norm K (S := L)) v =
      q₀ / rationalPrimeNaturalQuotientUnit p hp a c ha hc := by
    exact (algEquiv_unit_norm_transport e v₀).trans hv₀
  let ρ := localFieldFiniteCyclicReciprocity K Ω L
  have hratiozero : ρ (Additive.ofMul
      (q₀ / rationalPrimeNaturalQuotientUnit p hp a c ha hc)) = 0 :=
    (localFieldFiniteCyclicReciprocity_eq_zero_iff K Ω L _).mpr ⟨v, hv⟩
  have hq₀eq : ρ (Additive.ofMul q₀) =
      ρ (Additive.ofMul (rationalPrimeNaturalQuotientUnit p hp a c ha hc)) := by
    change ρ (Additive.ofMul q₀ -
      Additive.ofMul (rationalPrimeNaturalQuotientUnit p hp a c ha hc)) = 0 at hratiozero
    rw [map_sub, sub_eq_zero] at hratiozero
    exact hratiozero
  have hπzero : ρ (Additive.ofMul π) = 0 := by
    apply Additive.toMul.injective
    simpa using
      (rationalPrimeOriginalCyclotomicClosure_reciprocity_prime
        p hp hp2 n a u hu ha)
  have hq₀qK : ρ (Additive.ofMul q₀) = ρ (Additive.ofMul qK) := by
    change ρ (Additive.ofMul qK - z • Additive.ofMul π) = ρ (Additive.ofMul qK)
    rw [map_sub, map_zsmul, hπzero, zsmul_zero, sub_zero]
  have hqKeq : ρ (Additive.ofMul qK) =
      ρ (Additive.ofMul (rationalPrimeNaturalQuotientUnit p hp a c ha hc)) :=
    hq₀qK.symm.trans hq₀eq
  rw [hqKeq]
  exact haction

end
end Dubon2026
