import Dubon2026.ArithmeticCyclotomicSignedAwayProduct
import Dubon2026.RationalPrimeCyclotomicReciprocityCharacterCancellation
import Dubon2026.RationalPrimeLocalizedIntegerUnits
import Mathlib.NumberTheory.Padics.RingHoms

/-! # Conductor reduction of the normalized rational residual

The actual rational-prime valuation-integer ring is transported to `ℤ_[p]`
and reduced with `PadicInt.toZModPow`.  Restricting this map to the proved
order-zero kernel gives a multiplicative conductor-reduction character.

The positive rational norm witness is chosen in the congruence class
`r + p^N m`, with `N` at least the conductor exponent.  Its forward quotient
unit therefore has exactly the same reduction as `r`.  Applying this to the
normalized rational residual identifies its signed real/away-prime product
with the forward unit occurring in the ramified reciprocity cancellation.
-/
namespace Dubon2026
noncomputable section

set_option maxHeartbeats 1200000

open IsDedekindDomain HeightOneSpectrum Metric
open scoped ValuativeRel
attribute [local instance 1100] Ring.toIntAlgebra
attribute [local instance] rationalPrimeWittPrime wittCyclotomicRootDomain
  wittCyclotomicRootFaithful wittCyclotomicFieldAlgebra wittCyclotomicFieldTower
  rationalPrimeWittOriginalAlgebra rationalPrimeWittCyclotomicAlgebra
  rationalPrimeWittCyclotomicTower rationalPrimeWittCyclotomicModule
  rationalPrimeWittCyclotomicMulAction

/-- Reduction of the actual rational-prime valuation-integer ring modulo
`p^k`, transported through its proved equivalence with `ℤ_[p]`. -/
def rationalPrimeIntegerReduction
    (p : ℕ) (hp : p.Prime) (k : ℕ) :
    𝒪[rationalPrimeLocalField p hp] →+* ZMod (p ^ k) := by
  letI : Fact p.Prime := ⟨hp⟩
  let e₁ : 𝒪[rationalPrimeLocalField p hp] ≃+* rationalPrimeLocalIntegerRing p hp :=
    RingEquiv.subringCongr (rationalPrimeLocalInteger_subring_eq p hp)
  let e₂ := (PadicInt.adicCompletionIntegersEquiv ℤ ⟨p, hp⟩).symm.toRingEquiv
  exact (PadicInt.toZModPow k).comp (e₁.trans e₂).toRingHom

/-- The actual rational-prime integer reduction sends a natural integer to
its canonical class modulo `p^k`. -/
theorem rationalPrimeIntegerReduction_natCast
    (p : ℕ) (hp : p.Prime) (k a : ℕ) :
    rationalPrimeIntegerReduction p hp k (a : 𝒪[rationalPrimeLocalField p hp]) =
      (a : ZMod (p ^ k)) := by
  exact map_natCast (rationalPrimeIntegerReduction p hp k) a

/-- The subgroup of actual local-field units with normalized order zero. -/
def localFieldOrderZeroSubgroup
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : Subgroup Kˣ where
  carrier := {u | localFieldUnitOrder K (Additive.ofMul u) = 0}
  one_mem' := map_zero (localFieldUnitOrder K)
  mul_mem' := by
    intro a b ha hb
    change localFieldUnitOrder K (Additive.ofMul a + Additive.ofMul b) = 0
    rw [map_add, ha, hb, add_zero]
  inv_mem' := by
    intro a ha
    change localFieldUnitOrder K (-Additive.ofMul a) = 0
    rw [map_neg, ha, neg_zero]

/-- Inclusion of actual valuation-integer units into the order-zero subgroup
of local-field units. -/
def localFieldIntegerUnitToOrderZero
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    𝒪[K]ˣ →* localFieldOrderZeroSubgroup K where
  toFun u := ⟨Units.map (algebraMap 𝒪[K] K).toMonoidHom u,
    (localFieldUnitOrder_eq_zero_iff_integer_unit K _).mpr ⟨u, rfl⟩⟩
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

/-- The proved order-zero kernel theorem as a multiplicative equivalence
between valuation-integer units and order-zero field units. -/
def localFieldIntegerUnitOrderZeroEquiv
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    𝒪[K]ˣ ≃* localFieldOrderZeroSubgroup K :=
  MulEquiv.ofBijective (localFieldIntegerUnitToOrderZero K) ⟨
    fun _ _ h => localFieldIntegerUnit_inclusion_injective K (Subtype.ext_iff.mp h),
    by
      intro u
      obtain ⟨a, ha⟩ := (localFieldUnitOrder_eq_zero_iff_integer_unit K u.val).mp u.property
      refine ⟨a, ?_⟩
      exact Subtype.ext ha⟩

/-- Reduction modulo `p^k` on actual order-zero rational-prime local units. -/
def rationalPrimeOrderZeroReduction
    (p : ℕ) (hp : p.Prime) (k : ℕ) :
    localFieldOrderZeroSubgroup (rationalPrimeLocalField p hp) →*
      (ZMod (p ^ k))ˣ :=
  (Units.map (rationalPrimeIntegerReduction p hp k).toMonoidHom).comp
    (localFieldIntegerUnitOrderZeroEquiv (rationalPrimeLocalField p hp)).symm.toMonoidHom

/-- The valuation-integer unit with literal positive natural value away from
the rational prime `p`. -/
def rationalPrimeValuationNaturalUnit
    (p : ℕ) (hp : p.Prime) (a : ℕ) (ha : ¬p ∣ a) :
    𝒪[rationalPrimeLocalField p hp]ˣ :=
  (rationalPrimeValuationInteger_isUnit_int p hp (a : ℤ) (by exact_mod_cast ha)).unit

/-- The valuation-integer natural unit has its displayed literal value. -/
@[simp] theorem rationalPrimeValuationNaturalUnit_val
    (p : ℕ) (hp : p.Prime) (a : ℕ) (ha : ¬p ∣ a) :
    (rationalPrimeValuationNaturalUnit p hp a ha :
      𝒪[rationalPrimeLocalField p hp]) = a := by
  exact IsUnit.unit_spec _

/-- A positive natural away from `p`, regarded as an order-zero local unit. -/
def rationalPrimeOrderZeroNaturalUnit
    (p : ℕ) (hp : p.Prime) (a : ℕ) (ha : ¬p ∣ a) :
    localFieldOrderZeroSubgroup (rationalPrimeLocalField p hp) :=
  localFieldIntegerUnitToOrderZero (rationalPrimeLocalField p hp)
    (rationalPrimeValuationNaturalUnit p hp a ha)

/-- Conductor reduction sends an away natural unit to `unitOfCoprime`. -/
theorem rationalPrimeOrderZeroReduction_naturalUnit
    (p : ℕ) (hp : p.Prime) (k a : ℕ) (ha : ¬p ∣ a) :
    rationalPrimeOrderZeroReduction p hp k
        (rationalPrimeOrderZeroNaturalUnit p hp a ha) =
      ZMod.unitOfCoprime a (hp.coprime_pow_of_not_dvd ha) := by
  apply Units.ext
  change rationalPrimeIntegerReduction p hp k
      (((localFieldIntegerUnitOrderZeroEquiv (rationalPrimeLocalField p hp)).symm
        (localFieldIntegerUnitToOrderZero (rationalPrimeLocalField p hp)
          (rationalPrimeValuationNaturalUnit p hp a ha))) :
            𝒪[rationalPrimeLocalField p hp]ˣ).val = _
  have heq :
      localFieldIntegerUnitToOrderZero (rationalPrimeLocalField p hp)
          (rationalPrimeValuationNaturalUnit p hp a ha) =
        localFieldIntegerUnitOrderZeroEquiv (rationalPrimeLocalField p hp)
          (rationalPrimeValuationNaturalUnit p hp a ha) := rfl
  rw [heq, (localFieldIntegerUnitOrderZeroEquiv
    (rationalPrimeLocalField p hp)).symm_apply_apply]
  simp only [rationalPrimeValuationNaturalUnit_val,
    rationalPrimeIntegerReduction_natCast, ZMod.coe_unitOfCoprime]

/-- The actual local image of an order-zero rational unit, packaged in the
order-zero subgroup. -/
def rationalPrimeOrderZeroRationalUnit
    (p : ℕ) (hp : p.Prime) (q : ℚˣ)
    (hq : localFieldUnitOrder (rationalPrimeLocalField p hp)
      (Additive.ofMul (rationalPrimeRationalUnit p hp q)) = 0) :
    localFieldOrderZeroSubgroup (rationalPrimeLocalField p hp) :=
  ⟨rationalPrimeRationalUnit p hp q, hq⟩

/-- Two order-zero local units differing by `p^N m` have equal reduction
modulo `p^k` whenever `k ≤ N`. -/
theorem rationalPrimeOrderZeroReduction_eq_of_sub_eq_primePow_mul_nat
    (p : ℕ) (hp : p.Prime) (k N m : ℕ) (hkN : k ≤ N)
    (u v : localFieldOrderZeroSubgroup (rationalPrimeLocalField p hp))
    (hsub : ((u.val : (rationalPrimeLocalField p hp)ˣ) :
        rationalPrimeLocalField p hp) -
        ((v.val : (rationalPrimeLocalField p hp)ˣ) :
          rationalPrimeLocalField p hp) =
      (p : rationalPrimeLocalField p hp) ^ N * m) :
    rationalPrimeOrderZeroReduction p hp k u = rationalPrimeOrderZeroReduction p hp k v := by
  let K := rationalPrimeLocalField p hp
  let e := localFieldIntegerUnitOrderZeroEquiv K
  let a : 𝒪[K]ˣ := e.symm u
  let b : 𝒪[K]ˣ := e.symm v
  have hau : localFieldIntegerUnitToOrderZero K a = u := by
    exact e.apply_symm_apply u
  have hbv : localFieldIntegerUnitToOrderZero K b = v := by
    exact e.apply_symm_apply v
  have hab : a.val - b.val = (p : 𝒪[K]) ^ N * m := by
    apply Subtype.ext
    change (a.val : K) - (b.val : K) = (p : K) ^ N * m
    have hau' := congrArg (fun x : localFieldOrderZeroSubgroup K =>
      (((x : Kˣ) : K))) hau
    have hbv' := congrArg (fun x : localFieldOrderZeroSubgroup K =>
      (((x : Kˣ) : K))) hbv
    have hauK : (a.val : K) = ((u.val : Kˣ) : K) := by
      simpa [localFieldIntegerUnitToOrderZero] using hau'
    have hbvK : (b.val : K) = ((v.val : Kˣ) : K) := by
      simpa [localFieldIntegerUnitToOrderZero] using hbv'
    rw [hauK, hbvK]
    exact hsub
  apply Units.ext
  change rationalPrimeIntegerReduction p hp k a.val =
    rationalPrimeIntegerReduction p hp k b.val
  rw [← sub_eq_zero, ← map_sub, hab, map_mul, map_pow, map_natCast, map_natCast]
  have hpzero : (p : ZMod (p ^ k)) ^ N = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
    exact pow_dvd_pow p hkN
  rw [hpzero, zero_mul]

/-- A positive rational approximation can be chosen in the same residue
class modulo an arbitrarily prescribed power of the local prime. -/
theorem rationalPrime_exists_positive_primePower_shift_norm_sub_lt
    (p : ℕ) (hp : p.Prime) (x : ℚ) (k : ℕ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (N m : ℕ), k ≤ N ∧ 0 < x + (p : ℚ) ^ N * m ∧
      ‖algebraMap ℚ (rationalPrimeLocalField p hp)
          (x + (p : ℚ) ^ N * m) -
        algebraMap ℚ (rationalPrimeLocalField p hp) x‖ < ε := by
  let K := rationalPrimeLocalField p hp
  haveI : IsUltrametricDist K := inferInstance
  have hpnorm : ‖(p : K)‖ < 1 := by
    have hmem : (p : ℤ) ∈ (rationalPrimePlace p hp).asIdeal :=
      (rationalPrimePlace_nat_mem_iff p hp p).mpr (dvd_refl p)
    have h := (NumberField.FinitePlace.norm_lt_one_iff_mem
      (K := ℚ) (v := rationalPrimePlace p hp) (p : ℤ)).mpr hmem
    simpa only [map_intCast, map_natCast] using h
  obtain ⟨N₀, hN₀⟩ := exists_pow_lt_of_lt_one hε hpnorm
  let N := N₀ + k
  have hkN : k ≤ N := by simp [N]
  have hN : ‖(p : K)‖ ^ N < ε := by
    have hkone : ‖(p : K)‖ ^ k ≤ 1 := pow_le_one₀ (norm_nonneg _) hpnorm.le
    calc
      ‖(p : K)‖ ^ N = ‖(p : K)‖ ^ N₀ * ‖(p : K)‖ ^ k := by
        change ‖(p : K)‖ ^ (N₀ + k) = _
        rw [pow_add]
      _ ≤ ‖(p : K)‖ ^ N₀ :=
        mul_le_of_le_one_right (pow_nonneg (norm_nonneg _) _) hkone
      _ < ε := hN₀
  have hpqpos : 0 < (p : ℚ) ^ N := pow_pos (by exact_mod_cast hp.pos) N
  obtain ⟨m, hm⟩ := exists_nat_gt (-x / ((p : ℚ) ^ N))
  have hqpos : 0 < x + (p : ℚ) ^ N * m := by
    have hm' : -x < (m : ℚ) * (p : ℚ) ^ N :=
      (div_lt_iff₀ hpqpos).mp hm
    rw [mul_comm ((p : ℚ) ^ N)]
    linarith
  refine ⟨N, m, hkN, hqpos, ?_⟩
  have hmnorm : ‖(m : K)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one K m
  rw [map_add, add_sub_cancel_left, map_mul, map_pow, map_natCast, map_natCast,
    norm_mul, norm_pow]
  exact (mul_le_of_le_one_right (pow_nonneg (norm_nonneg _) _) hmnorm).trans_lt hN

/-- The positive norm-comparison quotient can be chosen with exactly the
same conductor residue as the original rational order-zero unit. -/
theorem rationalPrime_exists_positive_quotient_norm_comparison_reduction
    (p : ℕ) (hp : p.Prime) (k : ℕ)
    (L : Type) [Field L] [Algebra (rationalPrimeLocalField p hp) L]
    [FiniteDimensional (rationalPrimeLocalField p hp) L]
    (r : ℚˣ)
    (hr : localFieldUnitOrder (rationalPrimeLocalField p hp)
      (Additive.ofMul (rationalPrimeRationalUnit p hp r)) = 0) :
    ∃ (a c : ℕ) (ha : ¬p ∣ a) (hc : ¬p ∣ c),
      ∃ v : Lˣ,
        Units.map (Algebra.norm (rationalPrimeLocalField p hp) (S := L)) v =
          rationalPrimeRationalUnit p hp r /
            rationalPrimeNaturalQuotientUnit p hp a c ha hc ∧
        rationalPrimeOrderZeroReduction p hp k
            (rationalPrimeOrderZeroRationalUnit p hp r hr) =
          ZMod.unitOfCoprime a (hp.coprime_pow_of_not_dvd ha) *
            (ZMod.unitOfCoprime c (hp.coprime_pow_of_not_dvd hc))⁻¹ := by
  let K := rationalPrimeLocalField p hp
  let u := rationalPrimeRationalUnit p hp r
  have hu : ‖(u : K)‖ = 1 := rationalPrime_norm_eq_one_of_order_zero p hp u hr
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
  obtain ⟨δ, hδ0, hδ1, hnormball⟩ :=
    finiteDimensional_exists_norm_near_one K L hd0
  have hdnorm : 0 < ‖(Module.finrank K L : K)‖ := norm_pos_iff.mpr hd0
  let ε : ℝ := ‖(Module.finrank K L : K)‖ * δ
  have hε : 0 < ε := mul_pos hdnorm hδ0
  have hεone : ε < 1 := by
    have hdle : ‖(Module.finrank K L : K)‖ ≤ 1 :=
      IsUltrametricDist.norm_natCast_le_one K (Module.finrank K L)
    exact (mul_le_of_le_one_left hδ0.le hdle).trans_lt hδ1
  obtain ⟨N, m, hkN, hqpos, hqclose⟩ :=
    rationalPrime_exists_positive_primePower_shift_norm_sub_lt
      p hp r.val k ε hε
  let q : ℚ := r.val + (p : ℚ) ^ N * m
  have hqclose' : ‖algebraMap ℚ K q - (u : K)‖ < ε := by
    simpa only [q, u, rationalPrimeRationalUnit, Units.coe_map] using hqclose
  have hq0 : q ≠ 0 := hqpos.ne'
  let qU : Kˣ := Units.map (algebraMap ℚ K).toMonoidHom (Units.mk0 q hq0)
  have hqcloseOne : ‖(qU : K) - (u : K)‖ < 1 := hqclose'.trans hεone
  have hqnorm : ‖(qU : K)‖ = 1 := by
    have hqle : ‖(qU : K)‖ ≤ 1 := by
      calc
        ‖(qU : K)‖ = ‖((qU : K) - (u : K)) + (u : K)‖ := by rw [sub_add_cancel]
        _ ≤ max ‖(qU : K) - (u : K)‖ ‖(u : K)‖ :=
          IsUltrametricDist.norm_add_le_max _ _
        _ ≤ 1 := max_le hqcloseOne.le (by rw [hu])
    have honele : 1 ≤ ‖(qU : K)‖ := by
      by_contra hnot
      have hqlt : ‖(qU : K)‖ < 1 := lt_of_not_ge hnot
      have hult : ‖(u : K)‖ < 1 := by
        calc
          ‖(u : K)‖ = ‖((u : K) - (qU : K)) + (qU : K)‖ := by rw [sub_add_cancel]
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
  obtain ⟨w, hw⟩ := hnormball (u / qU) hratio
  let qZ : localFieldOrderZeroSubgroup K :=
    rationalPrimeOrderZeroNaturalUnit p hp a ha /
      rationalPrimeOrderZeroNaturalUnit p hp c hc
  let rZ := rationalPrimeOrderZeroRationalUnit p hp r hr
  have hsub : ((qZ.val : Kˣ) : K) - ((rZ.val : Kˣ) : K) = (p : K) ^ N * m := by
    have hqZ : qZ.val = qU := by
      apply Units.ext
      let H := localFieldOrderZeroSubgroup K
      let j : H →* K := (Units.coeHom K).comp H.subtype
      change j (rationalPrimeOrderZeroNaturalUnit p hp a ha /
          rationalPrimeOrderZeroNaturalUnit p hp c hc) = (qU : K)
      rw [map_div]
      change algebraMap 𝒪[K] K
          (rationalPrimeValuationNaturalUnit p hp a ha).val /
        algebraMap 𝒪[K] K
          (rationalPrimeValuationNaturalUnit p hp c hc).val = (qU : K)
      rw [rationalPrimeValuationNaturalUnit_val,
        rationalPrimeValuationNaturalUnit_val, map_natCast, map_natCast]
      simpa only [qN, rationalPrimeNaturalQuotientUnit,
        rationalPrimeNaturalUnit_val, Units.val_div_eq_div_val] using
          congrArg Units.val hqUN.symm
    rw [hqZ]
    change algebraMap ℚ K q - algebraMap ℚ K r.val = (p : K) ^ N * m
    rw [show q = r.val + (p : ℚ) ^ N * m by rfl, map_add, map_mul, map_pow,
      map_natCast, map_natCast, add_sub_cancel_left]
  have hred : rationalPrimeOrderZeroReduction p hp k qZ =
      rationalPrimeOrderZeroReduction p hp k rZ :=
    rationalPrimeOrderZeroReduction_eq_of_sub_eq_primePow_mul_nat p hp k N m hkN qZ rZ hsub
  have hqred : rationalPrimeOrderZeroReduction p hp k qZ =
      ZMod.unitOfCoprime a (hp.coprime_pow_of_not_dvd ha) *
        (ZMod.unitOfCoprime c (hp.coprime_pow_of_not_dvd hc))⁻¹ := by
    dsimp only [qZ]
    rw [map_div, rationalPrimeOrderZeroReduction_naturalUnit,
      rationalPrimeOrderZeroReduction_naturalUnit]
    exact div_eq_mul_inv _ _
  refine ⟨a, c, ha, hc, w, ?_, hred.symm.trans hqred⟩
  simpa only [hqUN] using hw

private theorem primitiveRoot_autToPow_mul_forwardUnit_eq_one_reduction
    (K L : Type*) [CommRing K] [Field L] [Algebra K L]
    (N : ℕ) [NeZero N] {ζ : L} (hζ : IsPrimitiveRoot ζ N)
    (σ : L ≃ₐ[K] L) (e : ℕ) (he : e.Coprime N)
    (hcancel : (σ ζ) ^ e = ζ) :
    hζ.autToPow K σ * ZMod.unitOfCoprime e he = 1 := by
  have hpow : ζ ^ ((hζ.autToPow K σ : (ZMod N)ˣ).val.val * e) = ζ ^ 1 := by
    calc
      ζ ^ ((hζ.autToPow K σ : (ZMod N)ˣ).val.val * e) =
          (ζ ^ (hζ.autToPow K σ : (ZMod N)ˣ).val.val) ^ e := by rw [pow_mul]
      _ = (σ ζ) ^ e := by rw [hζ.autToPow_spec K]
      _ = ζ := hcancel
      _ = ζ ^ 1 := (pow_one ζ).symm
  have hmod : (hζ.autToPow K σ : (ZMod N)ˣ).val.val * e ≡ 1 [MOD N] := by
    have hm := (hζ.isOfFinOrder (NeZero.ne N)).pow_eq_pow_iff_modEq.mp hpow
    simpa only [hζ.eq_orderOf] using hm
  apply Units.ext
  change (hζ.autToPow K σ : ZMod N) * ((e : ℕ) : ZMod N) = 1
  rw [← ZMod.natCast_zmod_val (hζ.autToPow K σ : ZMod N),
    ← Nat.cast_mul, ← Nat.cast_one]
  exact (ZMod.natCast_eq_natCast_iff _ _ N).2 hmod

/-- For an order-zero rational unit, the ramified cyclotomic cancellation
witness can be selected so that its forward unit is its exact conductor
reduction. -/
theorem rationalPrimeOrderZero_exists_character_cancellation_reduction
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (n : ℕ) (r : ℚˣ)
    (hr : localFieldUnitOrder (rationalPrimeLocalField p hp)
      (Additive.ofMul (rationalPrimeRationalUnit p hp r)) = 0) :
    let K := rationalPrimeLocalField p hp
    let Ω := rationalPrimeLocalClosure p hp
    ∃ (a c : ℕ), 0 < a ∧ 0 < c ∧ ¬p ∣ c ∧
      ∃ ha : ¬p ∣ a, ∃ u : 𝒪[K]ˣ, ∃ hu : u.val = a, ∃ b d : ℕ,
        ∃ hca : a.Coprime (p ^ (n + 1)),
        ∃ hcd : d.Coprime (p ^ (n + 1)),
        b.Coprime (p ^ (n + 1)) ∧ c.Coprime (p ^ (n + 1)) ∧
        a * b ≡ 1 [MOD p ^ (n + 1)] ∧
        c * d ≡ 1 [MOD p ^ (n + 1)] ∧
        let L := rationalPrimeOriginalCyclotomicClosureStage p hp n a u hu ha
        letI : IsCyclic Gal(L/K) :=
          rationalPrimeOriginalCyclotomicClosureStage_isCyclic p hp hp2 n a u hu ha
        letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω) := ⊥
        letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω) := ⟨rfl⟩
        let ζ := rationalPrimeOriginalCyclotomicClosureRoot p hp n a u hu ha
        let σ := (localFieldFiniteCyclicReciprocity K Ω L
          (Additive.ofMul (rationalPrimeRationalUnit p hp r))).toMul
        letI : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
        σ ζ = ζ ^ (b * c) ∧
        (rationalPrimeOriginalCyclotomicClosureRoot_isPrimitive p hp n a u hu ha).autToPow
            K σ * ZMod.unitOfCoprime (a * d) (hca.mul_left hcd) = 1 ∧
        rationalPrimeOrderZeroReduction p hp (n + 1)
            (rationalPrimeOrderZeroRationalUnit p hp r hr) =
          ZMod.unitOfCoprime (a * d) (hca.mul_left hcd) := by
  dsimp only
  let K := rationalPrimeLocalField p hp
  let Ω := rationalPrimeLocalClosure p hp
  let qK := rationalPrimeRationalUnit p hp r
  let L₀ := rationalPrimeOriginalCyclotomicStage p hp n
  obtain ⟨a, c, ha, hc, v₀, hv₀, hreduction⟩ :=
    rationalPrime_exists_positive_quotient_norm_comparison_reduction
      p hp (n + 1) L₀ r hr
  have ha0 : 0 < a := Nat.pos_of_ne_zero (fun ha0 => ha (by simp [ha0]))
  have hc0 : 0 < c := Nat.pos_of_ne_zero (fun hc0 => hc (by simp [hc0]))
  obtain ⟨u, hu, b, d, hca, hcb, hcc, hcd, hab, hcdinv, hactionQ⟩ :=
    rationalPrimeNaturalQuotient_exists_reciprocity_root_action
      p hp hp2 n a c ha hc
  let L := rationalPrimeOriginalCyclotomicClosureStage p hp n a u hu ha
  letI : IsCyclic Gal(L/K) :=
    rationalPrimeOriginalCyclotomicClosureStage_isCyclic p hp hp2 n a u hu ha
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω) := ⟨rfl⟩
  let e := rationalPrimeOriginalCyclotomicClosureEquiv p hp n a u hu ha
  let v : Lˣ := Units.map e.toMonoidHom v₀
  have hv : Units.map (Algebra.norm K (S := L)) v =
      qK / rationalPrimeNaturalQuotientUnit p hp a c ha hc := by
    exact (algEquiv_unit_norm_transport e v₀).trans hv₀
  let ρ := localFieldFiniteCyclicReciprocity K Ω L
  have hratiozero : ρ (Additive.ofMul
      (qK / rationalPrimeNaturalQuotientUnit p hp a c ha hc)) = 0 :=
    (localFieldFiniteCyclicReciprocity_eq_zero_iff K Ω L _).mpr ⟨v, hv⟩
  have hqeq : ρ (Additive.ofMul qK) =
      ρ (Additive.ofMul (rationalPrimeNaturalQuotientUnit p hp a c ha hc)) := by
    change ρ (Additive.ofMul qK -
      Additive.ofMul (rationalPrimeNaturalQuotientUnit p hp a c ha hc)) = 0 at hratiozero
    rw [map_sub, sub_eq_zero] at hratiozero
    exact hratiozero
  let ζ := rationalPrimeOriginalCyclotomicClosureRoot p hp n a u hu ha
  let σ := (ρ (Additive.ofMul qK)).toMul
  have haction : σ ζ = ζ ^ (b * c) := by
    change (ρ (Additive.ofMul qK)).toMul ζ = ζ ^ (b * c)
    rw [hqeq]
    exact hactionQ
  have hcancel : (σ ζ) ^ (a * d) = ζ := by
    rw [haction, ← pow_mul]
    have hζ := rationalPrimeOriginalCyclotomicClosureRoot_isPrimitive p hp n a u hu ha
    have hm : p ^ (n + 1) ≠ 0 := pow_ne_zero _ hp.ne_zero
    have hmod : (b * c) * (a * d) ≡ 1 [MOD p ^ (n + 1)] := by
      simpa only [one_mul, mul_one, mul_assoc, mul_left_comm, mul_comm] using
        hab.mul hcdinv
    calc
      ζ ^ ((b * c) * (a * d)) = ζ ^ 1 :=
        (hζ.isOfFinOrder hm).pow_eq_pow_iff_modEq.mpr (by
          simpa only [hζ.eq_orderOf] using hmod)
      _ = ζ := pow_one ζ
  letI : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hchar :
      (rationalPrimeOriginalCyclotomicClosureRoot_isPrimitive p hp n a u hu ha).autToPow
          K σ * ZMod.unitOfCoprime (a * d) (hca.mul_left hcd) = 1 :=
    primitiveRoot_autToPow_mul_forwardUnit_eq_one_reduction K L (p ^ (n + 1))
      (rationalPrimeOriginalCyclotomicClosureRoot_isPrimitive p hp n a u hu ha)
      σ (a * d) (hca.mul_left hcd) hcancel
  have hcdunit :
      ZMod.unitOfCoprime c hcc * ZMod.unitOfCoprime d hcd = 1 := by
    apply Units.ext
    change ((c : ℕ) : ZMod (p ^ (n + 1))) * d = 1
    rw [← Nat.cast_mul, ← Nat.cast_one]
    simpa only [Nat.cast_one] using
      (ZMod.natCast_eq_natCast_iff _ _ (p ^ (n + 1))).2 hcdinv
  have hcInv : (ZMod.unitOfCoprime c hcc)⁻¹ = ZMod.unitOfCoprime d hcd := by
    exact inv_eq_of_mul_eq_one_right hcdunit
  have had :
      ZMod.unitOfCoprime a hca * ZMod.unitOfCoprime d hcd =
        ZMod.unitOfCoprime (a * d) (hca.mul_left hcd) := by
    apply Units.ext
    change ((a : ℕ) : ZMod (p ^ (n + 1))) * d = ((a * d : ℕ) : ZMod (p ^ (n + 1)))
    rw [Nat.cast_mul]
  have hforward : rationalPrimeOrderZeroReduction p hp (n + 1)
      (rationalPrimeOrderZeroRationalUnit p hp r hr) =
        ZMod.unitOfCoprime (a * d) (hca.mul_left hcd) := by
    calc
      _ = ZMod.unitOfCoprime a hca * (ZMod.unitOfCoprime c hcc)⁻¹ := hreduction
      _ = ZMod.unitOfCoprime a hca * ZMod.unitOfCoprime d hcd := by rw [hcInv]
      _ = _ := had
  exact ⟨a, c, ha0, hc0, hc, ha, u, hu, b, d, hca, hcd,
    hcb, hcc, hab, hcdinv, haction, hchar, hforward⟩

/-- Every generator in a support omitting the actual `p`-place is prime to
`p`. -/
theorem rationalPrime_finiteSupport_generator_not_dvd
    (p : ℕ) (hp : p.Prime) (S : Finset (HeightOneSpectrum ℤ))
    (hpS : rationalPrimePlace p hp ∉ S) (v : HeightOneSpectrum ℤ) (hv : v ∈ S) :
    ¬p ∣ Rat.HeightOneSpectrum.natGenerator v := by
  intro hdvd
  have heq : p = Rat.HeightOneSpectrum.natGenerator v :=
    ((Nat.dvd_prime (Rat.HeightOneSpectrum.prime_natGenerator v)).mp hdvd).resolve_left hp.ne_one
  have hplace : rationalPrimePlace p hp = v := by
    apply Rat.HeightOneSpectrum.primesEquiv.injective
    apply Subtype.ext
    change Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p hp) =
      Rat.HeightOneSpectrum.natGenerator v
    exact (rationalPrimePlace_natGenerator p hp).trans heq
  exact hpS (hplace ▸ hv)

/-- The real sign and finite away-prime factors, multiplied inside the
order-zero subgroup of the rational `p`-adic field. -/
def rationalPrimeSignedProductOrderZero
    (p : ℕ) (hp : p.Prime) (S : Finset (HeightOneSpectrum ℤ))
    (hpS : rationalPrimePlace p hp ∉ S) (q : ℚˣ) :
    localFieldOrderZeroSubgroup (rationalPrimeLocalField p hp) :=
  (if 0 < q.val then 1 else
    localFieldIntegerUnitToOrderZero (rationalPrimeLocalField p hp) (-1)) *
  S.attach.prod fun v =>
    rationalPrimeOrderZeroNaturalUnit p hp
        (Rat.HeightOneSpectrum.natGenerator v.1)
        (rationalPrime_finiteSupport_generator_not_dvd p hp S hpS v.1 v.2) ^
      localFieldUnitOrder
        (rationalPrimeLocalField (Rat.HeightOneSpectrum.natGenerator v.1)
          (Rat.HeightOneSpectrum.prime_natGenerator v.1))
        (Additive.ofMul
          (rationalPrimeRationalUnit (Rat.HeightOneSpectrum.natGenerator v.1)
            (Rat.HeightOneSpectrum.prime_natGenerator v.1) q))

/-- Reducing the order-zero signed product gives the explicit cyclotomic
signed-away product unit. -/
theorem rationalPrimeOrderZeroReduction_signedProduct
    (p : ℕ) (hp : p.Prime) (k : ℕ)
    (S : Finset (HeightOneSpectrum ℤ)) (hpS : rationalPrimePlace p hp ∉ S)
    (hS : ∀ v ∈ S, ¬Rat.HeightOneSpectrum.natGenerator v ∣ p ^ k)
    (q : ℚˣ) :
    rationalPrimeOrderZeroReduction p hp k
        (rationalPrimeSignedProductOrderZero p hp S hpS q) =
      arithmeticCyclotomicSignedAwayProductUnit (p ^ k) S hS q := by
  rw [rationalPrimeSignedProductOrderZero, map_mul, map_prod]
  apply congrArg₂ (· * ·)
  · by_cases hq : 0 < q.val
    · simp [hq, rationalCyclotomicRealSignUnit]
    · rw [if_neg hq]
      change rationalPrimeOrderZeroReduction p hp k
          (localFieldIntegerUnitToOrderZero (rationalPrimeLocalField p hp) (-1)) =
        rationalCyclotomicRealSignUnit (p ^ k) q
      have heq : localFieldIntegerUnitToOrderZero (rationalPrimeLocalField p hp)
            (-1 : 𝒪[rationalPrimeLocalField p hp]ˣ) =
          localFieldIntegerUnitOrderZeroEquiv (rationalPrimeLocalField p hp) (-1) := rfl
      apply Units.ext
      change rationalPrimeIntegerReduction p hp k
          (((localFieldIntegerUnitOrderZeroEquiv (rationalPrimeLocalField p hp)).symm
            (localFieldIntegerUnitToOrderZero (rationalPrimeLocalField p hp) (-1))) :
              𝒪[rationalPrimeLocalField p hp]ˣ).val = _
      rw [heq, (localFieldIntegerUnitOrderZeroEquiv
        (rationalPrimeLocalField p hp)).symm_apply_apply]
      simp [hq, rationalCyclotomicRealSignUnit]
  · apply Finset.prod_congr rfl
    intro v _hv
    rw [map_zpow, rationalPrimeOrderZeroReduction_naturalUnit]

/-- An exact signed rational prime product represents the original rational
unit inside the order-zero local subgroup. -/
theorem rationalPrimeSignedProductOrderZero_eq_rationalUnit
    (p : ℕ) (hp : p.Prime) (S : Finset (HeightOneSpectrum ℤ))
    (hpS : rationalPrimePlace p hp ∉ S) (q : ℚˣ)
    (hproduct :
      (if 0 < q.val then (1 : ℚ) else -1) *
        (∏ v ∈ S, (Rat.HeightOneSpectrum.natGenerator v : ℚ) ^
          localFieldUnitOrder
            (rationalPrimeLocalField (Rat.HeightOneSpectrum.natGenerator v)
              (Rat.HeightOneSpectrum.prime_natGenerator v))
            (Additive.ofMul
              (rationalPrimeRationalUnit (Rat.HeightOneSpectrum.natGenerator v)
                (Rat.HeightOneSpectrum.prime_natGenerator v) q))) = q.val) :
    (rationalPrimeSignedProductOrderZero p hp S hpS q :
        (rationalPrimeLocalField p hp)ˣ) =
      rationalPrimeRationalUnit p hp q := by
  apply Units.ext
  let K := rationalPrimeLocalField p hp
  let H := localFieldOrderZeroSubgroup K
  let j : H →* K := (Units.coeHom K).comp H.subtype
  change j (rationalPrimeSignedProductOrderZero p hp S hpS q) =
    algebraMap ℚ K q.val
  have hproduct' :
      (if 0 < q.val then (1 : ℚ) else -1) *
        (S.attach.prod fun v =>
          (Rat.HeightOneSpectrum.natGenerator v.1 : ℚ) ^
            localFieldUnitOrder
              (rationalPrimeLocalField (Rat.HeightOneSpectrum.natGenerator v.1)
                (Rat.HeightOneSpectrum.prime_natGenerator v.1))
              (Additive.ofMul
                  (rationalPrimeRationalUnit (Rat.HeightOneSpectrum.natGenerator v.1)
                  (Rat.HeightOneSpectrum.prime_natGenerator v.1) q))) = q.val := by
    rw [← Finset.prod_attach S (fun v =>
      (Rat.HeightOneSpectrum.natGenerator v : ℚ) ^
        localFieldUnitOrder
          (rationalPrimeLocalField (Rat.HeightOneSpectrum.natGenerator v)
            (Rat.HeightOneSpectrum.prime_natGenerator v))
          (Additive.ofMul
            (rationalPrimeRationalUnit (Rat.HeightOneSpectrum.natGenerator v)
              (Rat.HeightOneSpectrum.prime_natGenerator v) q)))] at hproduct
    exact hproduct
  calc
    j (rationalPrimeSignedProductOrderZero p hp S hpS q) =
        algebraMap ℚ K (if 0 < q.val then (1 : ℚ) else -1) *
          (S.attach.prod fun v =>
            algebraMap ℚ K (Rat.HeightOneSpectrum.natGenerator v.1 : ℚ) ^
              localFieldUnitOrder
                (rationalPrimeLocalField (Rat.HeightOneSpectrum.natGenerator v.1)
                  (Rat.HeightOneSpectrum.prime_natGenerator v.1))
                (Additive.ofMul
                  (rationalPrimeRationalUnit (Rat.HeightOneSpectrum.natGenerator v.1)
                    (Rat.HeightOneSpectrum.prime_natGenerator v.1) q))) := by
      rw [rationalPrimeSignedProductOrderZero, map_mul, map_prod]
      apply congrArg₂ (· * ·)
      · by_cases hq : 0 < q.val <;>
          simp [hq, j, H, localFieldIntegerUnitToOrderZero]
      · apply Finset.prod_congr rfl
        intro v _hv
        rw [map_zpow]
        change algebraMap 𝒪[K] K
            (rationalPrimeValuationNaturalUnit p hp
              (Rat.HeightOneSpectrum.natGenerator v.1)
              (rationalPrime_finiteSupport_generator_not_dvd p hp S hpS v.1 v.2)).val ^ _ = _
        rw [rationalPrimeValuationNaturalUnit_val, map_natCast]
        congr 1
        exact (map_natCast (algebraMap ℚ K)
          (Rat.HeightOneSpectrum.natGenerator v.1)).symm
    _ = algebraMap ℚ K
        ((if 0 < q.val then (1 : ℚ) else -1) *
          (S.attach.prod fun v =>
            (Rat.HeightOneSpectrum.natGenerator v.1 : ℚ) ^
              localFieldUnitOrder
                (rationalPrimeLocalField (Rat.HeightOneSpectrum.natGenerator v.1)
                  (Rat.HeightOneSpectrum.prime_natGenerator v.1))
                (Additive.ofMul
                  (rationalPrimeRationalUnit (Rat.HeightOneSpectrum.natGenerator v.1)
                    (Rat.HeightOneSpectrum.prime_natGenerator v.1) q)))) := by
      rw [map_mul, map_prod]
      apply congrArg₂ (· * ·) rfl
      apply Finset.prod_congr rfl
      intro v _hv
      rw [map_zpow₀]
    _ = algebraMap ℚ K q.val := congrArg (algebraMap ℚ K) hproduct'

/-- The signed away-prime character of the normalized residual is exactly
the forward unit selected by the ramified reciprocity cancellation. -/
theorem rationalPrimeNormalizedResidual_exists_forwardUnit_identity
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (m : ℕ) (q : ℚˣ) :
    let K := rationalPrimeLocalField p hp
    let Ω := rationalPrimeLocalClosure p hp
    let N := p ^ (m + 1)
    let r := rationalPrimeNormalizedResidual p hp q
    ∃ S : Finset (HeightOneSpectrum ℤ),
      ∃ hS : ∀ v ∈ S, ¬Rat.HeightOneSpectrum.natGenerator v ∣ N,
        (∀ v ∉ S, v.valuation ℚ r.val = 1) ∧
        (if 0 < r.val then (1 : ℚ) else -1) *
          (∏ v ∈ S, (Rat.HeightOneSpectrum.natGenerator v : ℚ) ^
            localFieldUnitOrder
              (rationalPrimeLocalField (Rat.HeightOneSpectrum.natGenerator v)
                (Rat.HeightOneSpectrum.prime_natGenerator v))
              (Additive.ofMul
                (rationalPrimeRationalUnit (Rat.HeightOneSpectrum.natGenerator v)
                  (Rat.HeightOneSpectrum.prime_natGenerator v) r))) = r.val ∧
        ∃ (a c : ℕ), 0 < a ∧ 0 < c ∧ ¬p ∣ c ∧
          ∃ ha : ¬p ∣ a, ∃ u : 𝒪[K]ˣ, ∃ hu : u.val = a, ∃ b d : ℕ,
            ∃ hca : a.Coprime N, ∃ hcd : d.Coprime N,
            b.Coprime N ∧ c.Coprime N ∧
            a * b ≡ 1 [MOD N] ∧ c * d ≡ 1 [MOD N] ∧
            let L := rationalPrimeOriginalCyclotomicClosureStage p hp m a u hu ha
            letI : IsCyclic Gal(L/K) :=
              rationalPrimeOriginalCyclotomicClosureStage_isCyclic p hp hp2 m a u hu ha
            letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω) := ⊥
            letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω) := ⟨rfl⟩
            let ζ := rationalPrimeOriginalCyclotomicClosureRoot p hp m a u hu ha
            let σ := (localFieldFiniteCyclicReciprocity K Ω L
              (Additive.ofMul (rationalPrimeRationalUnit p hp r))).toMul
            letI : NeZero N := ⟨pow_ne_zero _ hp.ne_zero⟩
            σ ζ = ζ ^ (b * c) ∧
            (rationalPrimeOriginalCyclotomicClosureRoot_isPrimitive p hp m a u hu ha).autToPow
                K σ * ZMod.unitOfCoprime (a * d) (hca.mul_left hcd) = 1 ∧
            arithmeticCyclotomicSignedAwayProductUnit N S hS r =
              ZMod.unitOfCoprime (a * d) (hca.mul_left hcd) := by
  dsimp only
  let r := rationalPrimeNormalizedResidual p hp q
  have hr := rationalPrimeNormalizedResidual_order p hp q
  obtain ⟨S, hpS, houtside, hproduct⟩ :=
    rationalPrimeNormalizedResidual_exists_away_signed_prime_product p hp q
  let hS : ∀ v ∈ S, ¬Rat.HeightOneSpectrum.natGenerator v ∣ p ^ (m + 1) :=
    finiteSupport_away_primePower p hp (m + 1) S hpS
  obtain ⟨a, c, ha0, hc0, hc, ha, u, hu, b, d, hca, hcd,
      hcb, hcc, hab, hcdinv, haction, hchar, hforward⟩ :=
    rationalPrimeOrderZero_exists_character_cancellation_reduction
      p hp hp2 m r hr
  have hsigned :
      (rationalPrimeSignedProductOrderZero p hp S hpS r :
          (rationalPrimeLocalField p hp)ˣ) =
        rationalPrimeRationalUnit p hp r :=
    rationalPrimeSignedProductOrderZero_eq_rationalUnit p hp S hpS r hproduct
  have hsubgroup :
      rationalPrimeSignedProductOrderZero p hp S hpS r =
        rationalPrimeOrderZeroRationalUnit p hp r hr :=
    Subtype.ext hsigned
  have hunit : arithmeticCyclotomicSignedAwayProductUnit (p ^ (m + 1)) S hS r =
      ZMod.unitOfCoprime (a * d) (hca.mul_left hcd) := by
    calc
      arithmeticCyclotomicSignedAwayProductUnit (p ^ (m + 1)) S hS r =
          rationalPrimeOrderZeroReduction p hp (m + 1)
            (rationalPrimeSignedProductOrderZero p hp S hpS r) :=
        (rationalPrimeOrderZeroReduction_signedProduct p hp (m + 1) S hpS hS r).symm
      _ = rationalPrimeOrderZeroReduction p hp (m + 1)
          (rationalPrimeOrderZeroRationalUnit p hp r hr) := by rw [hsubgroup]
      _ = ZMod.unitOfCoprime (a * d) (hca.mul_left hcd) := hforward
  exact ⟨S, hS, houtside, hproduct, a, c, ha0, hc0, hc, ha, u, hu,
    b, d, hca, hcd, hcb, hcc, hab, hcdinv, haction, hchar, hunit⟩

end
end Dubon2026
