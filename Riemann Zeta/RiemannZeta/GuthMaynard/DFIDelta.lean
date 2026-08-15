import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.RingTheory.RootsOfUnity.Complex
import RiemannZeta.GuthMaynard.DFIWeight
import RiemannZeta.GuthMaynard.QuadraticDivisor

open Complex Finset Set
open scoped BigOperators ContDiff Topology
open scoped ArithmeticFunction.Moebius
open Classical

namespace RiemannZeta.GuthMaynard

/-!
# DFI equations (9)--(19): the delta symbol

The source chooses an even smooth function `w`, supported where
`Q ≤ |u| ≤ 2Q`, normalized by `∑_{r≥1} w(r)=1`, and satisfying
`w^(j)(u) ≪_j Q^(-j-1)`.  These are equations (9) and (13).

The support makes every series in the delta symbol finite at each argument.
The definitions below expose an explicit radius large enough to contain every
nonzero term; later identities can therefore use ordinary `Finset` algebra.
-/

/-- The source cutoff used in DFI equations (9)--(19). -/
structure DFIDeltaWeight (Q : ℝ) where
  toFun : ℝ → ℝ
  one_le_Q : 1 ≤ Q
  smooth : ContDiff ℝ ∞ toFun
  even : ∀ u : ℝ, toFun (-u) = toFun u
  support_annulus : Function.support toFun ⊆
    {u : ℝ | Q ≤ |u| ∧ |u| ≤ 2 * Q}
  normalized : ∑' r : ℕ, toFun (r + 1 : ℕ) = 1
  derivativeBound : ∀ j : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ,
    ‖iteratedDeriv j toFun u‖ ≤ C * (Q ^ (j + 1))⁻¹

/-- An explicit family of the equation-(9) derivative constants.  The
profile is kept separate from `DFIDeltaWeight` so a source theorem can
quantify over one `D` before varying the physical scale `Q`. -/
structure DFIDeltaWeightProfile {Q : ℝ} (w : DFIDeltaWeight Q)
    (D : ℕ → ℝ) : Prop where
  positive : ∀ j, 0 < D j
  bound : ∀ j u, ‖iteratedDeriv j w.toFun u‖ ≤
    D j * (Q ^ (j + 1))⁻¹

/-- Every individual delta weight admits a profile.  Uniform DFI
applications must additionally keep this chosen profile fixed while `Q`
varies; this theorem alone deliberately makes no such family claim. -/
theorem DFIDeltaWeight.exists_profile {Q : ℝ} (w : DFIDeltaWeight Q) :
    ∃ D : ℕ → ℝ, DFIDeltaWeightProfile w D := by
  choose D hD hbound using w.derivativeBound
  exact ⟨D, hD, hbound⟩

/-- Finite aggregate of the equation-(9) constants needed up to order
`J`. -/
noncomputable def dfiDeltaFiniteConstant (D : ℕ → ℝ) (J : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (J + 1), D j

theorem DFIDeltaWeightProfile.le_finiteConstant
    {Q : ℝ} {w : DFIDeltaWeight Q} {D : ℕ → ℝ}
    (hD : DFIDeltaWeightProfile w D) {j J : ℕ} (hj : j ≤ J) :
    D j ≤ dfiDeltaFiniteConstant D J := by
  unfold dfiDeltaFiniteConstant
  exact Finset.single_le_sum (fun k _hk ↦ (hD.positive k).le) (by simp [hj])

instance {Q : ℝ} : CoeFun (DFIDeltaWeight Q) (fun _ => ℝ → ℝ) :=
  ⟨DFIDeltaWeight.toFun⟩

theorem DFIDeltaWeight.Q_pos {Q : ℝ} (w : DFIDeltaWeight Q) : 0 < Q :=
  lt_of_lt_of_le zero_lt_one w.one_le_Q

/-- The annular support forces the source weight to vanish close to zero. -/
theorem DFIDeltaWeight.eq_zero_of_abs_lt {Q u : ℝ} (w : DFIDeltaWeight Q)
    (hu : |u| < Q) : w u = 0 := by
  by_contra hne
  have hmem : u ∈ Function.support w.toFun := hne
  exact (not_le_of_gt hu) (w.support_annulus hmem).1

/-- The annular support forces the source weight to vanish beyond `2Q`. -/
theorem DFIDeltaWeight.eq_zero_of_two_mul_lt_abs {Q u : ℝ}
    (w : DFIDeltaWeight Q) (hu : 2 * Q < |u|) : w u = 0 := by
  by_contra hne
  have hmem : u ∈ Function.support w.toFun := hne
  exact (not_le_of_gt hu) (w.support_annulus hmem).2

@[simp]
theorem DFIDeltaWeight.zero {Q : ℝ} (w : DFIDeltaWeight Q) : w 0 = 0 := by
  apply w.eq_zero_of_abs_lt
  simpa using w.Q_pos

/-- A common finite radius containing the `r`-support of both
`w(qr)` and `w(u/(qr))`.  It is deliberately a generous radius; exact
minimality is irrelevant, while its explicit dependence is useful below. -/
noncomputable def dfiDeltaRadius (Q u : ℝ) : ℕ :=
  ⌈2 * Q + |u| / Q⌉₊ + 1

/-- The explicit radius strictly exceeds both support scales used by the
delta kernel. -/
theorem dfiDeltaRadius_spec {Q u : ℝ} :
    2 * Q + |u| / Q < (dfiDeltaRadius Q u : ℝ) := by
  unfold dfiDeltaRadius
  have hceil := Nat.le_ceil (2 * Q + |u| / Q)
  exact lt_of_le_of_lt hceil (by norm_num)

/-- Both weight terms in the delta kernel vanish once the product index
reaches the explicit support radius. -/
theorem dfiDeltaWeight_pair_eq_zero_of_radius_le
    {Q u : ℝ} (w : DFIDeltaWeight Q) (k : ℕ) (hk : 0 < k)
    (hRk : dfiDeltaRadius Q u ≤ k) :
    w (k : ℝ) = 0 ∧ w (u / (k : ℝ)) = 0 := by
  have hrad := dfiDeltaRadius_spec (Q := Q) (u := u)
  have hRk' : (dfiDeltaRadius Q u : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast hRk
  have hsum : 2 * Q + |u| / Q < (k : ℝ) := hrad.trans_le hRk'
  constructor
  · apply w.eq_zero_of_two_mul_lt_abs
    rw [abs_of_nonneg (Nat.cast_nonneg k)]
    nlinarith [div_nonneg (abs_nonneg u) w.Q_pos.le]
  · apply w.eq_zero_of_abs_lt
    have habsk : |(k : ℝ)| = (k : ℝ) := abs_of_nonneg (Nat.cast_nonneg k)
    rw [abs_div, habsk]
    rw [div_lt_iff₀ (Nat.cast_pos.mpr hk)]
    rw [mul_comm Q]
    rw [← div_lt_iff₀ w.Q_pos]
    nlinarith [mul_pos two_pos w.Q_pos]

/-- The DFI kernel
`Δ_q(u)=∑_{r≥1}(w(qr)-w(u/(qr)))/(qr)`, with the exact finite support made
explicit.  Only positive moduli are used by `dfiDeltaExpansion`. -/
noncomputable def dfiDeltaKernel {Q : ℝ} (w : DFIDeltaWeight Q)
    (q : ℕ) (u : ℝ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 (dfiDeltaRadius Q u),
    (w ((q * r : ℕ) : ℝ) - w (u / (q * r : ℕ))) / (q * r : ℕ)

/-- DFI equation (11), in the paper's literal infinite-series form.  The
series is exactly the finite implementation `dfiDeltaKernel`: annular support
kills every term outside the explicit radius. -/
theorem dfiDeltaKernel_eq_tsum {Q : ℝ} (w : DFIDeltaWeight Q)
    (q : ℕ) (hq : 0 < q) (u : ℝ) :
    dfiDeltaKernel w q u =
      ∑' r : ℕ,
        (w ((q * r : ℕ) : ℝ) - w (u / (q * r : ℕ))) / (q * r : ℕ) := by
  rw [dfiDeltaKernel, tsum_eq_sum (s := Finset.Icc 1 (dfiDeltaRadius Q u))]
  intro r hr
  simp only [Finset.mem_Icc, not_and_or, not_le] at hr
  rcases hr with hr0 | hrR
  · have hrz : r = 0 := by omega
    simp [hrz]
  · have hqr : dfiDeltaRadius Q u ≤ q * r := by
      exact le_trans (Nat.le_of_lt hrR) (Nat.le_mul_of_pos_left r hq)
    have hqrpos : 0 < q * r := Nat.mul_pos hq (lt_of_le_of_lt (by omega) hrR)
    obtain ⟨hfirst, hsecond⟩ :=
      dfiDeltaWeight_pair_eq_zero_of_radius_le w (q * r) hqrpos hqr
    rw [hfirst, hsecond]
    simp

/-- Ramanujan's complete reduced-residue sum at an integer frequency. -/
noncomputable def ramanujanSumInt (q : ℕ) (n : ℤ) : ℂ :=
  if hq : q = 0 then 0
  else
    letI : NeZero q := ⟨hq⟩
    ∑ d ∈ Finset.range q with Nat.Coprime d q,
      ZMod.stdAddChar ((n : ZMod q) * (d : ZMod q))

@[simp]
theorem ramanujanSumInt_zero (q : ℕ) :
    ramanujanSumInt q 0 = (Nat.totient q : ℂ) := by
  by_cases hq : q = 0
  · simp [ramanujanSumInt, hq]
  · letI : NeZero q := ⟨hq⟩
    simp only [ramanujanSumInt, hq, ↓reduceDIte, Int.cast_zero, zero_mul,
      sum_const, nsmul_eq_mul]
    norm_cast
    simpa [Nat.coprime_comm] using Nat.totient_eq_card_coprime q

/-- Positive reduced residue classes, represented by the literal range used
in the complete exponential sum. -/
def dfiCoprimeResidues (q : ℕ) : Finset ℕ :=
  (Finset.range q).filter fun d => Nat.Coprime d q

/-- Raising the standard primitive `q`-th root to reduced residue powers is
the bijection between reduced residues and all primitive `q`-th roots. -/
noncomputable def dfiCoprimeResiduesEquivPrimitiveRoots (q : ℕ) [NeZero q] :
    ↥(dfiCoprimeResidues q) ≃ ↥(primitiveRoots q ℂ) := by
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / q)
  have hζ : IsPrimitiveRoot ζ q := Complex.isPrimitiveRoot_exp q NeZero.out
  let F : ↥(dfiCoprimeResidues q) → ↥(primitiveRoots q ℂ) := fun d =>
    ⟨ζ ^ d.1, by
      rw [mem_primitiveRoots (Nat.pos_of_ne_zero NeZero.out)]
      exact hζ.pow_of_coprime d.1 (Finset.mem_filter.mp d.2).2⟩
  apply Equiv.ofBijective F
  constructor
  · intro d e hde
    apply Subtype.ext
    apply hζ.pow_inj
    · exact Finset.mem_range.mp (Finset.mem_filter.mp d.2).1
    · exact Finset.mem_range.mp (Finset.mem_filter.mp e.2).1
    · exact congrArg Subtype.val hde
  · intro ξ
    have hξ := ξ.2
    rw [mem_primitiveRoots (Nat.pos_of_ne_zero NeZero.out),
      hζ.isPrimitiveRoot_iff] at hξ
    obtain ⟨i, hi, hcop, hpow⟩ := hξ
    let d : ↥(dfiCoprimeResidues q) :=
      ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, hcop⟩⟩
    refine ⟨d, ?_⟩
    apply Subtype.ext
    exact hpow

@[simp]
theorem dfiCoprimeResiduesEquivPrimitiveRoots_apply
    (q : ℕ) [NeZero q] (d : ↥(dfiCoprimeResidues q)) :
    ((dfiCoprimeResiduesEquivPrimitiveRoots q d : ↥(primitiveRoots q ℂ)) : ℂ) =
      Complex.exp (2 * Real.pi * Complex.I / q) ^ d.1 := by
  rfl

/-- The complete reduced-residue exponential sum is the power sum over all
primitive roots of unity of the same order. -/
theorem ramanujanSumInt_ofNat_eq_sum_primitiveRoots
    (q n : ℕ) [NeZero q] :
    ramanujanSumInt q n = ∑ ζ ∈ primitiveRoots q ℂ, ζ ^ n := by
  let ζq : ℂ := Complex.exp (2 * Real.pi * Complex.I / q)
  simp only [ramanujanSumInt, NeZero.ne q, ↓reduceDIte]
  simp only [Int.cast_natCast]
  conv_lhs => rw [← Finset.sum_attach]
  conv_rhs => rw [← Finset.sum_attach]
  simp only [Finset.attach_eq_univ]
  refine Fintype.sum_equiv (dfiCoprimeResiduesEquivPrimitiveRoots q)
    (fun d : ↥(dfiCoprimeResidues q) =>
      ZMod.stdAddChar (((n : ℕ) : ZMod q) * (d.1 : ZMod q)))
    (fun ξ : ↥(primitiveRoots q ℂ) => (ξ.1 : ℂ) ^ n) (fun d => ?_)
  change ZMod.stdAddChar (((n : ℕ) : ZMod q) * (d.1 : ZMod q)) =
    ((dfiCoprimeResiduesEquivPrimitiveRoots q d : ℂ) ^ n)
  rw [dfiCoprimeResiduesEquivPrimitiveRoots_apply]
  rw [← Nat.cast_mul]
  rw [show ((n * d.1 : ℕ) : ZMod q) = ((n * d.1 : ℤ) : ZMod q) by simp]
  rw [ZMod.stdAddChar_coe]
  simp only [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The power sum over all `k`-th roots of unity is the exact additive
character orthogonality value. -/
theorem sum_nthRootsFinset_pow (k n : ℕ) (hk : 0 < k) :
    ∑ ζ ∈ Polynomial.nthRootsFinset k (1 : ℂ), ζ ^ n =
      if k ∣ n then (k : ℂ) else 0 := by
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / k)
  have hζ : IsPrimitiveRoot ζ k := Complex.isPrimitiveRoot_exp k hk.ne'
  have hroots : Polynomial.nthRootsFinset k (1 : ℂ) =
      (Finset.range k).image (fun i => ζ ^ i) := by
    rw [Polynomial.nthRootsFinset_def,
      hζ.nthRoots_eq (α := (1 : ℂ)) (by simp)]
    rw [Multiset.toFinset_map]
    simp
  rw [hroots, Finset.sum_image]
  · have hsum :
        ∑ i ∈ Finset.range k, (ζ ^ i) ^ n =
          ∑ i ∈ Finset.range k, (ζ ^ n) ^ i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← pow_mul, ← pow_mul, mul_comm i n]
    rw [hsum]
    by_cases hkn : k ∣ n
    · obtain ⟨m, rfl⟩ := hkn
      simp [pow_mul, hζ.pow_eq_one]
    · have hpow_ne : ζ ^ n ≠ 1 := by
        intro h
        exact hkn ((hζ.pow_eq_one_iff_dvd n).mp h)
      rw [geom_sum_eq hpow_ne]
      rw [← pow_mul, mul_comm n k, pow_mul, hζ.pow_eq_one, one_pow,
        sub_self, zero_div, if_neg hkn]
  · intro a ha b hb hab
    exact hζ.pow_inj (Finset.mem_range.mp ha) (Finset.mem_range.mp hb) hab

/-- Summing the complete reduced-residue sums over all divisors of `k`
recovers the full roots-of-unity orthogonality value. -/
theorem sum_divisors_ramanujanSumInt_ofNat (k n : ℕ) (hk : 0 < k) :
    ∑ q ∈ k.divisors, ramanujanSumInt q n =
      if k ∣ n then (k : ℂ) else 0 := by
  have hdis : Set.PairwiseDisjoint (↑k.divisors)
      (fun q : ℕ => primitiveRoots q ℂ) := by
    intro q _ r _ hqr
    exact IsPrimitiveRoot.disjoint hqr
  calc
    ∑ q ∈ k.divisors, ramanujanSumInt q n =
        ∑ q ∈ k.divisors, ∑ ζ ∈ primitiveRoots q ℂ, ζ ^ n := by
          apply Finset.sum_congr rfl
          intro q hq
          letI : NeZero q := ⟨(Nat.pos_of_mem_divisors hq).ne'⟩
          exact ramanujanSumInt_ofNat_eq_sum_primitiveRoots q n
    _ = ∑ ζ ∈ k.divisors.biUnion (fun q => primitiveRoots q ℂ), ζ ^ n := by
          rw [Finset.sum_biUnion hdis]
    _ = ∑ ζ ∈ Polynomial.nthRootsFinset k (1 : ℂ), ζ ^ n := by
          rw [IsPrimitiveRoot.nthRoots_one_eq_biUnion_primitiveRoots]
    _ = if k ∣ n then (k : ℂ) else 0 := sum_nthRootsFinset_pow k n hk

/-- Negating the integer frequency conjugates the complete reduced-residue
sum. -/
theorem ramanujanSumInt_neg (q : ℕ) (n : ℤ) :
    ramanujanSumInt q (-n) = star (ramanujanSumInt q n) := by
  by_cases hq : q = 0
  · simp [ramanujanSumInt, hq]
  · letI : NeZero q := ⟨hq⟩
    simp only [ramanujanSumInt, hq, ↓reduceDIte, Int.cast_neg, neg_mul,
      AddChar.map_neg_eq_conj]
    change _ = (starRingEnd ℂ) _
    rw [map_sum]

/-- Integer-frequency form of Ramanujan orthogonality, expressed using
`natAbs` so that it applies uniformly to positive and negative shifts. -/
theorem sum_divisors_ramanujanSumInt (k : ℕ) (n : ℤ) (hk : 0 < k) :
    ∑ q ∈ k.divisors, ramanujanSumInt q n =
      if k ∣ n.natAbs then (k : ℂ) else 0 := by
  cases n with
  | ofNat m =>
      simpa using sum_divisors_ramanujanSumInt_ofNat k m hk
  | negSucc m =>
      have hneg : Int.negSucc m = -((m + 1 : ℕ) : ℤ) := by omega
      have habs : (-((m + 1 : ℕ) : ℤ)).natAbs = m + 1 := by omega
      rw [hneg]
      simp_rw [ramanujanSumInt_neg]
      change ∑ q ∈ k.divisors,
        (starRingEnd ℂ) (ramanujanSumInt q (m + 1 : ℕ)) = _
      rw [← map_sum]
      rw [sum_divisors_ramanujanSumInt_ofNat k (m + 1) hk]
      rw [habs]
      split_ifs <;> simp

/-- Positive index pairs below the support radius partition exactly into the
divisor antidiagonals of their products. -/
theorem dfiProductFilter_eq_biUnion_divisorsAntidiagonal (R : ℕ) :
    ((Finset.Icc 1 R) ×ˢ (Finset.Icc 1 R)).filter
        (fun p => p.1 * p.2 < R) =
      (Finset.Ico 1 R).biUnion Nat.divisorsAntidiagonal := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
    Finset.mem_Ico, Finset.mem_biUnion, Nat.mem_divisorsAntidiagonal]
  constructor
  · rintro ⟨⟨⟨ha1, haR⟩, ⟨hb1, hbR⟩⟩, habR⟩
    exact ⟨p.1 * p.2, ⟨Nat.mul_pos ha1 hb1, habR⟩, rfl,
      mul_ne_zero (Nat.ne_of_gt ha1) (Nat.ne_of_gt hb1)⟩
  · rintro ⟨k, ⟨hk1, hkR⟩, hp, hk0⟩
    have ha1 : 1 ≤ p.1 := by
      by_contra h
      have hp1 : p.1 = 0 := Nat.eq_zero_of_not_pos h
      have hz : p.1 * p.2 = 0 := by simp [hp1]
      rw [hz] at hp
      omega
    have hb1 : 1 ≤ p.2 := by
      by_contra h
      have hp2 : p.2 = 0 := Nat.eq_zero_of_not_pos h
      have hz : p.1 * p.2 = 0 := by simp [hp2]
      rw [hz] at hp
      omega
    have haR : p.1 ≤ R := by
      calc p.1 ≤ p.1 * p.2 := Nat.le_mul_of_pos_right p.1 hb1
        _ = k := hp
        _ ≤ R := hkR.le
    have hbR : p.2 ≤ R := by
      calc p.2 ≤ p.1 * p.2 := Nat.le_mul_of_pos_left p.2 ha1
        _ = k := hp
        _ ≤ R := hkR.le
    exact ⟨⟨⟨ha1, haR⟩, ⟨hb1, hbR⟩⟩, hp ▸ hkR⟩

/-- Different product fibers have disjoint divisor antidiagonals. -/
theorem dfiDivisorsAntidiagonal_pairwiseDisjoint (R : ℕ) :
    Set.PairwiseDisjoint (↑(Finset.Ico 1 R)) Nat.divisorsAntidiagonal := by
  intro k _ l _ hkl
  change Disjoint (Nat.divisorsAntidiagonal k) (Nat.divisorsAntidiagonal l)
  rw [Finset.disjoint_left]
  intro p hpk hpl
  have hpk' := (Nat.mem_divisorsAntidiagonal.mp hpk).1
  have hpl' := (Nat.mem_divisorsAntidiagonal.mp hpl).1
  exact hkl (hpk'.symm.trans hpl')

/-- A finite double sum supported on products below `R` can be regrouped
exactly by product and then by divisor antidiagonal. -/
theorem dfiSum_product_eq_sum_divisorsAntidiagonal
    {M : Type*} [AddCommMonoid M] (R : ℕ) (F : ℕ × ℕ → M)
    (hzero : ∀ p ∈ (Finset.Icc 1 R) ×ˢ (Finset.Icc 1 R),
      ¬p.1 * p.2 < R → F p = 0) :
    ∑ q ∈ Finset.Icc 1 R, ∑ r ∈ Finset.Icc 1 R, F (q, r) =
      ∑ k ∈ Finset.Ico 1 R, ∑ p ∈ k.divisorsAntidiagonal, F p := by
  rw [← Finset.sum_product]
  calc
    ∑ p ∈ (Finset.Icc 1 R) ×ˢ (Finset.Icc 1 R), F p =
        ∑ p ∈ ((Finset.Icc 1 R) ×ˢ (Finset.Icc 1 R)).filter
          (fun p => p.1 * p.2 < R), F p := by
            symm
            apply Finset.sum_subset (Finset.filter_subset _ _)
            intro p hp hpn
            exact hzero p hp (fun hlt => hpn (Finset.mem_filter.mpr ⟨hp, hlt⟩))
    _ = ∑ p ∈ (Finset.Ico 1 R).biUnion Nat.divisorsAntidiagonal, F p := by
          rw [dfiProductFilter_eq_biUnion_divisorsAntidiagonal]
    _ = ∑ k ∈ Finset.Ico 1 R, ∑ p ∈ k.divisorsAntidiagonal, F p := by
          rw [Finset.sum_biUnion (dfiDivisorsAntidiagonal_pairwiseDisjoint R)]

/-- The divisor-frequency function `d ↦ d * 1_{d∣N}`.  Its convolution with
Möbius is the arithmetic form of the Ramanujan sum. -/
noncomputable def dfiDivisorFrequency (N : ℕ) : ArithmeticFunction ℂ :=
  ⟨fun d => if d = 0 then 0 else if d ∣ N then (d : ℂ) else 0, by simp⟩

/-- The arithmetic Ramanujan function
`q ↦ ∑_{d∣gcd(q,N)} d μ(q/d)`, represented as a Dirichlet convolution. -/
noncomputable def dfiRamanujanArithmetic (N : ℕ) : ArithmeticFunction ℂ :=
  dfiDivisorFrequency N * (ArithmeticFunction.moebius : ArithmeticFunction ℂ)

/-- Summing the arithmetic Ramanujan function over the divisors of `k`
recovers the full additive-character orthogonality value.  This is the
convolution identity underlying DFI equation (10). -/
theorem sum_divisors_dfiRamanujanArithmetic (N k : ℕ) (hk : 0 < k) :
    ∑ q ∈ k.divisors, dfiRamanujanArithmetic N q =
      if k ∣ N then (k : ℂ) else 0 := by
  have hconv :
      (ArithmeticFunction.zeta : ArithmeticFunction ℂ) *
          dfiRamanujanArithmetic N = dfiDivisorFrequency N := by
    unfold dfiRamanujanArithmetic
    calc
      (ArithmeticFunction.zeta : ArithmeticFunction ℂ) *
            (dfiDivisorFrequency N *
              (ArithmeticFunction.moebius : ArithmeticFunction ℂ)) =
          ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) *
              (ArithmeticFunction.moebius : ArithmeticFunction ℂ)) *
            dfiDivisorFrequency N := by ac_rfl
      _ = dfiDivisorFrequency N := by
        rw [ArithmeticFunction.coe_zeta_mul_coe_moebius, one_mul]
  rw [← ArithmeticFunction.coe_zeta_mul_apply, hconv]
  simp [dfiDivisorFrequency, hk.ne']

/-- The right side of DFI equation (10).  The source writes an infinite sum;
annular support bounds every nonzero modulus by the displayed finite radius. -/
noncomputable def dfiDeltaExpansion {Q : ℝ} (w : DFIDeltaWeight Q)
    (n : ℤ) : ℂ :=
  ∑ q ∈ Finset.Icc 1 (dfiDeltaRadius Q n),
    (dfiDeltaKernel w q n : ℂ) * ramanujanSumInt q n

/-- The individual `(q,r)` summand before the DFI delta sum is regrouped by
the product `k = q r`. -/
noncomputable def dfiDeltaPairSummand {Q : ℝ} (w : DFIDeltaWeight Q)
    (n : ℤ) (p : ℕ × ℕ) : ℂ :=
  (((w ((p.1 * p.2 : ℕ) : ℝ) -
      w ((n : ℝ) / (p.1 * p.2 : ℕ))) /
        (p.1 * p.2 : ℕ) : ℝ) : ℂ) * ramanujanSumInt p.1 n

/-- Expanding every kernel makes the delta expression an exact finite double
sum over positive `q` and `r`. -/
theorem dfiDeltaExpansion_eq_pair_sum {Q : ℝ} (w : DFIDeltaWeight Q)
    (n : ℤ) :
    dfiDeltaExpansion w n =
      ∑ q ∈ Finset.Icc 1 (dfiDeltaRadius Q n),
        ∑ r ∈ Finset.Icc 1 (dfiDeltaRadius Q n),
          dfiDeltaPairSummand w n (q, r) := by
  unfold dfiDeltaExpansion dfiDeltaKernel dfiDeltaPairSummand
  apply Finset.sum_congr rfl
  intro q _
  push_cast
  rw [Finset.sum_mul]

/-- Regrouping the exact double sum by `k = q r` produces the divisor sum of
Ramanujan sums that is evaluated by additive-character orthogonality. -/
theorem dfiDeltaExpansion_eq_product_fibers {Q : ℝ} (w : DFIDeltaWeight Q)
    (n : ℤ) :
    dfiDeltaExpansion w n =
      ∑ k ∈ Finset.Ico 1 (dfiDeltaRadius Q n),
        (((w (k : ℝ) - w ((n : ℝ) / k)) / k : ℝ) : ℂ) *
          ∑ q ∈ k.divisors, ramanujanSumInt q n := by
  rw [dfiDeltaExpansion_eq_pair_sum]
  rw [dfiSum_product_eq_sum_divisorsAntidiagonal]
  · apply Finset.sum_congr rfl
    intro k _
    rw [← Nat.map_div_right_divisors]
    rw [Finset.sum_map, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    have hprod : q * (k / q) = k := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hq)
    change dfiDeltaPairSummand w n (q, k / q) =
      (((w (k : ℝ) - w ((n : ℝ) / k)) / k : ℝ) : ℂ) *
        ramanujanSumInt q n
    unfold dfiDeltaPairSummand
    rw [hprod]
  · intro p hp hnot
    have hpmem := Finset.mem_product.mp hp
    have hp1 : 0 < p.1 := (Finset.mem_Icc.mp hpmem.1).1
    have hp2 : 0 < p.2 := (Finset.mem_Icc.mp hpmem.2).1
    have hR : dfiDeltaRadius Q n ≤ p.1 * p.2 := Nat.le_of_not_gt hnot
    have hzero := dfiDeltaWeight_pair_eq_zero_of_radius_le w (p.1 * p.2)
      (Nat.mul_pos hp1 hp2) hR
    unfold dfiDeltaPairSummand
    rw [hzero.1, hzero.2, sub_self, zero_div, ofReal_zero, zero_mul]

/-- Ramanujan orthogonality removes every product fiber except divisors of
the integer shift.  The surviving factor `k` cancels its delta-kernel
denominator exactly. -/
theorem dfiDeltaExpansion_eq_divisor_filter {Q : ℝ} (w : DFIDeltaWeight Q)
    (n : ℤ) :
    dfiDeltaExpansion w n =
      ∑ k ∈ Finset.Ico 1 (dfiDeltaRadius Q n),
        if k ∣ n.natAbs then
          ((w (k : ℝ) - w ((n : ℝ) / k) : ℝ) : ℂ)
        else 0 := by
  rw [dfiDeltaExpansion_eq_product_fibers]
  apply Finset.sum_congr rfl
  intro k hk
  have hkpos : 0 < k := (Finset.mem_Ico.mp hk).1
  rw [sum_divisors_ramanujanSumInt k n hkpos]
  by_cases hkn : k ∣ n.natAbs
  · rw [if_pos hkn, if_pos hkn]
    push_cast
    exact div_mul_cancel₀ _ (by exact_mod_cast hkpos.ne')
  · rw [if_neg hkn, if_neg hkn, mul_zero]

/-- At zero shift, the finite positive-index interval contains the entire
support of the normalized DFI cutoff. -/
theorem DFIDeltaWeight.sum_Ico_radius_zero {Q : ℝ} (w : DFIDeltaWeight Q) :
    ∑ k ∈ Finset.Ico 1 (dfiDeltaRadius Q 0), w (k : ℝ) = 1 := by
  let R := dfiDeltaRadius Q 0
  have hR : 0 < R := by
    dsimp [R, dfiDeltaRadius]
    omega
  have htail : ∀ r : ℕ, r ∉ Finset.range R → w ((r + 1 : ℕ) : ℝ) = 0 := by
    intro r hr
    have hRr : R ≤ r := by simpa using hr
    exact (dfiDeltaWeight_pair_eq_zero_of_radius_le w (r + 1)
      (Nat.succ_pos r) (hRr.trans (Nat.le_succ r))).1
  have hfinite : ∑ r ∈ Finset.range R, w ((r + 1 : ℕ) : ℝ) = 1 := by
    calc
      ∑ r ∈ Finset.range R, w ((r + 1 : ℕ) : ℝ) =
          ∑' r : ℕ, w ((r + 1 : ℕ) : ℝ) := (tsum_eq_sum htail).symm
      _ = 1 := w.normalized
  have hlast : w (R : ℝ) = 0 :=
    (dfiDeltaWeight_pair_eq_zero_of_radius_le w R hR le_rfl).1
  rw [Finset.sum_Ico_eq_sum_range]
  have hpred : R - 1 + 1 = R := Nat.sub_add_cancel hR
  rw [← hpred, Finset.sum_range_succ] at hfinite
  simp only [hpred, hlast, add_zero] at hfinite
  simpa [Nat.add_comm] using hfinite

/-- For a positive shift, the surviving divisor terms cancel under the
involution `k ↦ N / k`.  Terms beyond the explicit radius vanish by support. -/
theorem DFIDeltaWeight.sum_Ico_divisor_difference_eq_zero
    {Q : ℝ} (w : DFIDeltaWeight Q) (N : ℕ) (hN : 0 < N) :
    (∑ k ∈ Finset.Ico 1 (dfiDeltaRadius Q N),
        if k ∣ N then w (k : ℝ) - w ((N : ℝ) / k) else 0) = 0 := by
  rw [← Finset.sum_filter (s := Finset.Ico 1 (dfiDeltaRadius Q N))
    (fun k => k ∣ N) (fun k => w (k : ℝ) - w ((N : ℝ) / k))]
  let S := (Finset.Ico 1 (dfiDeltaRadius Q N)).filter (fun k => k ∣ N)
  have hsubset : S ⊆ N.divisors := by
    intro k hk
    have hk' := Finset.mem_filter.mp hk
    exact Nat.mem_divisors.mpr ⟨hk'.2, hN.ne'⟩
  have hextend :
      ∑ k ∈ S, (w (k : ℝ) - w ((N : ℝ) / k)) =
        ∑ k ∈ N.divisors, (w (k : ℝ) - w ((N : ℝ) / k)) := by
    apply Finset.sum_subset hsubset
    intro k hkdiv hknot
    have hkpos : 0 < k := Nat.pos_of_mem_divisors hkdiv
    have hkR : dfiDeltaRadius Q N ≤ k := by
      have hnotIco : k ∉ Finset.Ico 1 (dfiDeltaRadius Q N) := by
        intro hkIco
        exact hknot (Finset.mem_filter.mpr ⟨hkIco, Nat.dvd_of_mem_divisors hkdiv⟩)
      have := Finset.mem_Ico.not.mp hnotIco
      omega
    have hz := dfiDeltaWeight_pair_eq_zero_of_radius_le w k hkpos hkR
    rw [hz.1, hz.2, sub_self]
  change ∑ k ∈ S, (w (k : ℝ) - w ((N : ℝ) / k)) = 0
  rw [hextend]
  calc
    ∑ k ∈ N.divisors, (w (k : ℝ) - w ((N : ℝ) / k)) =
        ∑ k ∈ N.divisors, (w (k : ℝ) - w ((N / k : ℕ) : ℝ)) := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [Nat.cast_div_charZero (K := ℝ) (Nat.dvd_of_mem_divisors hk)]
    _ = (∑ k ∈ N.divisors, w (k : ℝ)) -
        ∑ k ∈ N.divisors, w ((N / k : ℕ) : ℝ) := by
          rw [Finset.sum_sub_distrib]
    _ = 0 := by
      rw [Nat.sum_div_divisors N (fun k => w (k : ℝ)), sub_self]

/-- Signed-integer form of the divisor involution cancellation.  Evenness of
the source cutoff removes the sign of a negative shift. -/
theorem DFIDeltaWeight.sum_Ico_int_divisor_difference_eq_zero
    {Q : ℝ} (w : DFIDeltaWeight Q) (n : ℤ) (hn : n ≠ 0) :
    (∑ k ∈ Finset.Ico 1 (dfiDeltaRadius Q n),
        if k ∣ n.natAbs then w (k : ℝ) - w ((n : ℝ) / k) else 0) = 0 := by
  cases n with
  | ofNat N =>
      have hN : 0 < N := Nat.pos_of_ne_zero (by simpa using hn)
      simpa using w.sum_Ico_divisor_difference_eq_zero N hN
  | negSucc m =>
      let N := m + 1
      have hN : 0 < N := Nat.succ_pos m
      have hnval : ((Int.negSucc m : ℤ) : ℝ) = -(N : ℝ) := by
        dsimp [N]
        push_cast
        ring
      have hrad : dfiDeltaRadius Q (Int.negSucc m : ℤ) = dfiDeltaRadius Q N := by
        unfold dfiDeltaRadius
        rw [hnval, abs_neg]
      rw [hrad]
      convert w.sum_Ico_divisor_difference_eq_zero N hN using 1
      apply Finset.sum_congr rfl
      intro k _
      have habs : (Int.negSucc m).natAbs = N := by
        dsimp [N]
      rw [habs]
      by_cases hkN : k ∣ N
      · rw [if_pos hkN, if_pos hkN, hnval, neg_div]
        rw [w.even]
      · rw [if_neg hkN, if_neg hkN]

/-- The exact target asserted by DFI equation (10).  This definition is used
only to name the source equality while its proof is developed from equations
(9)--(19); it is not itself evidence for that equality. -/
def DFIDeltaIdentity {Q : ℝ} (w : DFIDeltaWeight Q) : Prop :=
  ∀ n : ℤ, dfiDeltaExpansion w n = if n = 0 then 1 else 0

/-- DFI equation (10): the delta symbol detects exactly the zero integer.
The proof expands the kernel, groups by the product `qr`, applies exact
Ramanujan orthogonality, and cancels the surviving divisor terms. -/
theorem dfiDeltaIdentity {Q : ℝ} (w : DFIDeltaWeight Q) :
    DFIDeltaIdentity w := by
  intro n
  rw [dfiDeltaExpansion_eq_divisor_filter]
  by_cases hn : n = 0
  · subst n
    simp only [Int.natAbs_zero, dvd_zero, if_true, Int.cast_zero, zero_div,
      w.zero, sub_zero]
    rw [← ofReal_sum]
    rw [w.sum_Ico_radius_zero, ofReal_one]
  · rw [if_neg hn]
    have hcancel := w.sum_Ico_int_divisor_difference_eq_zero n hn
    have hc := congrArg Complex.ofReal hcancel
    rw [ofReal_zero] at hc
    calc
      ∑ k ∈ Finset.Ico 1 (dfiDeltaRadius Q n),
          (if k ∣ n.natAbs then
            ((w (k : ℝ) - w ((n : ℝ) / k) : ℝ) : ℂ) else 0) =
          Complex.ofReal (∑ k ∈ Finset.Ico 1 (dfiDeltaRadius Q n),
            if k ∣ n.natAbs then w (k : ℝ) - w ((n : ℝ) / k) else 0) := by
              symm
              calc
                Complex.ofReal (∑ k ∈ Finset.Ico 1 (dfiDeltaRadius Q n),
                    if k ∣ n.natAbs then
                      w (k : ℝ) - w ((n : ℝ) / k) else 0) =
                    ∑ k ∈ Finset.Ico 1 (dfiDeltaRadius Q n),
                      Complex.ofReal (if k ∣ n.natAbs then
                        w (k : ℝ) - w ((n : ℝ) / k) else 0) := ofReal_sum _ _
                _ = _ := by
                  apply Finset.sum_congr rfl
                  intro k _
                  split_ifs <;> simp
      _ = 0 := hc

end RiemannZeta.GuthMaynard
