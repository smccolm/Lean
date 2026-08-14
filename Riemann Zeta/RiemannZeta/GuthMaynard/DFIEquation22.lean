import RiemannZeta.GuthMaynard.DFIEquation21
import RiemannZeta.GuthMaynard.DFIDelta

open Complex Finset Set
open scoped BigOperators ContDiff Topology
open Classical

namespace RiemannZeta.GuthMaynard

/-!
# DFI equation (22): exact finite delta-symbol insertion

This file carries out the step between equations (21) and (22) of
Duke--Friedlander--Iwaniec.  The modulus restriction is represented by the
literal source condition `1 ≤ q` and `(q : ℝ) < 2Q`.
-/

/-- Continuity forces the annular DFI weight to vanish at the outer boundary
as well as beyond it. -/
theorem DFIDeltaWeight.eq_zero_of_two_mul_le_abs
    {Q u : ℝ} (w : DFIDeltaWeight Q) (hu : 2 * Q ≤ |u|) : w u = 0 := by
  rcases hu.eq_or_lt with heq | hlt
  · by_contra hne
    have hopen : IsOpen (Function.support w.toFun) :=
      isOpen_compl_singleton.preimage w.smooth.continuous
    have hnhds : Function.support w.toFun ∈ 𝓝 u := hopen.mem_nhds hne
    rw [Metric.mem_nhds_iff] at hnhds
    obtain ⟨ε, hε, hball⟩ := hnhds
    by_cases hu0 : 0 ≤ u
    · have habsu : |u| = u := abs_of_nonneg hu0
      have huval : u = 2 * Q := by linarith
      let v := u + ε / 2
      have hvball : v ∈ Metric.ball u ε := by
        rw [Metric.mem_ball, Real.dist_eq]
        dsimp [v]
        rw [show u + ε / 2 - u = ε / 2 by ring,
          abs_of_pos (by positivity : 0 < ε / 2)]
        linarith
      have hvne : w v ≠ 0 := hball hvball
      have hvpos : 0 < v := by dsimp [v]; nlinarith [w.Q_pos]
      have hvabs : 2 * Q < |v| := by
        rw [abs_of_pos hvpos]
        dsimp [v]
        linarith
      exact hvne (w.eq_zero_of_two_mul_lt_abs hvabs)
    · have huNeg : u < 0 := lt_of_not_ge hu0
      have habsu : |u| = -u := abs_of_neg huNeg
      have huval : u = -(2 * Q) := by linarith
      let v := u - ε / 2
      have hvball : v ∈ Metric.ball u ε := by
        rw [Metric.mem_ball, Real.dist_eq]
        dsimp [v]
        rw [abs_of_nonpos (by linarith : u - ε / 2 - u ≤ 0)]
        linarith
      have hvne : w v ≠ 0 := hball hvball
      have hvneg : v < 0 := by dsimp [v]; linarith
      have hvabs : 2 * Q < |v| := by
        rw [abs_of_neg hvneg]
        dsimp [v]
        linarith
      exact hvne (w.eq_zero_of_two_mul_lt_abs hvabs)
  · exact w.eq_zero_of_two_mul_lt_abs hlt

/-- If the shift has source size at most `Q²`, every modulus at least `2Q`
has zero delta kernel.  This is the truncation assertion used in (22). -/
theorem dfiDeltaKernel_eq_zero_of_two_mul_le
    {Q u : ℝ} (w : DFIDeltaWeight Q) (hu : |u| ≤ Q ^ 2)
    (q : ℕ) (hq : 2 * Q ≤ q) : dfiDeltaKernel w q u = 0 := by
  unfold dfiDeltaKernel
  apply Finset.sum_eq_zero
  intro r hr
  have hrpos : 0 < r := (Finset.mem_Icc.mp hr).1
  have hqpos : 0 < q := by
    have : 0 < (q : ℝ) := (mul_pos two_pos w.Q_pos).trans_le hq
    exact_mod_cast this
  have hqr : 2 * Q ≤ (q * r : ℕ) := by
    have hqle : q ≤ q * r := Nat.le_mul_of_pos_right q hrpos
    exact hq.trans (by exact_mod_cast hqle)
  have hfirst : w ((q * r : ℕ) : ℝ) = 0 := by
    apply w.eq_zero_of_two_mul_le_abs
    rw [abs_of_nonneg (by positivity : 0 ≤ ((q * r : ℕ) : ℝ))]
    exact hqr
  have hqrpos : 0 < ((q * r : ℕ) : ℝ) := by positivity
  have hsecond : w (u / (q * r : ℕ)) = 0 := by
    apply w.eq_zero_of_abs_lt
    rw [abs_div, abs_of_pos hqrpos]
    apply (div_lt_iff₀ hqrpos).2
    have hQ2lt : Q ^ 2 < Q * ((q * r : ℕ) : ℝ) := by
      have hstrict : 2 * Q ^ 2 ≤ Q * ((q * r : ℕ) : ℝ) := by
        calc
          2 * Q ^ 2 = Q * (2 * Q) := by ring
          _ ≤ Q * ((q * r : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_left hqr w.Q_pos.le
      have hQsq : 0 < Q ^ 2 := sq_pos_of_pos w.Q_pos
      nlinarith
    exact hu.trans_lt hQ2lt
  rw [hfirst, hsecond, sub_self, zero_div]

/-- The literal finite set `1 ≤ q < 2Q` in DFI equation (22). -/
noncomputable def dfiEquation22Moduli (Q : ℝ) : Finset ℕ :=
  (Finset.Icc 1 ⌈2 * Q⌉₊).filter fun q => (q : ℝ) < 2 * Q

theorem mem_dfiEquation22Moduli_iff {Q : ℝ} (q : ℕ) :
    q ∈ dfiEquation22Moduli Q ↔ 0 < q ∧ (q : ℝ) < 2 * Q := by
  simp only [dfiEquation22Moduli, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hq, _⟩, hlt⟩
    exact ⟨by omega, hlt⟩
  · rintro ⟨hq, hlt⟩
    refine ⟨⟨by omega, ?_⟩, hlt⟩
    exact_mod_cast (Nat.le_ceil (2 * Q)).trans' hlt.le

/-- The source modulus set is the ordinary initial interval
`[1, ceil(2Q))`.  This form is used to split the infinite equation-(27)
Ramanujan series exactly at the delta-symbol cutoff. -/
theorem dfiEquation22Moduli_eq_Ico (Q : ℝ) :
    dfiEquation22Moduli Q = Finset.Ico 1 ⌈2 * Q⌉₊ := by
  ext q
  rw [mem_dfiEquation22Moduli_iff]
  simp only [Finset.mem_Ico]
  rw [← Nat.lt_ceil]
  omega

/-- The delta expansion is a `q`-series with finite support even before the
source-size truncation. -/
theorem dfiDeltaExpansion_eq_tsum_moduli
    {Q : ℝ} (w : DFIDeltaWeight Q) (u : ℤ) :
    dfiDeltaExpansion w u =
      ∑' q : ℕ, (dfiDeltaKernel w q u : ℂ) * ramanujanSumInt q u := by
  rw [dfiDeltaExpansion, tsum_eq_sum (s := Finset.Icc 1 (dfiDeltaRadius Q u))]
  intro q hq
  by_cases hq0 : q = 0
  · simp [hq0, ramanujanSumInt]
  have hqpos : 0 < q := Nat.pos_of_ne_zero hq0
  have hqR : dfiDeltaRadius Q u ≤ q := by
    have hnmem := Finset.mem_Icc.not.mp hq
    omega
  have hkernel : dfiDeltaKernel w q u = 0 := by
    unfold dfiDeltaKernel
    apply Finset.sum_eq_zero
    intro r hr
    have hrpos : 0 < r := (Finset.mem_Icc.mp hr).1
    have hqrR : dfiDeltaRadius Q u ≤ q * r :=
      hqR.trans (Nat.le_mul_of_pos_right q hrpos)
    obtain ⟨h₁, h₂⟩ := dfiDeltaWeight_pair_eq_zero_of_radius_le
      w (q * r) (Nat.mul_pos hqpos hrpos) hqrR
    rw [h₁, h₂, sub_self, zero_div]
  simp [hkernel]

/-- Under `|u| ≤ Q²`, equation (10) truncates exactly to the moduli in
equation (22). -/
theorem dfiDeltaIdentity_short_moduli
    {Q : ℝ} (w : DFIDeltaWeight Q) (u : ℤ) (hu : |(u : ℝ)| ≤ Q ^ 2) :
    (if u = 0 then 1 else 0 : ℂ) =
      ∑ q ∈ dfiEquation22Moduli Q,
        (dfiDeltaKernel w q u : ℂ) * ramanujanSumInt q u := by
  rw [← dfiDeltaIdentity w u, dfiDeltaExpansion_eq_tsum_moduli]
  apply tsum_eq_sum
  intro q hq
  by_cases hq0 : q = 0
  · simp [hq0, ramanujanSumInt]
  have hqpos : 0 < q := Nat.pos_of_ne_zero hq0
  have hnotlt : ¬(q : ℝ) < 2 * Q := by
    intro hlt
    exact hq ((mem_dfiEquation22Moduli_iff q).2 ⟨hqpos, hlt⟩)
  have hkernel := dfiDeltaKernel_eq_zero_of_two_mul_le w hu q (le_of_not_gt hnotlt)
  simp [hkernel]

theorem ramanujanSumInt_eq_sum_coprime
    (q : ℕ) [NeZero q] (hq : 0 < q) (u : ℤ) :
    ramanujanSumInt q u =
      ∑ d ∈ Finset.range q with Nat.Coprime d q,
        ZMod.stdAddChar ((u : ZMod q) * (d : ZMod q)) := by
  simp [ramanujanSumInt, hq.ne']

/-- The standard additive character at an integer frequency, totalized at
the unused modulus `q=0`. -/
noncomputable def dfiAdditiveCharacter (q : ℕ) (z : ℤ) : ℂ :=
  if hq : q = 0 then 0
  else
    letI : NeZero q := ⟨hq⟩
    ZMod.stdAddChar (z : ZMod q)

theorem dfiAdditiveCharacter_eq
    (q : ℕ) [NeZero q] (hq : 0 < q) (z : ℤ) :
    dfiAdditiveCharacter q z = ZMod.stdAddChar (z : ZMod q) := by
  simp [dfiAdditiveCharacter, hq.ne']

/-- The source quantity `E(m,n)` directly below DFI equation (22). -/
noncomputable def dfiEquation22Weight
    {Q : ℝ} (w : DFIDeltaWeight Q) (F : ℝ → ℝ → ℂ)
    (a b : ℕ) (h : ℤ) (q m n : ℕ) : ℂ :=
  F (a * m) (b * n) *
    (dfiDeltaKernel w q (quadraticDivisorShift a b m n - h) : ℂ)

/-- The finite form of the shifted divisor sum on the left of equation
(22).  The explicit positive bounds are harmless because the localized
source weight has compact dyadic support. -/
noncomputable def dfiEquation22Left
    (F : ℝ → ℝ → ℂ) (a b M N : ℕ) (h : ℤ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
    divisorWeight m * divisorWeight n * F (a * m) (b * n) *
      if quadraticDivisorShift a b m n = h then 1 else 0

/-- The literal right side of DFI equation (22), with its two separate
additive characters and the source quantity `E(m,n)`. -/
noncomputable def dfiEquation22Right
    {Q : ℝ} (w : DFIDeltaWeight Q) (F : ℝ → ℝ → ℂ)
    (a b M N : ℕ) (h : ℤ) : ℂ :=
  ∑ q ∈ dfiEquation22Moduli Q,
    ∑ d ∈ Finset.range q with Nat.Coprime d q,
      dfiAdditiveCharacter q ((-h) * d) *
        ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
          divisorWeight m * divisorWeight n *
            dfiAdditiveCharacter q (quadraticDivisorShift a b m n * d) *
            dfiEquation22Weight w F a b h q m n

theorem dfiLocalizedWeight_shift_abs_lt
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {U h x y : ℝ}
    (hφ : DFIRedundantCutoff φ U)
    (hne : dfiLocalizedWeight f φ h x y ≠ 0) :
    |x - y - h| < U := by
  have hφne : φ (x - y - h) ≠ 0 := by
    intro hz
    exact hne (by simp [dfiLocalizedWeight, hz])
  have hmem := hφ.support_subset hφne
  rw [abs_lt]
  exact hmem

theorem dfiEquation22_point
    {Q U : ℝ} (w : DFIDeltaWeight Q) {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hφ : DFIRedundantCutoff φ U) (hQU : Q ^ 2 = U)
    (a b m n : ℕ) (h : ℤ) :
    dfiLocalizedWeight f φ h (a * m) (b * n) *
        (if quadraticDivisorShift a b m n = h then 1 else 0) =
      ∑ q ∈ dfiEquation22Moduli Q,
        ∑ d ∈ Finset.range q with Nat.Coprime d q,
          dfiAdditiveCharacter q ((-h) * d) *
          dfiAdditiveCharacter q (quadraticDivisorShift a b m n * d) *
          dfiEquation22Weight w (dfiLocalizedWeight f φ h) a b h q m n := by
  let shift := quadraticDivisorShift a b m n
  let u := shift - h
  by_cases hF : dfiLocalizedWeight f φ h (a * m) (b * n) = 0
  · simp [hF, dfiEquation22Weight]
  have hu : |(u : ℝ)| ≤ Q ^ 2 := by
    have hlt := dfiLocalizedWeight_shift_abs_lt hφ hF
    have hcast : ((u : ℤ) : ℝ) =
        (a * m : ℕ) - (b * n : ℕ) - (h : ℝ) := by
      dsimp [u, shift, quadraticDivisorShift]
      push_cast
      ring
    rw [hcast]
    rw [hQU]
    simpa only [Nat.cast_mul] using hlt.le
  have hdelta := dfiDeltaIdentity_short_moduli w u hu
  have hzero : u = 0 ↔ shift = h := sub_eq_zero
  have hif : (if u = 0 then 1 else 0 : ℂ) =
      if shift = h then 1 else 0 := if_congr hzero rfl rfl
  rw [hif] at hdelta
  calc
    dfiLocalizedWeight f φ h (a * m) (b * n) *
        (if shift = h then 1 else 0) =
      dfiLocalizedWeight f φ h (a * m) (b * n) *
        ∑ q ∈ dfiEquation22Moduli Q,
          (dfiDeltaKernel w q u : ℂ) * ramanujanSumInt q u := by rw [hdelta]
    _ = ∑ q ∈ dfiEquation22Moduli Q,
        ∑ d ∈ Finset.range q with Nat.Coprime d q,
          dfiAdditiveCharacter q ((-h) * d) *
          dfiAdditiveCharacter q (shift * d) *
          dfiEquation22Weight w (dfiLocalizedWeight f φ h) a b h q m n := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      have hqpos := (mem_dfiEquation22Moduli_iff q).1 hq |>.1
      letI : NeZero q := ⟨hqpos.ne'⟩
      rw [ramanujanSumInt_eq_sum_coprime q hqpos]
      rw [show dfiLocalizedWeight f φ h (a * m) (b * n) *
          ((dfiDeltaKernel w q u : ℂ) *
            ∑ d ∈ Finset.range q with Nat.Coprime d q,
              ZMod.stdAddChar ((u : ZMod q) * (d : ZMod q))) =
        (dfiLocalizedWeight f φ h (a * m) (b * n) *
          (dfiDeltaKernel w q u : ℂ)) *
            ∑ d ∈ Finset.range q with Nat.Coprime d q,
              ZMod.stdAddChar ((u : ZMod q) * (d : ZMod q)) by ring]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      rw [dfiAdditiveCharacter_eq q hqpos,
        dfiAdditiveCharacter_eq q hqpos]
      have hchar :
          ZMod.stdAddChar ((u : ZMod q) * (d : ZMod q)) =
            ZMod.stdAddChar (((-h : ℤ) : ZMod q) * (d : ZMod q)) *
            ZMod.stdAddChar ((shift : ZMod q) * (d : ZMod q)) := by
        rw [← ZMod.stdAddChar.map_add_eq_mul]
        apply congrArg ZMod.stdAddChar
        dsimp [u]
        push_cast
        ring
      rw [hchar]
      dsimp [u, shift, dfiEquation22Weight]
      push_cast
      ring
    _ = _ := by rfl

/-- DFI equation (22): exact finite delta-symbol insertion, character
splitting, and interchange of the four finite sums. -/
theorem dfiEquation22
    {Q U : ℝ} (w : DFIDeltaWeight Q) {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hφ : DFIRedundantCutoff φ U) (hQU : Q ^ 2 = U)
    (a b M N : ℕ) (h : ℤ) :
    dfiEquation22Left (dfiLocalizedWeight f φ h) a b M N h =
      dfiEquation22Right w (dfiLocalizedWeight f φ h) a b M N h := by
  let T : ℕ → ℕ → ℕ → ℕ → ℂ := fun q d m n =>
    divisorWeight m * divisorWeight n *
      dfiAdditiveCharacter q ((-h) * d) *
      dfiAdditiveCharacter q (quadraticDivisorShift a b m n * d) *
      dfiEquation22Weight w (dfiLocalizedWeight f φ h) a b h q m n
  have hleft :
      dfiEquation22Left (dfiLocalizedWeight f φ h) a b M N h =
        ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
          ∑ q ∈ dfiEquation22Moduli Q,
            ∑ d ∈ Finset.range q with Nat.Coprime d q, T q d m n := by
    unfold dfiEquation22Left
    apply Finset.sum_congr rfl
    intro m hm
    apply Finset.sum_congr rfl
    intro n hn
    change divisorWeight m * divisorWeight n *
          dfiLocalizedWeight f φ (h : ℝ) ((a : ℝ) * m) ((b : ℝ) * n) *
          (if quadraticDivisorShift a b m n = h then 1 else 0) = _
    rw [show divisorWeight m * divisorWeight n *
          dfiLocalizedWeight f φ h ((a : ℝ) * m) ((b : ℝ) * n) *
          (if quadraticDivisorShift a b m n = h then 1 else 0) =
        (divisorWeight m * divisorWeight n) *
          (dfiLocalizedWeight f φ h ((a : ℝ) * m) ((b : ℝ) * n) *
            (if quadraticDivisorShift a b m n = h then 1 else 0)) by ring]
    rw [dfiEquation22_point w hφ hQU a b m n h]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    apply Finset.sum_congr rfl
    intro d hd
    dsimp [T]
    ring
  have hreorder :
      (∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
          ∑ q ∈ dfiEquation22Moduli Q,
            ∑ d ∈ Finset.range q with Nat.Coprime d q, T q d m n) =
        ∑ q ∈ dfiEquation22Moduli Q,
          ∑ d ∈ Finset.range q with Nat.Coprime d q,
            ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N, T q d m n := by
    calc
      (∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
          ∑ q ∈ dfiEquation22Moduli Q,
            ∑ d ∈ Finset.range q with Nat.Coprime d q, T q d m n) =
        ∑ m ∈ Finset.Icc 1 M, ∑ q ∈ dfiEquation22Moduli Q,
          ∑ n ∈ Finset.Icc 1 N,
            ∑ d ∈ Finset.range q with Nat.Coprime d q, T q d m n := by
              apply Finset.sum_congr rfl
              intro m hm
              rw [Finset.sum_comm]
      _ = ∑ q ∈ dfiEquation22Moduli Q, ∑ m ∈ Finset.Icc 1 M,
          ∑ n ∈ Finset.Icc 1 N,
            ∑ d ∈ Finset.range q with Nat.Coprime d q, T q d m n := by
              rw [Finset.sum_comm]
      _ = ∑ q ∈ dfiEquation22Moduli Q, ∑ m ∈ Finset.Icc 1 M,
          ∑ d ∈ Finset.range q with Nat.Coprime d q,
            ∑ n ∈ Finset.Icc 1 N, T q d m n := by
              apply Finset.sum_congr rfl
              intro q hq
              apply Finset.sum_congr rfl
              intro m hm
              rw [Finset.sum_comm]
      _ = ∑ q ∈ dfiEquation22Moduli Q,
          ∑ d ∈ Finset.range q with Nat.Coprime d q,
            ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N, T q d m n := by
              apply Finset.sum_congr rfl
              intro q hq
              rw [Finset.sum_comm]
  have hright :
      dfiEquation22Right w (dfiLocalizedWeight f φ h) a b M N h =
        ∑ q ∈ dfiEquation22Moduli Q,
          ∑ d ∈ Finset.range q with Nat.Coprime d q,
            ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N, T q d m n := by
    unfold dfiEquation22Right
    apply Finset.sum_congr rfl
    intro q hq
    apply Finset.sum_congr rfl
    intro d hd
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    apply Finset.sum_congr rfl
    intro n hn
    dsimp [T]
    ring
  exact hleft.trans (hreorder.trans hright.symm)

end RiemannZeta.GuthMaynard
