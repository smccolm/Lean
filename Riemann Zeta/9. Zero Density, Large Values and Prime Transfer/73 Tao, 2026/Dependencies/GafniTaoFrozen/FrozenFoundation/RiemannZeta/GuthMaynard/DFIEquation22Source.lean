import RiemannZeta.GuthMaynard.DFIEquation24

/-!
# The exact source bridge from DFI equation (22) to equation (23)

Equation (22) is a finite sum because the source weight is supported in a
dyadic rectangle.  Equation (23), as naturally produced by the Estermann
functional equation, is expressed using absolutely convergent `tsum`s.  This
module proves that the two inputs are exactly equal; no infinite-sum tail is
discarded at the interface.
-/

open Complex Finset Set
open scoped BigOperators
open Classical

namespace RiemannZeta.GuthMaynard

/-- The finite dyadic version of DFI's source sum `D_f(a,b;h)`, with the
real-variable weight evaluated at `(a*m,b*n)`. -/
noncomputable def dfiDyadicShiftedDivisorSum
    (f : ℝ → ℝ → ℂ) (a b M N : ℕ) (h : ℤ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
    if quadraticDivisorShift a b m n = h then
      divisorWeight m * divisorWeight n * f (a * m) (b * n)
    else 0

/-- The redundant cutoff in equation (21) is exactly one on every summand
selected by the shifted equation, so it leaves the source sum unchanged. -/
theorem dfiEquation22Left_localized_eq_source
    {U : ℝ} {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hφ : DFIRedundantCutoff φ U) (a b M N : ℕ) (h : ℤ) :
    dfiEquation22Left (dfiLocalizedWeight f φ h) a b M N h =
      dfiDyadicShiftedDivisorSum f a b M N h := by
  unfold dfiEquation22Left dfiDyadicShiftedDivisorSum
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hShift : quadraticDivisorShift a b m n = h
  · rw [if_pos hShift, if_pos hShift]
    rw [dfiLocalizedWeight_eq_of_sub_eq hφ]
    · ring
    · unfold quadraticDivisorShift at hShift
      exact_mod_cast hShift
  · simp [hShift]

/-- A compactly supported two-variable periodic divisor series is exactly its
finite positive rectangle.  The `n = 0` terms vanish because the divisor
coefficient at zero vanishes. -/
theorem dfiEquation23SourceLeft_eq_finite_of_support
    (q a b d M N : ℕ) [NeZero q] (E : ℝ → ℝ → ℂ)
    (hSupport : Function.support (Function.uncurry E) ⊆
      Set.Icc (0 : ℝ) M ×ˢ Set.Icc (0 : ℝ) N) :
    dfiEquation23SourceLeft q a b d E =
      ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
        periodicDivisorCoeff q
            (dfiVoronoiCharacter q (((a * d : ℕ) : ZMod q))) m *
          periodicDivisorCoeff q
            (dfiVoronoiCharacter q (-(((b * d : ℕ) : ZMod q)))) n *
          E m n := by
  unfold dfiEquation23SourceLeft periodicDivisorWeightedSum
  rw [tsum_eq_sum (s := Finset.Icc 1 M)]
  · apply Finset.sum_congr rfl
    intro m hm
    change periodicDivisorCoeff q
          (dfiVoronoiCharacter q (((a * d : ℕ) : ZMod q))) m *
        (∑' n : ℕ, periodicDivisorCoeff q
            (dfiVoronoiCharacter q (-(((b * d : ℕ) : ZMod q)))) n *
          E m n) = _
    rw [tsum_eq_sum (s := Finset.Icc 1 N)]
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    · intro n hn
      have hnOutside : n = 0 ∨ N < n := by
        simp only [Finset.mem_Icc, not_and_or, not_le] at hn
        omega
      rcases hnOutside with rfl | hnLarge
      · simp [periodicDivisorCoeff]
      · have hEzero : E m n = 0 := by
          by_contra hne
          have hp := hSupport (show ((m : ℝ), (n : ℝ)) ∈
            Function.support (Function.uncurry E) from hne)
          have hnUpper : (n : ℝ) ≤ N := hp.2.2
          exact (not_lt_of_ge hnUpper) (by exact_mod_cast hnLarge)
        simp [hEzero]
  · intro m hm
    have hmOutside : m = 0 ∨ M < m := by
      simp only [Finset.mem_Icc, not_and_or, not_le] at hm
      omega
    rcases hmOutside with rfl | hmLarge
    · simp [periodicDivisorCoeff]
    · have hEzero : ∀ y : ℝ, E m y = 0 := by
        intro y
        by_contra hne
        have hp := hSupport (show ((m : ℝ), y) ∈
          Function.support (Function.uncurry E) from hne)
        have hmUpper : (m : ℝ) ≤ M := hp.1.2
        exact (not_lt_of_ge hmUpper) (by exact_mod_cast hmLarge)
      simp [hEzero]

/-- The finite inner `m,n` sum in equation (22) is literally the source
periodic divisor sum to which the two Voronoi formulas in equation (23) are
applied. -/
theorem dfiEquation22_inner_eq_equation23SourceLeft
    {Q X Y : ℝ} (w : DFIDeltaWeight Q) (F : ℝ → ℝ → ℂ)
    (hF : Function.support (Function.uncurry F) ⊆
      Set.Icc X (2 * X) ×ˢ Set.Icc Y (2 * Y))
    (a b M N : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hX : 0 < X) (hY : 0 < Y)
    (hM : 2 * X / a ≤ M) (hN : 2 * Y / b ≤ N)
    (h : ℤ) (q : ℕ) [NeZero q] (hq : 0 < q) (d : ℕ) :
    (∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N,
      divisorWeight m * divisorWeight n *
        dfiAdditiveCharacter q (quadraticDivisorShift a b m n * d) *
        dfiEquation22Weight w F a b h q m n) =
      dfiEquation23SourceLeft q a b d
        (dfiEquation23Weight w F a b h q) := by
  have hSupport : Function.support (Function.uncurry
      (dfiEquation23Weight w F a b h q)) ⊆
      Set.Icc (0 : ℝ) M ×ˢ Set.Icc (0 : ℝ) N := by
    intro p hp
    have hFne : F ((a : ℝ) * p.1) ((b : ℝ) * p.2) ≠ 0 := by
      intro hz
      exact hp (by simp [Function.uncurry, dfiEquation23Weight, hz])
    have hxy := hF (show ((a : ℝ) * p.1, (b : ℝ) * p.2) ∈
      Function.support (Function.uncurry F) from hFne)
    have haR : (0 : ℝ) < a := by exact_mod_cast ha
    have hbR : (0 : ℝ) < b := by exact_mod_cast hb
    constructor
    · constructor
      · have hpos : 0 < (a : ℝ) * p.1 := hX.trans_le hxy.1.1
        nlinarith
      · exact ((le_div_iff₀ haR).2 (by
          simpa only [mul_comm] using hxy.1.2)).trans hM
    · constructor
      · have hpos : 0 < (b : ℝ) * p.2 := hY.trans_le hxy.2.1
        nlinarith
      · exact ((le_div_iff₀ hbR).2 (by
          simpa only [mul_comm] using hxy.2.2)).trans hN
  rw [dfiEquation23SourceLeft_eq_finite_of_support
    q a b d M N (dfiEquation23Weight w F a b h q) hSupport]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  rw [periodicDivisorCoeff_voronoiCharacter,
    periodicDivisorCoeff_voronoiCharacter,
    dfiAdditiveCharacter_eq q hq,
    dfiEquation23Weight_natCast]
  have hchar :
      ZMod.stdAddChar ((quadraticDivisorShift a b m n * d : ℤ) : ZMod q) =
        ZMod.stdAddChar (((a * d : ℕ) : ZMod q) * (m : ZMod q)) *
          ZMod.stdAddChar (-(((b * d : ℕ) : ZMod q)) * (n : ZMod q)) := by
    rw [← ZMod.stdAddChar.map_add_eq_mul]
    congr 1
    unfold quadraticDivisorShift
    push_cast
    ring
  rw [hchar]
  ring

/-- Totalized equation-(24) pre-Voronoi term.  The zero modulus is assigned
zero and is never selected by the equation-(22) modulus set. -/
noncomputable def dfiEquation24PreVoronoiTotal
    (q a b : ℕ) (h : ℤ) (E : ℝ → ℝ → ℂ) : ℂ :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩
    dfiEquation24PreVoronoi q a b h E

/-- Totalized double-main term from equation (24). -/
noncomputable def dfiEquation24MainTotal
    (q a b : ℕ) (h : ℤ) (E : ℝ → ℝ → ℂ) : ℂ :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩
    dfiEquation24MainCoefficient q h
      (dfiVoronoiMainTerm (dfiReducedModulus a q).denominator (fun x =>
        dfiVoronoiMainTerm (dfiReducedModulus b q).denominator (E x)))

/-- Totalized sum of the eight non-main branches from equation (24). -/
noncomputable def dfiEquation24ErrorTotal
    (q a b : ℕ) (h : ℤ) (E : ℝ → ℝ → ℂ) : ℂ :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩
    dfiEquation24ReducedError q a b h E

/-- Source-specialized equations (23)--(24) for one positive modulus, with
the double-main term separated from all eight Voronoi error branches. -/
theorem dfiEquation24PreVoronoiTotal_eq_main_add_error
    {Q P X Y U : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (h : ℤ)
    (q : ℕ) (hq : 0 < q) :
    dfiEquation24PreVoronoiTotal q a b h
        (dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q) =
      dfiEquation24MainTotal q a b h
          (dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q) +
        dfiEquation24ErrorTotal q a b h
          (dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q) := by
  letI : NeZero q := ⟨hq.ne'⟩
  rw [dfiEquation24PreVoronoiTotal, dif_neg hq.ne',
    dfiEquation24MainTotal, dif_neg hq.ne',
    dfiEquation24ErrorTotal, dif_neg hq.ne']
  rw [dfiEquation24_reassemble_equation23
    w hf hbox hφ a b ha hb h q hq]
  exact dfiEquation24ReducedExpansion_eq_main_add_error q a b h _

/-- Equation (22), after the compact-support truncation has been discharged,
is the finite sum of the exact equation-(23) source inputs over the delta
moduli and primitive residues. -/
theorem dfiEquation22Right_eq_sum_equation24PreVoronoi
    {Q X Y : ℝ} (w : DFIDeltaWeight Q) (F : ℝ → ℝ → ℂ)
    (hF : Function.support (Function.uncurry F) ⊆
      Set.Icc X (2 * X) ×ˢ Set.Icc Y (2 * Y))
    (a b M N : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hX : 0 < X) (hY : 0 < Y)
    (hM : 2 * X / a ≤ M) (hN : 2 * Y / b ≤ N) (h : ℤ) :
    dfiEquation22Right w F a b M N h =
      ∑ q ∈ dfiEquation22Moduli Q,
        dfiEquation24PreVoronoiTotal q a b h
          (dfiEquation23Weight w F a b h q) := by
  unfold dfiEquation22Right
  apply Finset.sum_congr rfl
  intro q hqMem
  have hq : 0 < q := (mem_dfiEquation22Moduli_iff q).1 hqMem |>.1
  letI : NeZero q := ⟨hq.ne'⟩
  rw [dfiEquation24PreVoronoiTotal, dif_neg hq.ne']
  unfold dfiEquation24PreVoronoi
  apply Finset.sum_congr rfl
  intro d hd
  rw [dfiAdditiveCharacter_eq q hq]
  congr 1
  exact dfiEquation22_inner_eq_equation23SourceLeft
    w F hF a b M N ha hb hX hY hM hN h q hq d

/-- Exact source assembly of equations (22)--(24): the original finite
shifted divisor sum equals the sum of the double-main contributions plus the
sum of all eight Voronoi errors. -/
theorem dfiEquation22_eq_sum_main_add_sum_error
    {Q U P X Y : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hQU : Q ^ 2 = U)
    (a b M N : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hM : 2 * X / a ≤ M) (hN : 2 * Y / b ≤ N) (h : ℤ) :
    dfiEquation22Left (dfiLocalizedWeight f φ h) a b M N h =
      (∑ q ∈ dfiEquation22Moduli Q,
        dfiEquation24MainTotal q a b h
          (dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q)) +
      ∑ q ∈ dfiEquation22Moduli Q,
        dfiEquation24ErrorTotal q a b h
          (dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q) := by
  rw [dfiEquation22 w hφ hQU a b M N h]
  rw [dfiEquation22Right_eq_sum_equation24PreVoronoi
    w (dfiLocalizedWeight f φ h)
    (support_uncurry_dfiLocalizedWeight_subset hbox)
    a b M N ha hb
    (zero_lt_one.trans_le hf.one_le_X)
    (zero_lt_one.trans_le hf.one_le_Y) hM hN h]
  calc
    (∑ q ∈ dfiEquation22Moduli Q,
      dfiEquation24PreVoronoiTotal q a b h
        (dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q)) =
        ∑ q ∈ dfiEquation22Moduli Q,
          (dfiEquation24MainTotal q a b h
              (dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q) +
            dfiEquation24ErrorTotal q a b h
              (dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q)) := by
          apply Finset.sum_congr rfl
          intro q hqMem
          exact dfiEquation24PreVoronoiTotal_eq_main_add_error
            w hf hbox hφ a b ha hb h q
              ((mem_dfiEquation22Moduli_iff q).1 hqMem |>.1)
    _ = _ := by rw [Finset.sum_add_distrib]

/-- Equations (22)--(24) stated directly for DFI's finite dyadic source
sum. -/
theorem dfiDyadicShiftedDivisorSum_eq_sum_main_add_sum_error
    {Q U P X Y : ℝ} (w : DFIDeltaWeight Q)
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hQU : Q ^ 2 = U)
    (a b M N : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hM : 2 * X / a ≤ M) (hN : 2 * Y / b ≤ N) (h : ℤ) :
    dfiDyadicShiftedDivisorSum f a b M N h =
      (∑ q ∈ dfiEquation22Moduli Q,
        dfiEquation24MainTotal q a b h
          (dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q)) +
      ∑ q ∈ dfiEquation22Moduli Q,
        dfiEquation24ErrorTotal q a b h
          (dfiEquation23Weight w (dfiLocalizedWeight f φ h) a b h q) := by
  rw [← dfiEquation22Left_localized_eq_source hφ a b M N h]
  exact dfiEquation22_eq_sum_main_add_sum_error
    w hf hbox hφ hQU a b M N ha hb hM hN h

end RiemannZeta.GuthMaynard
