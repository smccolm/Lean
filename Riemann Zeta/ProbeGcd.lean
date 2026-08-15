import RiemannZeta.GuthMaynard.DFIDivisorEpsilon
import RiemannZeta.GuthMaynard.DFIReducedModulus
import RiemannZeta.GuthMaynard.DFIEquation22
import RiemannZeta.GuthMaynard.DFIErrorTerms

example (q : ℕ) [NeZero q] (z : ℤ) :
    Nat.gcd ((z : ZMod q).val) q = z.gcd q := by
  rw [← Int.gcd_emod z q, ← ZMod.val_intCast]
  rfl

example (q : ℕ) [NeZero q] (h : ℤ) :
    Nat.gcd ((-h : ZMod q).val) q = Nat.gcd h.natAbs q := by
  rw [← Int.cast_neg]
  calc
    Nat.gcd (((-h : ℤ) : ZMod q).val) q = (-h).gcd q := by
      rw [← Int.gcd_emod (-h) q, ← ZMod.val_intCast]
      rfl
    _ = Nat.gcd h.natAbs q := by simp [Int.gcd_def]

open scoped BigOperators

open Nat

example (k : ℕ) (hk : 0 < k) :
    (∑' n : ℕ, (n : ℝ) ^ (-(1 : ℝ) - k)) ≤ 1 + 1 / (k : ℝ) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hbase : Summable (fun n : ℕ ↦ (n : ℝ) ^ (-(1 : ℝ) - k)) := by
    apply Real.summable_nat_rpow.mpr
    linarith
  have hsplit := hbase.sum_add_tsum_nat_add 2
  have htail := RiemannZeta.GuthMaynard.tsum_nat_add_one_rpow_neg_le
    (L := (1 : ℝ)) (p := 1 + (k : ℝ)) (by norm_num) (by linarith)
  have htail' :
      (∑' j : ℕ, ((j + 2 : ℕ) : ℝ) ^ (-(1 : ℝ) - k)) ≤ 1 / (k : ℝ) := by
    calc
      _ = ∑' j : ℕ, (1 + ((j + 1 : ℕ) : ℝ)) ^ (-(1 + (k : ℝ))) := by
        apply tsum_congr
        intro j
        congr 2 <;> push_cast <;> ring
      _ ≤ 1 ^ (1 - (1 + (k : ℝ))) / (1 + (k : ℝ) - 1) := htail
      _ = 1 / (k : ℝ) := by rw [Real.one_rpow]; ring_nf
  calc
    (∑' n : ℕ, (n : ℝ) ^ (-(1 : ℝ) - k)) =
        (∑ n ∈ Finset.range 2, (n : ℝ) ^ (-(1 : ℝ) - k)) +
          ∑' j : ℕ, ((j + 2 : ℕ) : ℝ) ^ (-(1 : ℝ) - k) := by
      simpa [Nat.cast_add, add_comm] using hsplit.symm
    _ = 1 + ∑' j : ℕ, ((j + 2 : ℕ) : ℝ) ^ (-(1 : ℝ) - k) := by
      have hexp : -(1 : ℝ) - k < 0 := by linarith
      norm_num [Finset.sum_range_succ, Real.zero_rpow hexp.ne]
    _ ≤ 1 + 1 / (k : ℝ) := by gcongr

open RiemannZeta.GuthMaynard

example
    (qx : ℕ) [NeZero qx] (xBranch : DFIVoronoiDualBranch)
    (qy : ℕ) [NeZero qy] (yBranch : DFIVoronoiDualBranch)
    (E : ℝ → ℝ → ℂ) (Lx Ly k : ℕ) (hLx : 0 < Lx) (hLy : 0 < Ly)
    (hk : 0 < k) (A : ℝ) (hA : 0 ≤ A)
    (hPoint : ∀ m n : ℕ, 0 < m → 0 < n →
      ‖dfiEquation24DoubleDualMellinAmplitude
          qx xBranch qy yBranch E m n‖ ≤
        A * (m : ℝ) ^ (-(1 : ℝ) - k) *
          (n : ℝ) ^ (-(1 : ℝ) - k)) :
    dfiEquation29DoubleRetainedXTailYMass
        qx xBranch qy yBranch E Lx Ly ≤
      A * (1 + 1 / (k : ℝ)) *
        ((Ly : ℝ) ^ (-(k : ℝ)) / (k : ℝ)) := by
  let p : ℕ → ℝ := fun n ↦ (n : ℝ) ^ (-(1 : ℝ) - k)
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hp : Summable p := by
    dsimp [p]
    apply Real.summable_nat_rpow.mpr
    linarith
  have hp0 (n : ℕ) : 0 ≤ p n := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hTailSummable : Summable (fun j : ℕ ↦ p (Ly + (j + 1))) := by
    have hs := (summable_nat_add_iff (Ly + 1)).2 hp
    simpa [p, Nat.cast_add, add_assoc, add_comm, add_left_comm] using hs
  have hTail := tsum_nat_add_rpow_neg_one_sub_nat_le Ly k hLy hk
  have hEach (m : ℕ) (hm : 0 < m) :
      (∑' j : ℕ, ‖dfiEquation24DoubleDualMellinAmplitude qx xBranch qy yBranch E
          m (Ly + (j + 1))‖) ≤
        (A * p m) * ((Ly : ℝ) ^ (-(k : ℝ)) / (k : ℝ)) := by
    have hAmpAll := summable_norm_dfiEquation24DoubleDualMellinAmplitude_right
      (E := E) qx xBranch qy yBranch m
    have hAmp : Summable (fun j : ℕ ↦
        ‖dfiEquation24DoubleDualMellinAmplitude qx xBranch qy yBranch E
          m (Ly + (j + 1))‖) := by
      have hs := (summable_nat_add_iff (Ly + 1)).2 hAmpAll
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs
    calc
      _ ≤ ∑' j : ℕ, (A * p m) * p (Ly + (j + 1)) :=
        hAmp.tsum_le_tsum (fun j ↦ by
          have hn : 0 < Ly + (j + 1) := by omega
          simpa [p, mul_assoc] using hPoint m (Ly + (j + 1)) hm hn)
          (hTailSummable.mul_left (A * p m))
      _ = (A * p m) * ∑' j : ℕ, p (Ly + (j + 1)) := by rw [tsum_mul_left]
      _ ≤ (A * p m) * ((Ly : ℝ) ^ (-(k : ℝ)) / (k : ℝ)) := by
        gcongr
  unfold dfiEquation29DoubleRetainedXTailYMass
  calc
    _ ≤ ∑ m ∈ Finset.Icc 1 Lx,
        (A * p m) * ((Ly : ℝ) ^ (-(k : ℝ)) / (k : ℝ)) := by
      apply Finset.sum_le_sum
      intro m hm
      exact hEach m (Finset.mem_Icc.mp hm).1
    _ = (A * ((Ly : ℝ) ^ (-(k : ℝ)) / (k : ℝ))) *
        ∑ m ∈ Finset.Icc 1 Lx, p m := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      ring
    _ ≤ (A * ((Ly : ℝ) ^ (-(k : ℝ)) / (k : ℝ))) *
        (∑' m : ℕ, p m) := by
      gcongr
      exact hp.sum_le_tsum (Finset.Icc 1 Lx) (fun n hn ↦ hp0 n)
    _ ≤ (A * ((Ly : ℝ) ^ (-(k : ℝ)) / (k : ℝ))) *
        (1 + 1 / (k : ℝ)) := by
      gcongr
      exact tsum_natCast_rpow_neg_one_sub_nat_le k hk
    _ = _ := by ring

example
    (qx : ℕ) [NeZero qx] (xBranch : DFIVoronoiDualBranch)
    (qy : ℕ) [NeZero qy] (yBranch : DFIVoronoiDualBranch)
    (E : ℝ → ℝ → ℂ) (Lx k : ℕ) (hLx : 0 < Lx)
    (hk : 0 < k) (A : ℝ) (hA : 0 ≤ A)
    (hPoint : ∀ m n : ℕ, 0 < m → 0 < n →
      ‖dfiEquation24DoubleDualMellinAmplitude
          qx xBranch qy yBranch E m n‖ ≤
        A * (m : ℝ) ^ (-(1 : ℝ) - k) *
          (n : ℝ) ^ (-(1 : ℝ) - k)) :
    dfiEquation29DoubleTailXAllYMass
        qx xBranch qy yBranch E Lx ≤
      A * ((Lx : ℝ) ^ (-(k : ℝ)) / (k : ℝ)) *
        (1 + 1 / (k : ℝ)) := by
  let p : ℕ → ℝ := fun n ↦ (n : ℝ) ^ (-(1 : ℝ) - k)
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hp : Summable p := by
    dsimp [p]
    apply Real.summable_nat_rpow.mpr
    linarith
  have hp0 (n : ℕ) : 0 ≤ p n := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hTailSummable : Summable (fun i : ℕ ↦ p (Lx + (i + 1))) := by
    have hs := (summable_nat_add_iff (Lx + 1)).2 hp
    simpa [p, Nat.cast_add, add_assoc, add_comm, add_left_comm] using hs
  have hTail := tsum_nat_add_rpow_neg_one_sub_nat_le Lx k hLx hk
  have hMass := tsum_natCast_rpow_neg_one_sub_nat_le k hk
  have hInner (m : ℕ) (hm : 0 < m) :
      (∑' n : ℕ, ‖dfiEquation24DoubleDualMellinAmplitude qx xBranch qy yBranch E
          m n‖) ≤ (A * p m) * (1 + 1 / (k : ℝ)) := by
    have hAmp := summable_norm_dfiEquation24DoubleDualMellinAmplitude_right
      (E := E) qx xBranch qy yBranch m
    calc
      _ ≤ ∑' n : ℕ, (A * p m) * p n :=
        hAmp.tsum_le_tsum (fun n ↦ by
          by_cases hn : n = 0
          · subst n
            rw [show dfiEquation24DoubleDualMellinAmplitude
                qx xBranch qy yBranch E m 0 = 0 by
              simp [dfiEquation24DoubleDualMellinAmplitude,
                dfiEquation24DoubleDualAmplitudeIntegrand, divisorWeight]]
            simp only [norm_zero]
            exact mul_nonneg (mul_nonneg hA (hp0 m)) (hp0 0)
          · exact hPoint m n hm (Nat.pos_of_ne_zero hn))
          (hp.mul_left (A * p m))
      _ = (A * p m) * ∑' n : ℕ, p n := by rw [tsum_mul_left]
      _ ≤ (A * p m) * (1 + 1 / (k : ℝ)) := by gcongr
  unfold dfiEquation29DoubleTailXAllYMass
  have hAmpOuter := summable_tsum_norm_dfiEquation24DoubleDualMellinAmplitude
    (E := E) qx xBranch qy yBranch
  have hAmpTail : Summable (fun i : ℕ ↦
      ∑' n : ℕ, ‖dfiEquation24DoubleDualMellinAmplitude qx xBranch qy yBranch E
        (Lx + (i + 1)) n‖) := by
    have hs := (summable_nat_add_iff (Lx + 1)).2 hAmpOuter
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs
  calc
    _ ≤ ∑' i : ℕ, (A * p (Lx + (i + 1))) *
        (1 + 1 / (k : ℝ)) :=
      hAmpTail.tsum_le_tsum (fun i ↦ hInner (Lx + (i + 1)) (by omega))
        ((hTailSummable.mul_left A).mul_right (1 + 1 / (k : ℝ)))
    _ = (A * ∑' i : ℕ, p (Lx + (i + 1))) *
        (1 + 1 / (k : ℝ)) := by
      rw [← tsum_mul_left, tsum_mul_right]
    _ ≤ (A * ((Lx : ℝ) ^ (-(k : ℝ)) / (k : ℝ))) *
        (1 + 1 / (k : ℝ)) := by gcongr

example (L d : ℕ) (hd : 0 < d) :
    (∑ q ∈ Finset.Ioo 0 L,
        if d ∣ q then Real.sqrt d / Real.sqrt q else 0) ≤
      Real.sqrt L * Real.sqrt (((harmonic L : ℚ) : ℝ)) := by
  rw [← Finset.sum_filter]
  let S := (Finset.Ioo 0 L).filter (d ∣ ·)
  have hquotPos : ∀ q ∈ S, 0 < q / d := by
    intro q hq
    have hqPos := (Finset.mem_Ioo.mp (Finset.mem_filter.mp hq).1).1
    exact Nat.div_pos (Nat.le_of_dvd hqPos (Finset.mem_filter.mp hq).2) hd
  have hterm : ∀ q ∈ S,
      Real.sqrt d / Real.sqrt q = 1 / Real.sqrt ((q / d : ℕ) : ℝ) := by
    intro q hq
    have hdq := (Finset.mem_filter.mp hq).2
    have hqPos := (Finset.mem_Ioo.mp (Finset.mem_filter.mp hq).1).1
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd
    have hqR : (0 : ℝ) < q := by exact_mod_cast hqPos
    have hdNe : (d : ℝ) ≠ 0 := hdR.ne'
    rw [← Real.sqrt_div (Nat.cast_nonneg d) q]
    have hcast : (d : ℝ) / q = 1 / ((q / d : ℕ) : ℝ) := by
      rw [Nat.cast_div hdq hdNe]
      field_simp
    rw [hcast, Real.sqrt_div (by positivity)]
    simp
  have hCS := Real.sum_mul_le_sqrt_mul_sqrt S
    (fun _ : ℕ ↦ (1 : ℝ))
    (fun q ↦ 1 / Real.sqrt ((q / d : ℕ) : ℝ))
  have hsq :
      (∑ q ∈ S, (1 / Real.sqrt ((q / d : ℕ) : ℝ)) ^ 2) =
        ∑ q ∈ S, 1 / ((q / d : ℕ) : ℝ) := by
    apply Finset.sum_congr rfl
    intro q hq
    rw [div_pow, one_pow, Real.sq_sqrt (by positivity)]
  have hcard : (S.card : ℝ) ≤ L := by
    have hc := Finset.card_le_card (show S ⊆ Finset.range L by
      intro q hq
      exact Finset.mem_range.mpr
        (Finset.mem_Ioo.mp (Finset.mem_filter.mp hq).1).2)
    simpa using hc
  have hsum :=
    RiemannZeta.GuthMaynard.sum_Ioo_filter_dvd_one_div_quotient_le_harmonic
      0 L d hd
  change (∑ q ∈ S, Real.sqrt d / Real.sqrt q) ≤ _
  calc
    ∑ q ∈ S, Real.sqrt d / Real.sqrt q =
        ∑ q ∈ S, 1 / Real.sqrt ((q / d : ℕ) : ℝ) := by
          apply Finset.sum_congr rfl
          exact hterm
    _ = ∑ q ∈ S, (1 : ℝ) *
        (1 / Real.sqrt ((q / d : ℕ) : ℝ)) := by simp
    _ ≤ Real.sqrt (∑ _q ∈ S, (1 : ℝ) ^ 2) *
        Real.sqrt (∑ q ∈ S,
          (1 / Real.sqrt ((q / d : ℕ) : ℝ)) ^ 2) := hCS
    _ = Real.sqrt (S.card : ℝ) *
        Real.sqrt (∑ q ∈ S, 1 / ((q / d : ℕ) : ℝ)) := by
          rw [hsq]
          simp
    _ ≤ Real.sqrt L * Real.sqrt (((harmonic L : ℚ) : ℝ)) := by
      gcongr

example (H q : ℕ) (hH : H ≠ 0) :
    Real.sqrt (Nat.gcd H q) ≤
      ∑ d ∈ H.divisors, if d ∣ q then Real.sqrt d else 0 := by
  let g := Nat.gcd H q
  have hgH : g ∈ H.divisors := Nat.mem_divisors.mpr
    ⟨Nat.gcd_dvd_left H q, hH⟩
  have hgq : g ∣ q := Nat.gcd_dvd_right H q
  calc
    Real.sqrt (Nat.gcd H q) = if g ∣ q then Real.sqrt g else 0 := by
      simp [g, hgq]
    _ ≤ ∑ d ∈ H.divisors, if d ∣ q then Real.sqrt d else 0 := by
      refine Finset.single_le_sum (s := H.divisors)
        (f := fun d ↦ if d ∣ q then Real.sqrt d else 0) ?_ hgH
      intro d hd
      dsimp
      split_ifs <;> positivity

example (K L H : ℕ) (hH : H ≠ 0) :
    (∑ q ∈ Finset.Ioo K L,
        Real.sqrt (Nat.gcd H q) / Real.sqrt q) ≤
      (H.divisors.card : ℝ) * Real.sqrt L *
        Real.sqrt (((harmonic L : ℚ) : ℝ)) := by
  calc
    ∑ q ∈ Finset.Ioo K L,
        Real.sqrt (Nat.gcd H q) / Real.sqrt q ≤
      ∑ q ∈ Finset.Ioo K L,
        (∑ d ∈ H.divisors, if d ∣ q then Real.sqrt d else 0) /
          Real.sqrt q := by
      apply Finset.sum_le_sum
      intro q hq
      gcongr
      exact RiemannZeta.GuthMaynard.sqrt_gcd_le_sum_divisors_filter_dvd H q hH
    _ = ∑ d ∈ H.divisors, ∑ q ∈ Finset.Ioo K L,
        if d ∣ q then Real.sqrt d / Real.sqrt q else 0 := by
      simp_rw [Finset.sum_div]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q hq
      apply Finset.sum_congr rfl
      intro d hd
      split_ifs <;> simp
    _ ≤ ∑ _d ∈ H.divisors,
        Real.sqrt L * Real.sqrt (((harmonic L : ℚ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro d hd
      exact RiemannZeta.GuthMaynard.sum_Ioo_dvd_sqrt_div_sqrt_le K L d
        (Nat.pos_of_dvd_of_pos
          (Nat.dvd_of_mem_divisors hd) (Nat.pos_of_ne_zero hH))
    _ = (H.divisors.card : ℝ) * Real.sqrt L *
        Real.sqrt (((harmonic L : ℚ) : ℝ)) := by
      simp
      ring

example (L H : ℕ) (hH : H ≠ 0) (δ : ℝ) (hδ : 0 < δ) :
    (∑ q ∈ Finset.Ioo 0 L,
        (Real.sqrt (Nat.gcd H q) / Real.sqrt q) *
          (q.divisors.card : ℝ)) ≤
      RiemannZeta.GuthMaynard.divisorEpsilonConstant δ *
        max 1 ((L : ℝ) ^ δ) *
        ((H.divisors.card : ℝ) * Real.sqrt L *
          Real.sqrt (((harmonic L : ℚ) : ℝ))) := by
  let D := RiemannZeta.GuthMaynard.divisorEpsilonConstant δ *
    max 1 ((L : ℝ) ^ δ)
  have hD : 0 ≤ D := by
    dsimp [D]
    exact mul_nonneg
      (RiemannZeta.GuthMaynard.divisorEpsilonConstant_pos δ).le
      (zero_le_one.trans (le_max_left 1 ((L : ℝ) ^ δ)))
  calc
    ∑ q ∈ Finset.Ioo 0 L,
        (Real.sqrt (Nat.gcd H q) / Real.sqrt q) *
          (q.divisors.card : ℝ) ≤
      ∑ q ∈ Finset.Ioo 0 L,
        (Real.sqrt (Nat.gcd H q) / Real.sqrt q) * D := by
      apply Finset.sum_le_sum
      intro q hq
      have hqPos := (Finset.mem_Ioo.mp hq).1
      have hqLt := (Finset.mem_Ioo.mp hq).2
      have hdiv :=
        RiemannZeta.GuthMaynard.card_divisors_le_const_mul_rpow hδ hqPos.ne'
      have hqL : (q : ℝ) ^ δ ≤ max 1 ((L : ℝ) ^ δ) := by
        apply le_max_of_le_right
        exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hqLt.le) hδ.le
      gcongr
      exact hdiv.trans (mul_le_mul_of_nonneg_left hqL
        (RiemannZeta.GuthMaynard.divisorEpsilonConstant_pos δ).le)
    _ = D * (∑ q ∈ Finset.Ioo 0 L,
        Real.sqrt (Nat.gcd H q) / Real.sqrt q) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ ≤ D * ((H.divisors.card : ℝ) * Real.sqrt L *
        Real.sqrt (((harmonic L : ℚ) : ℝ))) := by
      gcongr
      exact RiemannZeta.GuthMaynard.sum_Ioo_sqrt_gcd_div_sqrt_le 0 L H hH
    _ = _ := by rfl

example (a q : ℕ) [NeZero q] (ha : 0 < a) :
    ((RiemannZeta.GuthMaynard.dfiReducedModulus a q).denominator : ℝ) ^
        (-(1 / 2 : ℝ)) ≤ Real.sqrt a / Real.sqrt q := by
  let R := RiemannZeta.GuthMaynard.dfiReducedModulus a q
  have hq : 0 < q := NeZero.pos q
  have hden : 0 < R.denominator := R.denominator_pos
  have hg : R.gcd ≤ a := Nat.gcd_le_left q ha
  have hrec : R.gcd * R.denominator = q := R.denominator_reconstruct
  have hdenR : (0 : ℝ) < R.denominator := by exact_mod_cast hden
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hEq : Real.sqrt q = Real.sqrt R.gcd * Real.sqrt R.denominator := by
    rw [← Real.sqrt_mul (Nat.cast_nonneg R.gcd)]
    congr 1
    exact_mod_cast hrec.symm
  rw [Real.rpow_neg (Nat.cast_nonneg R.denominator), ← Real.sqrt_eq_rpow]
  have hsqrtg : Real.sqrt R.gcd ≤ Real.sqrt a := by
    exact Real.sqrt_le_sqrt (by exact_mod_cast hg)
  have hsqrtDen : 0 < Real.sqrt R.denominator := Real.sqrt_pos.2 hdenR
  calc
    (Real.sqrt R.denominator)⁻¹ =
        Real.sqrt R.gcd / (Real.sqrt R.gcd * Real.sqrt R.denominator) := by
      by_cases hg0 : R.gcd = 0
      · have : q = 0 := by simpa [hg0] using hrec.symm
        exact (NeZero.ne q this).elim
      field_simp
    _ ≤ Real.sqrt a / (Real.sqrt R.gcd * Real.sqrt R.denominator) := by
      gcongr
    _ = Real.sqrt a / Real.sqrt q := by rw [← hEq]

example (a q : ℕ) [NeZero q] (ha : 0 < a) :
    (((RiemannZeta.GuthMaynard.dfiReducedModulus a q).denominator : ℝ)⁻¹) ≤
      (a : ℝ) / q := by
  let R := RiemannZeta.GuthMaynard.dfiReducedModulus a q
  have hq : 0 < q := NeZero.pos q
  have hg : R.gcd ≤ a := Nat.gcd_le_left q ha
  have hrec : R.gcd * R.denominator = q := R.denominator_reconstruct
  have hdenR : (0 : ℝ) < R.denominator := by exact_mod_cast R.denominator_pos
  have hgR : (0 : ℝ) < R.gcd := by exact_mod_cast R.gcd_pos
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hEq : (q : ℝ) = R.gcd * R.denominator := by exact_mod_cast hrec.symm
  calc
    ((R.denominator : ℝ))⁻¹ = (R.gcd : ℝ) / q := by
      rw [hEq]
      field_simp
    _ ≤ (a : ℝ) / q := by
      gcongr

namespace RiemannZeta.GuthMaynard

example {Q : ℝ} (h : ℤ) (hh : h ≠ 0) (δ : ℝ) (hδ : 0 < δ) :
    let L := ⌈2 * Q⌉₊
    (∑ q ∈ dfiEquation22Moduli Q,
        (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
          (q.divisors.card : ℝ)) ≤
      divisorEpsilonConstant δ * max 1 ((L : ℝ) ^ δ) *
        ((h.natAbs.divisors.card : ℝ) * Real.sqrt L *
          Real.sqrt (((harmonic L : ℚ) : ℝ))) := by
  dsimp only
  let L := ⌈2 * Q⌉₊
  have hset : dfiEquation22Moduli Q = Finset.Ioo 0 L := by
    rw [dfiEquation22Moduli_eq_Ico]
    ext q
    simp only [Finset.mem_Ico, Finset.mem_Ioo]
    omega
  rw [hset]
  calc
    ∑ q ∈ Finset.Ioo 0 L,
        (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
          (q.divisors.card : ℝ) =
      ∑ q ∈ Finset.Ioo 0 L,
        (Real.sqrt (Nat.gcd h.natAbs q) / Real.sqrt q) *
          (q.divisors.card : ℝ) := by
      apply Finset.sum_congr rfl
      intro q hq
      have hqPos := (Finset.mem_Ioo.mp hq).1
      letI : NeZero q := ⟨hqPos.ne'⟩
      rw [gcd_neg_intCast_zmod_val q h]
    _ ≤ _ := sum_Ioo_sqrt_gcd_mul_divisors_div_sqrt_le
      L h.natAbs (Int.natAbs_ne_zero.mpr hh) δ hδ

end RiemannZeta.GuthMaynard

namespace RiemannZeta.GuthMaynard

example (q a b : ℕ) [NeZero q] (hab : a.Coprime b) (h : ℤ) :
    (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
        (q.divisors.card : ℝ)) *
        ((dfiReducedModulus a q).denominator : ℝ) ^ (-(1 / 2 : ℝ)) *
        ((dfiReducedModulus b q).denominator : ℝ) ^ (-(1 / 2 : ℝ)) ≤
      Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) *
        (q.divisors.card : ℝ) := by
  have hqN : 0 < q := NeZero.pos q
  have hq : (0 : ℝ) < q := by exact_mod_cast hqN
  have hsqrtq : 0 < Real.sqrt q := Real.sqrt_pos.2 hq
  have hgdvd := gcd_mul_gcd_dvd_right_of_coprime a b q hab
  have hgleN : Nat.gcd a q * Nat.gcd b q ≤ q := Nat.le_of_dvd hqN hgdvd
  have hgle : (Nat.gcd a q : ℝ) * Nat.gcd b q ≤ q := by exact_mod_cast hgleN
  have hsqrtprod :
      Real.sqrt (Nat.gcd a q) * Real.sqrt (Nat.gcd b q) ≤ Real.sqrt q := by
    rw [← Real.sqrt_mul (Nat.cast_nonneg (Nat.gcd a q))]
    exact Real.sqrt_le_sqrt hgle
  rw [dfiReducedModulus_denominator_rpow_neg_half_eq,
    dfiReducedModulus_denominator_rpow_neg_half_eq]
  have hbase : 0 ≤ Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) *
      (q.divisors.card : ℝ) := by positivity
  calc
    _ = (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) *
          (q.divisors.card : ℝ)) *
        ((Real.sqrt (Nat.gcd a q) * Real.sqrt (Nat.gcd b q)) /
          Real.sqrt q) := by field_simp
    _ ≤ (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) *
          (q.divisors.card : ℝ)) * (Real.sqrt q / Real.sqrt q) := by
      gcongr
    _ = _ := by field_simp

example (q a b : ℕ) [NeZero q] (hab : a.Coprime b) (h : ℤ) :
    (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
        (q.divisors.card : ℝ)) *
        ((dfiReducedModulus a q).denominator : ℝ) ^ (-(1 / 2 : ℝ)) *
        ((dfiReducedModulus b q).denominator : ℝ)⁻¹ ≤
      Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) *
        (q.divisors.card : ℝ) := by
  have hqN : 0 < q := NeZero.pos q
  have hq : (0 : ℝ) < q := by exact_mod_cast hqN
  have hsqrtq : 0 < Real.sqrt q := Real.sqrt_pos.2 hq
  have hgdvd := gcd_mul_gcd_dvd_right_of_coprime a b q hab
  have hgleN : Nat.gcd a q * Nat.gcd b q ≤ q := Nat.le_of_dvd hqN hgdvd
  have hgaPos : 0 < Nat.gcd a q := Nat.gcd_pos_of_pos_right a hqN
  have hsqrtga_le : Real.sqrt (Nat.gcd a q) ≤ Nat.gcd a q := by
    have hone : (1 : ℝ) ≤ Nat.gcd a q := by exact_mod_cast hgaPos
    nlinarith [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ Nat.gcd a q),
      Real.sqrt_nonneg (Nat.gcd a q)]
  have hprod : Real.sqrt (Nat.gcd a q) * Nat.gcd b q ≤ q := by
    calc
      _ ≤ (Nat.gcd a q : ℝ) * Nat.gcd b q := by gcongr
      _ ≤ q := by exact_mod_cast hgleN
  rw [dfiReducedModulus_denominator_rpow_neg_half_eq,
    dfiReducedModulus_denominator_inv_eq]
  have hbase : 0 ≤ Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) *
      (q.divisors.card : ℝ) := by positivity
  calc
    _ = (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) *
          (q.divisors.card : ℝ)) *
        ((Real.sqrt (Nat.gcd a q) * Nat.gcd b q) / q) := by field_simp
    _ ≤ (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) *
          (q.divisors.card : ℝ)) * ((q : ℝ) / q) := by gcongr
    _ = _ := by field_simp

end RiemannZeta.GuthMaynard

namespace RiemannZeta.GuthMaynard

example (a b q : ℕ) (hab : a.Coprime b) :
    Nat.gcd a q * Nat.gcd b q ∣ q := by
  simpa [Nat.gcd_comm] using
    (hab.gcd_both q q).mul_dvd_of_dvd_of_dvd
      (Nat.gcd_dvd_left q a) (Nat.gcd_dvd_left q b)

example (a q : ℕ) [NeZero q] :
    ((dfiReducedModulus a q).denominator : ℝ) ^ (-(1 / 2 : ℝ)) =
      Real.sqrt (Nat.gcd a q) / Real.sqrt q := by
  let R := dfiReducedModulus a q
  have hdenR : (0 : ℝ) < R.denominator := by exact_mod_cast R.denominator_pos
  have hEq : Real.sqrt q = Real.sqrt R.gcd * Real.sqrt R.denominator := by
    rw [← Real.sqrt_mul (Nat.cast_nonneg R.gcd)]
    congr 1
    exact_mod_cast R.denominator_reconstruct.symm
  rw [Real.rpow_neg (Nat.cast_nonneg R.denominator), ← Real.sqrt_eq_rpow]
  change (Real.sqrt R.denominator)⁻¹ = Real.sqrt R.gcd / Real.sqrt q
  rw [hEq]
  have hg : 0 < Real.sqrt R.gcd := Real.sqrt_pos.2 (by exact_mod_cast R.gcd_pos)
  have hd : 0 < Real.sqrt R.denominator := Real.sqrt_pos.2 hdenR
  field_simp

end RiemannZeta.GuthMaynard

namespace RiemannZeta.GuthMaynard

example (q a b : ℕ) [NeZero q] (ha : 0 < a) (hb : 0 < b) (h : ℤ) :
    (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
        (q.divisors.card : ℝ)) *
        ((dfiReducedModulus a q).denominator : ℝ) ^ (-(1 / 2 : ℝ)) *
        ((dfiReducedModulus b q).denominator : ℝ)⁻¹ ≤
      Real.sqrt a * b *
        ((Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
          (q.divisors.card : ℝ)) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hsqrtq : 0 < Real.sqrt q := Real.sqrt_pos.2 hq
  have hsquare : Real.sqrt q * Real.sqrt q = (q : ℝ) := by
    rw [← pow_two, Real.sq_sqrt hq.le]
  have hqOne : (1 : ℝ) ≤ q := by
    exact_mod_cast (NeZero.one_le : 1 ≤ q)
  have hsqrt_le_q : Real.sqrt q ≤ (q : ℝ) := by
    nlinarith [Real.sqrt_nonneg (q : ℝ)]
  have hx := dfiReducedModulus_denominator_rpow_neg_half_le a q ha
  have hy := dfiReducedModulus_denominator_inv_le b q hb
  calc
    _ ≤ (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
        (q.divisors.card : ℝ)) *
        (Real.sqrt a / Real.sqrt q) * ((b : ℝ) / q) := by
      gcongr
    _ = Real.sqrt a * b *
        ((Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / q) *
          (q.divisors.card : ℝ)) := by
      field_simp
    _ ≤ _ := by
      gcongr

example (q a b : ℕ) [NeZero q] (ha : 0 < a) (hb : 0 < b) (h : ℤ) :
    (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
        (q.divisors.card : ℝ)) *
        ((dfiReducedModulus a q).denominator : ℝ) ^ (-(1 / 2 : ℝ)) *
        ((dfiReducedModulus b q).denominator : ℝ) ^ (-(1 / 2 : ℝ)) ≤
      Real.sqrt a * Real.sqrt b *
        ((Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
          (q.divisors.card : ℝ)) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hsqrtq : 0 < Real.sqrt q := Real.sqrt_pos.2 hq
  have hsquare : Real.sqrt q * Real.sqrt q = (q : ℝ) := by
    rw [← pow_two, Real.sq_sqrt hq.le]
  have hx := dfiReducedModulus_denominator_rpow_neg_half_le a q ha
  have hy := dfiReducedModulus_denominator_rpow_neg_half_le b q hb
  calc
    _ ≤ (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
        (q.divisors.card : ℝ)) *
        (Real.sqrt a / Real.sqrt q) * (Real.sqrt b / Real.sqrt q) := by
      gcongr
    _ = _ := by
      field_simp

example (q a b : ℕ) [NeZero q] (ha : 0 < a) (hb : 0 < b) (h : ℤ) :
    (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) * Real.sqrt q *
        (q.divisors.card : ℝ)) *
        ((dfiReducedModulus a q).denominator : ℝ) ^ (-(1 / 2 : ℝ)) *
        ((dfiReducedModulus b q).denominator : ℝ)⁻¹ *
        (a : ℝ) * (((a : ℝ) * b)⁻¹) ≤
      (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) / Real.sqrt q) *
        (q.divisors.card : ℝ) := by
  have hqN : 0 < q := NeZero.pos q
  have hq : (0 : ℝ) < q := by exact_mod_cast hqN
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hsqrtq : 0 < Real.sqrt q := Real.sqrt_pos.2 hq
  have hga : Nat.gcd a q ≤ q := Nat.gcd_le_right a hqN
  have hgb : Nat.gcd b q ≤ b := Nat.gcd_le_left q hb
  have hsqrtga : Real.sqrt (Nat.gcd a q) ≤ Real.sqrt q :=
    Real.sqrt_le_sqrt (by exact_mod_cast hga)
  have hgbR : (Nat.gcd b q : ℝ) ≤ b := by exact_mod_cast hgb
  rw [dfiReducedModulus_denominator_rpow_neg_half_eq,
    dfiReducedModulus_denominator_inv_eq]
  have hbase : 0 ≤ Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) *
      (q.divisors.card : ℝ) := by positivity
  calc
    _ = (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) *
          (q.divisors.card : ℝ)) *
        ((Real.sqrt (Nat.gcd a q) / Real.sqrt q) *
          ((Nat.gcd b q : ℝ) / b) * (Real.sqrt q)⁻¹) := by
      field_simp
      rw [Real.sq_sqrt hq.le]
      ring
    _ ≤ (Real.sqrt (Nat.gcd ((-h : ZMod q).val) q) *
          (q.divisors.card : ℝ)) *
        ((Real.sqrt q / Real.sqrt q) * ((b : ℝ) / b) *
          (Real.sqrt q)⁻¹) := by gcongr
    _ = _ := by field_simp

end RiemannZeta.GuthMaynard
