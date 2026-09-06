import GafniTao.HeathBrownAtkinsonPhase

open Real
open GafniTao

noncomputable section

def hbQ (T : ℝ) (n : ℕ) : ℝ := Real.pi * (n : ℝ) / (2 * T)

def hbX (T : ℝ) (n : ℕ) : ℝ := Real.sqrt (hbQ T n)

def hbPhaseNorm (T : ℝ) (n : ℕ) : ℝ :=
  2 * T * (Real.arsinh (hbX T n) +
    hbX T n * Real.sqrt (1 + (hbX T n) ^ 2)) - Real.pi / 4

example {T : ℝ} {n : ℕ} (hT : 0 < T) :
    HasDerivAt (fun u => hbQ u n) (-(hbQ T n) / T) T := by
  unfold hbQ
  convert ((hasDerivAt_const T (Real.pi * (n : ℝ))).div
    ((hasDerivAt_id T).const_mul 2) (by positivity : 2 * T ≠ 0)) using 1
  · simp only [id_eq]
    field_simp [hT.ne']
    ring

example {T : ℝ} {n : ℕ} (hT : 0 < T) (hn : 0 < n) :
    HasDerivAt (fun u => hbX u n) (-(hbX T n) / (2 * T)) T := by
  have hq : 0 < hbQ T n := by unfold hbQ; positivity
  have hq' : HasDerivAt (fun u => hbQ u n) (-(hbQ T n) / T) T := by
    unfold hbQ
    convert ((hasDerivAt_const T (Real.pi * (n : ℝ))).div
      ((hasDerivAt_id T).const_mul 2) (by positivity : 2 * T ≠ 0)) using 1
    · simp only [id_eq]
      field_simp [hT.ne']
      ring
  have hs := hq'.sqrt hq.ne'
  unfold hbX
  convert hs using 1
  have hsquare := Real.sq_sqrt hq.le
  field_simp [hT.ne', (Real.sqrt_pos.2 hq).ne']
  nlinarith

example {T : ℝ} {n : ℕ} (hT : 0 < T) (hn : 0 < n) :
    HasDerivAt (fun u => hbPhaseNorm u n)
      (2 * Real.arsinh (hbX T n)) T := by
  have hq : 0 < hbQ T n := by unfold hbQ; positivity
  have hx : HasDerivAt (fun u => hbX u n)
      (-(hbX T n) / (2 * T)) T := by
    have hq' : HasDerivAt (fun u => hbQ u n) (-(hbQ T n) / T) T := by
      unfold hbQ
      convert ((hasDerivAt_const T (Real.pi * (n : ℝ))).div
        ((hasDerivAt_id T).const_mul 2) (by positivity : 2 * T ≠ 0)) using 1
      · simp only [id_eq]
        field_simp [hT.ne']
        ring
    have hs0 := hq'.sqrt hq.ne'
    unfold hbX
    convert hs0 using 1
    have hsquare := Real.sq_sqrt hq.le
    field_simp [hT.ne', (Real.sqrt_pos.2 hq).ne']
    nlinarith
  let x : ℝ := hbX T n
  let xp : ℝ := -x / (2 * T)
  let s : ℝ := Real.sqrt (1 + x ^ 2)
  let sp : ℝ := (xp * x + x * xp) / (2 * s)
  have hx' : HasDerivAt (fun u => hbX u n) xp T := by
    simpa only [x, xp] using hx
  have hspos : 0 < s := by dsimp only [s, x]; positivity
  have hinside : HasDerivAt
      (fun u => 1 + hbX u n * hbX u n)
      (xp * x + x * xp) T := by
    simpa only [zero_add, x] using
      (hasDerivAt_const T (1 : ℝ)).add (hx'.mul hx')
  have hs : HasDerivAt
      (fun u => Real.sqrt (1 + (hbX u n) ^ 2)) sp T := by
    have hne : 1 + hbX T n * hbX T n ≠ 0 := by
      have hsquare := sq_nonneg (hbX T n)
      nlinarith
    have hs0 := hinside.sqrt hne
    simpa only [pow_two, sp, s, x] using hs0
  have hsum : HasDerivAt
      (fun u => Real.arsinh (hbX u n) +
        hbX u n * Real.sqrt (1 + (hbX u n) ^ 2))
      (s⁻¹ * xp + (xp * s + x * sp)) T := by
    simpa only [x, s, sp] using hx'.arsinh.add (hx'.mul hs)
  have htwoT : HasDerivAt (fun u : ℝ => 2 * u) 2 T := by
    simpa only [mul_one] using (hasDerivAt_id T).const_mul 2
  have hsub := (htwoT.mul hsum).sub (hasDerivAt_const T (Real.pi / 4))
  have hsub' : HasDerivAt (fun u => hbPhaseNorm u n)
      (2 * (Real.arsinh x + x * s) +
        2 * T * (s⁻¹ * xp + (xp * s + x * sp)) - 0) T := by
    convert hsub using 1
  have hsquare : s ^ 2 = 1 + x ^ 2 := by
    dsimp only [s]
    exact Real.sq_sqrt (by positivity)
  have halg :
      2 * (Real.arsinh x + x * s) +
          2 * T * (s⁻¹ * xp + (xp * s + x * sp)) - 0 =
        2 * Real.arsinh x := by
    dsimp only [xp, sp]
    field_simp [hT.ne', hspos.ne']
    linear_combination 2 * x * hsquare
  exact hsub'.congr_deriv halg

example {T : ℝ} {n : ℕ} (hT : 0 < T) (hn : 0 < n) :
    HasDerivAt (fun u => 2 * Real.arsinh (hbX u n))
      (-hbX T n / (T * Real.sqrt (1 + (hbX T n) ^ 2))) T := by
  have hq : 0 < hbQ T n := by unfold hbQ; positivity
  have hq' : HasDerivAt (fun u => hbQ u n) (-(hbQ T n) / T) T := by
    unfold hbQ
    convert ((hasDerivAt_const T (Real.pi * (n : ℝ))).div
      ((hasDerivAt_id T).const_mul 2) (by positivity : 2 * T ≠ 0)) using 1
    simp only [id_eq]
    field_simp [hT.ne']
    ring
  have hs0 := hq'.sqrt hq.ne'
  have hx : HasDerivAt (fun u => hbX u n)
      (-(hbX T n) / (2 * T)) T := by
    unfold hbX
    convert hs0 using 1
    have hsquare := Real.sq_sqrt hq.le
    field_simp [hT.ne', (Real.sqrt_pos.2 hq).ne']
    nlinarith
  have h := hx.arsinh.const_mul 2
  have hspos : 0 < Real.sqrt (1 + hbX T n ^ 2) := by positivity
  have halg :
      2 * (Real.sqrt (1 + hbX T n ^ 2))⁻¹ *
          (-hbX T n / (2 * T)) =
        -hbX T n / (T * Real.sqrt (1 + hbX T n ^ 2)) := by
    field_simp [hT.ne', hspos.ne']
    ring
  simpa only [smul_eq_mul, mul_assoc] using h.congr_deriv halg

end
