import RiemannZeta.GuthMaynard.DFIPeriodicBounds

/-! Exact finite-Fourier expansion of the dual Estermann term in DFI
Proposition 1.  This is the algebraic bridge from the periodic functional
equation to the two additive-character Bessel branches. -/

open Complex Finset
open scoped BigOperators
open Classical

namespace RiemannZeta.GuthMaynard

/-- The Fourier transform of the reflected residue indicator. -/
theorem zmod_dft_neg_residueIndicator (q : ℕ) [NeZero q]
    (a k : ZMod q) :
    ZMod.dft (fun x : ZMod q => if -x = a then 1 else 0) k =
      ZMod.stdAddChar (a * k) := by
  have hfun : (fun x : ZMod q => if -x = a then (1 : ℂ) else 0) =
      fun x : ZMod q => if x = -a then 1 else 0 := by
    funext x
    by_cases h : x = -a
    · subst x
      simp
    · have hn : -x ≠ a := by
        intro hx
        apply h
        simpa using congrArg Neg.neg hx
      simp [h, hn]
  rw [hfun, zmod_dft_residueIndicator]
  congr 1
  ring

/-- A Fourier-transformed residue-class L-function is the exact finite
linear combination of residue-class L-functions with additive-character
coefficients. -/
theorem LFunction_residueIndicator (q : ℕ) [NeZero q]
    (k : ZMod q) (s : ℂ) :
    ZMod.LFunction (fun x : ZMod q => if x = k then 1 else 0) s =
      (q : ℂ) ^ (-s) * HurwitzZeta.hurwitzZeta (ZMod.toAddCircle k) s := by
  unfold ZMod.LFunction
  simp

theorem LFunction_dft_residueIndicator (q : ℕ) [NeZero q]
    (a : ZMod q) (s : ℂ) :
    ZMod.LFunction (ZMod.dft (fun x : ZMod q => if x = a then 1 else 0)) s =
      ∑ k : ZMod q, ZMod.stdAddChar (-(a * k)) *
        ZMod.LFunction (fun x : ZMod q => if x = k then 1 else 0) s := by
  have hdft : ZMod.dft (fun x : ZMod q => if x = a then (1 : ℂ) else 0) =
      fun k => ZMod.stdAddChar (-(a * k)) := by
    funext k
    exact zmod_dft_residueIndicator q a k
  rw [hdft]
  simp_rw [LFunction_residueIndicator]
  unfold ZMod.LFunction
  rw [Finset.mul_sum]
  ring_nf

/-- The corresponding expansion for the reflected indicator. -/
theorem LFunction_dft_neg_residueIndicator (q : ℕ) [NeZero q]
    (a : ZMod q) (s : ℂ) :
    ZMod.LFunction
        (ZMod.dft (fun x : ZMod q => if -x = a then 1 else 0)) s =
      ∑ k : ZMod q, ZMod.stdAddChar (a * k) *
        ZMod.LFunction (fun x : ZMod q => if x = k then 1 else 0) s := by
  have hdft : ZMod.dft (fun x : ZMod q => if -x = a then (1 : ℂ) else 0) =
      fun k => ZMod.stdAddChar (a * k) := by
    funext k
    exact zmod_dft_neg_residueIndicator q a k
  rw [hdft]
  simp_rw [LFunction_residueIndicator]
  unfold ZMod.LFunction
  rw [Finset.mul_sum]
  ring_nf

private theorem isUnit_mul_eq_zero_iff' {R : Type*} [MonoidWithZero R]
    {a b : R} (ha : IsUnit a) : a * b = 0 ↔ b = 0 := by
  constructor
  · intro h
    apply ha.mul_left_cancel
    simpa using h
  · rintro rfl
    exact mul_zero a

/-- The complete two-variable finite character sum.  The signs are left as
arbitrary residues; the four choices `±m, ±n` are its DFI applications. -/
theorem sum_voronoiCharacter_three_linear (q : ℕ) [NeZero q]
    (d : ZMod q) (hd : IsUnit d) (m n : ZMod q) :
    ∑ a : ZMod q, ∑ b : ZMod q,
        ZMod.stdAddChar (d * a * b) * ZMod.stdAddChar (a * m) *
          ZMod.stdAddChar (b * n) =
      (q : ℂ) * ZMod.stdAddChar (-(d⁻¹ * m * n)) := by
  calc
    ∑ a : ZMod q, ∑ b : ZMod q,
        ZMod.stdAddChar (d * a * b) * ZMod.stdAddChar (a * m) *
          ZMod.stdAddChar (b * n) =
      ∑ a : ZMod q, ZMod.stdAddChar (a * m) *
        (∑ b : ZMod q, ZMod.stdAddChar (b * (d * a + n))) := by
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro b _
          have hchar :
              ZMod.stdAddChar (d * a * b) * ZMod.stdAddChar (b * n) =
                ZMod.stdAddChar (b * (d * a + n)) := by
            rw [← ZMod.stdAddChar.map_add_eq_mul]
            congr 1
            ring
          rw [show ZMod.stdAddChar (d * a * b) * ZMod.stdAddChar (a * m) *
              ZMod.stdAddChar (b * n) =
                ZMod.stdAddChar (a * m) *
                  (ZMod.stdAddChar (d * a * b) * ZMod.stdAddChar (b * n)) by ring,
            hchar]
    _ = ∑ a : ZMod q, ZMod.stdAddChar (a * m) *
        (if d * a + n = 0 then (q : ℂ) else 0) := by
          apply Finset.sum_congr rfl
          intro a _
          rw [AddChar.sum_mulShift (d * a + n) (ZMod.isPrimitive_stdAddChar q)]
          simp [ZMod.card]
    _ = (q : ℂ) * ZMod.stdAddChar (-(d⁻¹ * m * n)) := by
      have hdinv : d * d⁻¹ = 1 := ZMod.mul_inv_of_unit d hd
      have hroot : d * (-(d⁻¹ * n)) + n = 0 := by
        rw [mul_neg, ← mul_assoc, hdinv, one_mul]
        exact neg_add_cancel n
      have hiff (a : ZMod q) : d * a + n = 0 ↔ a = -(d⁻¹ * n) := by
        constructor
        · intro h
          have hmul : d * (a + d⁻¹ * n) = 0 := by
            calc
              d * (a + d⁻¹ * n) = d * a + n := by
                rw [mul_add, ← mul_assoc, hdinv, one_mul]
              _ = 0 := h
          have := (isUnit_mul_eq_zero_iff' hd).mp hmul
          exact eq_neg_of_add_eq_zero_left this
        · rintro rfl
          exact hroot
      simp_rw [hiff]
      simp
      rw [show -(d⁻¹ * n * m) = -(d⁻¹ * m * n) by ring]
      ring

/-- Orthogonality after both finite Fourier expansions.  This is stated for
arbitrary residue multipliers so all four sign choices in the product of the
two periodic functional equations are instances of one theorem. -/
theorem sum_voronoiCharacter_fourier_products (q : ℕ) [NeZero q]
    (d : ZMod q) (hd : IsUnit d) (r t : ZMod q)
    (A B : ZMod q → ℂ) :
    ∑ a : ZMod q, ∑ b : ZMod q,
        dfiVoronoiCharacter q d (a * b) *
          (∑ m : ZMod q, ZMod.stdAddChar (a * (r * m)) * A m) *
          (∑ n : ZMod q, ZMod.stdAddChar (b * (t * n)) * B n) =
      (q : ℂ) * ∑ m : ZMod q, ∑ n : ZMod q,
        dfiVoronoiCharacter q (-(d⁻¹ * r * t)) (m * n) * A m * B n := by
  let F : ZMod q → ZMod q → ZMod q → ZMod q → ℂ := fun a b m n =>
    (ZMod.stdAddChar (d * a * b) *
      ZMod.stdAddChar (a * (r * m)) *
      ZMod.stdAddChar (b * (t * n))) * A m * B n
  calc
    ∑ a : ZMod q, ∑ b : ZMod q,
        dfiVoronoiCharacter q d (a * b) *
          (∑ m : ZMod q, ZMod.stdAddChar (a * (r * m)) * A m) *
          (∑ n : ZMod q, ZMod.stdAddChar (b * (t * n)) * B n) =
      ∑ a : ZMod q, ∑ b : ZMod q, ∑ m : ZMod q, ∑ n : ZMod q,
        F a b m n := by
            apply Finset.sum_congr rfl
            intro a _
            apply Finset.sum_congr rfl
            intro b _
            unfold dfiVoronoiCharacter F
            calc
              ZMod.stdAddChar (d * (a * b)) *
                    (∑ m, ZMod.stdAddChar (a * (r * m)) * A m) *
                    (∑ n, ZMod.stdAddChar (b * (t * n)) * B n) =
                  (∑ m, ZMod.stdAddChar (d * (a * b)) *
                    (ZMod.stdAddChar (a * (r * m)) * A m)) *
                    (∑ n, ZMod.stdAddChar (b * (t * n)) * B n) := by
                      congr 1
                      rw [Finset.mul_sum]
              _ = ∑ m, (ZMod.stdAddChar (d * (a * b)) *
                    (ZMod.stdAddChar (a * (r * m)) * A m)) *
                    (∑ n, ZMod.stdAddChar (b * (t * n)) * B n) := by
                      rw [Finset.sum_mul]
              _ = ∑ m, ∑ n, (ZMod.stdAddChar (d * (a * b)) *
                    (ZMod.stdAddChar (a * (r * m)) * A m)) *
                    (ZMod.stdAddChar (b * (t * n)) * B n) := by
                      apply Finset.sum_congr rfl
                      intro m _
                      rw [Finset.mul_sum]
              _ = ∑ m, ∑ n, (ZMod.stdAddChar (d * a * b) *
                    ZMod.stdAddChar (a * (r * m)) *
                    ZMod.stdAddChar (b * (t * n))) * A m * B n := by
                      apply Finset.sum_congr rfl
                      intro m _
                      apply Finset.sum_congr rfl
                      intro n _
                      ring_nf
    _ = ∑ a : ZMod q, ∑ m : ZMod q, ∑ b : ZMod q, ∑ n : ZMod q,
        F a b m n := by
            apply Finset.sum_congr rfl
            intro a _
            rw [Finset.sum_comm]
    _ = ∑ m : ZMod q, ∑ a : ZMod q, ∑ b : ZMod q, ∑ n : ZMod q,
        F a b m n := by
            rw [Finset.sum_comm]
    _ = ∑ m : ZMod q, ∑ a : ZMod q, ∑ n : ZMod q, ∑ b : ZMod q,
        F a b m n := by
            apply Finset.sum_congr rfl
            intro m _
            apply Finset.sum_congr rfl
            intro a _
            rw [Finset.sum_comm]
    _ = ∑ m : ZMod q, ∑ n : ZMod q, ∑ a : ZMod q, ∑ b : ZMod q,
        F a b m n := by
            apply Finset.sum_congr rfl
            intro m _
            rw [Finset.sum_comm]
    _ = ∑ m : ZMod q, ∑ n : ZMod q,
        ((q : ℂ) * ZMod.stdAddChar
          (-(d⁻¹ * (r * m) * (t * n)))) * A m * B n := by
            apply Finset.sum_congr rfl
            intro m _
            apply Finset.sum_congr rfl
            intro n _
            unfold F
            calc
              (∑ a, ∑ b,
                  (ZMod.stdAddChar (d * a * b) *
                    ZMod.stdAddChar (a * (r * m)) *
                    ZMod.stdAddChar (b * (t * n))) * A m * B n) =
                (∑ a, ∑ b,
                  ZMod.stdAddChar (d * a * b) *
                    ZMod.stdAddChar (a * (r * m)) *
                    ZMod.stdAddChar (b * (t * n))) * (A m * B n) := by
                      rw [Finset.sum_mul]
                      apply Finset.sum_congr rfl
                      intro a _
                      rw [Finset.sum_mul]
                      apply Finset.sum_congr rfl
                      intro b _
                      ring
              _ = ((q : ℂ) * ZMod.stdAddChar
                    (-(d⁻¹ * (r * m) * (t * n)))) * A m * B n := by
                      rw [sum_voronoiCharacter_three_linear q d hd
                        (r * m) (t * n)]
                      ring
    _ = (q : ℂ) * ∑ m : ZMod q, ∑ n : ZMod q,
        dfiVoronoiCharacter q (-(d⁻¹ * r * t)) (m * n) * A m * B n := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro m _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro n _
            unfold dfiVoronoiCharacter
            have harg : -(d⁻¹ * (r * m) * (t * n)) =
                -(d⁻¹ * r * t) * (m * n) := by ring
            rw [harg]
            ring

/-- The residue-class L-function appearing after the right-half-plane
Dirichlet-series expansion. -/
noncomputable def dfiResidueL (q : ℕ) [NeZero q]
    (s : ℂ) (m : ZMod q) : ℂ :=
  ZMod.LFunction (fun x : ZMod q => if x = m then 1 else 0) s

/-- One of the two signed finite Fourier branches in the reflected
periodic L-function. -/
noncomputable def dfiFourierBranch (q : ℕ) [NeZero q]
    (s : ℂ) (r a : ZMod q) : ℂ :=
  ∑ m : ZMod q, ZMod.stdAddChar (a * (r * m)) * dfiResidueL q s m

/-- The common Gamma and scaling factor in a periodic L-function's
functional equation. -/
noncomputable def dfiPeriodicArchimedeanFactor (q : ℕ) [NeZero q]
    (s : ℂ) : ℂ :=
  (q : ℂ) ^ (s - 1) * (2 * Real.pi : ℂ) ^ (-s) * Gamma s

/-- The common Voronoi archimedean factor is holomorphic in the positive
half-plane.  This is the pole-free region traversed when the dual Mellin
contour is shifted to the left. -/
theorem differentiableAt_dfiPeriodicArchimedeanFactor_of_re_pos
    (q : ℕ) [NeZero q] {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (dfiPeriodicArchimedeanFactor q) s := by
  have hq : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hpi : (2 * Real.pi : ℂ) ≠ 0 :=
    mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hGamma : DifferentiableAt ℂ Gamma s :=
    Complex.differentiableAt_Gamma s (fun m hm => by
      have hre := congrArg Complex.re hm
      norm_num at hre
      linarith)
  exact (((differentiableAt_id.sub_const 1).const_cpow (Or.inl hq)).mul
    (differentiableAt_id.neg.const_cpow (Or.inl hpi))).mul hGamma

theorem periodicLFunctionDual_indicator_eq_branches (q : ℕ) [NeZero q]
    (a : ZMod q) (s : ℂ) :
    periodicLFunctionDual q (fun x : ZMod q => if x = a then 1 else 0) s =
      dfiPeriodicArchimedeanFactor q s *
        (cexp (Real.pi * I * s / 2) *
            dfiFourierBranch q s (-1) a +
          cexp (-Real.pi * I * s / 2) *
            dfiFourierBranch q s 1 a) := by
  unfold periodicLFunctionDual dfiPeriodicArchimedeanFactor dfiFourierBranch
    dfiResidueL
  rw [LFunction_dft_residueIndicator, LFunction_dft_neg_residueIndicator]
  congr 3
  · apply Finset.sum_congr rfl
    intro m _
    congr 2
    ring
  · apply Finset.sum_congr rfl
    intro m _
    congr 2
    ring

/-- Each signed pair of finite Fourier branches is exactly the corresponding
dual additive Estermann function. -/
theorem sum_voronoiCharacter_branches (q : ℕ) [NeZero q]
    (d : ZMod q) (hd : IsUnit d) (r t : ZMod q) (s : ℂ) :
    ∑ a : ZMod q, ∑ b : ZMod q,
        dfiVoronoiCharacter q d (a * b) *
          dfiFourierBranch q s r a * dfiFourierBranch q s t b =
      (q : ℂ) * periodicEstermann q
        (dfiVoronoiCharacter q (-(d⁻¹ * r * t))) s := by
  simpa only [dfiFourierBranch, dfiResidueL, periodicEstermann] using
    sum_voronoiCharacter_fourier_products q d hd r t
      (fun m => dfiResidueL q s m) (fun n => dfiResidueL q s n)

/-- Exact additive-character specialization of the dual periodic Estermann
function.  This is the four-branch functional-equation identity immediately
preceding the two DFI Bessel transforms. -/
theorem periodicEstermannDual_voronoiCharacter (q : ℕ) [NeZero q]
    (d : ZMod q) (hd : IsUnit d) (s : ℂ) :
    periodicEstermannDual q (dfiVoronoiCharacter q d) s =
      (q : ℂ) * dfiPeriodicArchimedeanFactor q s ^ 2 *
        ((cexp (Real.pi * I * s) + cexp (-Real.pi * I * s)) *
            periodicEstermann q (dfiVoronoiCharacter q (-d⁻¹)) s +
          2 * periodicEstermann q (dfiVoronoiCharacter q d⁻¹) s) := by
  let C := dfiPeriodicArchimedeanFactor q s
  let ep := cexp (Real.pi * I * s / 2)
  let em := cexp (-Real.pi * I * s / 2)
  let P : ZMod q → ZMod q → ℂ := fun r a => dfiFourierBranch q s r a
  have hepem : ep * em = 1 := by
    dsimp [ep, em]
    rw [← Complex.exp_add]
    ring_nf
    simp
  have hepep : ep * ep = cexp (Real.pi * I * s) := by
    dsimp [ep]
    rw [← Complex.exp_add]
    congr 1
    ring
  have hemem : em * em = cexp (-Real.pi * I * s) := by
    dsimp [em]
    rw [← Complex.exp_add]
    congr 1
    ring
  have hmm := sum_voronoiCharacter_branches q d hd (-1) (-1) s
  have hmp := sum_voronoiCharacter_branches q d hd (-1) 1 s
  have hpm := sum_voronoiCharacter_branches q d hd 1 (-1) s
  have hpp := sum_voronoiCharacter_branches q d hd 1 1 s
  have hmm' :
      (∑ a : ZMod q, ∑ b : ZMod q,
        dfiVoronoiCharacter q d (a * b) * P (-1) a * P (-1) b) =
        (q : ℂ) * periodicEstermann q
          (dfiVoronoiCharacter q (-d⁻¹)) s := by
    simpa [P] using hmm
  have hmp' :
      (∑ a : ZMod q, ∑ b : ZMod q,
        dfiVoronoiCharacter q d (a * b) * P (-1) a * P 1 b) =
        (q : ℂ) * periodicEstermann q
          (dfiVoronoiCharacter q d⁻¹) s := by
    simpa [P] using hmp
  have hpm' :
      (∑ a : ZMod q, ∑ b : ZMod q,
        dfiVoronoiCharacter q d (a * b) * P 1 a * P (-1) b) =
        (q : ℂ) * periodicEstermann q
          (dfiVoronoiCharacter q d⁻¹) s := by
    simpa [P] using hpm
  have hpp' :
      (∑ a : ZMod q, ∑ b : ZMod q,
        dfiVoronoiCharacter q d (a * b) * P 1 a * P 1 b) =
        (q : ℂ) * periodicEstermann q
          (dfiVoronoiCharacter q (-d⁻¹)) s := by
    simpa [P] using hpp
  have hscale (r t : ZMod q) (α β : ℂ) :
      (∑ a : ZMod q, ∑ b : ZMod q,
        dfiVoronoiCharacter q d (a * b) *
          (C * (α * P r a)) * (C * (β * P t b))) =
        C ^ 2 * α * β *
          (∑ a : ZMod q, ∑ b : ZMod q,
            dfiVoronoiCharacter q d (a * b) * P r a * P t b) := by
    conv_rhs => rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    conv_rhs => rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring
  unfold periodicEstermannDual
  simp_rw [periodicLFunctionDual_indicator_eq_branches]
  change (∑ a : ZMod q, ∑ b : ZMod q,
      dfiVoronoiCharacter q d (a * b) *
        (C * (ep * P (-1) a + em * P 1 a)) *
        (C * (ep * P (-1) b + em * P 1 b))) = _
  simp_rw [mul_add, add_mul, Finset.sum_add_distrib]
  rw [hscale (-1) (-1) ep ep, hscale 1 (-1) em ep,
    hscale (-1) 1 ep em, hscale 1 1 em em]
  rw [hmm', hpm', hmp', hpp']
  have hemp : em * ep = 1 := by rw [mul_comm, hepem]
  have hfinal (Q K ep' em' E F X Y : ℂ)
      (hee : ep' * ep' = E) (hff : em' * em' = F)
      (hef : ep' * em' = 1) (hfe : em' * ep' = 1) :
      K * ep' * ep' * (Q * X) + K * em' * ep' * (Q * Y) +
          (K * ep' * em' * (Q * Y) + K * em' * em' * (Q * X)) =
        Q * K * (E * X + F * X) + Q * K * (2 * Y) := by
    calc
      K * ep' * ep' * (Q * X) + K * em' * ep' * (Q * Y) +
            (K * ep' * em' * (Q * Y) + K * em' * em' * (Q * X)) =
          K * (ep' * ep') * (Q * X) + K * (em' * ep') * (Q * Y) +
            (K * (ep' * em') * (Q * Y) + K * (em' * em') * (Q * X)) := by
              ring
      _ = K * E * (Q * X) + K * 1 * (Q * Y) +
            (K * 1 * (Q * Y) + K * F * (Q * X)) := by
              rw [hee, hff, hef, hfe]
      _ = Q * K * (E * X + F * X) + Q * K * (2 * Y) := by ring
  simpa [C] using hfinal (q : ℂ) (C ^ 2) ep em
    (cexp (Real.pi * I * s)) (cexp (-Real.pi * I * s))
    (periodicEstermann q (dfiVoronoiCharacter q (-d⁻¹)) s)
    (periodicEstermann q (dfiVoronoiCharacter q d⁻¹) s)
    hepep hemem hepem hemp

/-- Mellin multiplier of DFI's `Y₀` (equal-sign) Voronoi branch. -/
noncomputable def dfiVoronoiMinusMultiplier (q : ℕ) [NeZero q]
    (z : ℂ) : ℂ :=
  (q : ℂ) * dfiPeriodicArchimedeanFactor q (1 - z) ^ 2 *
    (cexp (Real.pi * I * (1 - z)) + cexp (-Real.pi * I * (1 - z)))

/-- Mellin multiplier of DFI's `K₀` (mixed-sign) Voronoi branch. -/
noncomputable def dfiVoronoiPlusMultiplier (q : ℕ) [NeZero q]
    (z : ℂ) : ℂ :=
  2 * (q : ℂ) * dfiPeriodicArchimedeanFactor q (1 - z) ^ 2

/-- Both DFI dual multipliers are holomorphic to the left of `Re z = 1`.
This is the analytic input for arbitrary repeated contour shifts in (29). -/
theorem differentiableAt_dfiVoronoiMinusMultiplier_of_re_lt_one
    (q : ℕ) [NeZero q] {z : ℂ} (hz : z.re < 1) :
    DifferentiableAt ℂ (dfiVoronoiMinusMultiplier q) z := by
  have hinner : DifferentiableAt ℂ (fun w : ℂ => 1 - w) z := by fun_prop
  have hfactor := (differentiableAt_dfiPeriodicArchimedeanFactor_of_re_pos q
    (s := 1 - z) (by simpa using sub_pos.mpr hz)).comp z hinner
  unfold dfiVoronoiMinusMultiplier
  exact ((differentiableAt_const (c := (q : ℂ))).mul (hfactor.pow 2)).mul
    ((Complex.differentiableAt_exp.comp z (by fun_prop)).add
      (Complex.differentiableAt_exp.comp z (by fun_prop)))

theorem differentiableAt_dfiVoronoiPlusMultiplier_of_re_lt_one
    (q : ℕ) [NeZero q] {z : ℂ} (hz : z.re < 1) :
    DifferentiableAt ℂ (dfiVoronoiPlusMultiplier q) z := by
  have hinner : DifferentiableAt ℂ (fun w : ℂ => 1 - w) z := by fun_prop
  have hfactor := (differentiableAt_dfiPeriodicArchimedeanFactor_of_re_pos q
    (s := 1 - z) (by simpa using sub_pos.mpr hz)).comp z hinner
  unfold dfiVoronoiPlusMultiplier
  exact ((differentiableAt_const (c := (2 : ℂ))).mul
    (differentiableAt_const (c := (q : ℂ)))).mul (hfactor.pow 2)

/-- DFI's negative-sign Bessel transform in its canonical Mellin--Barnes
form.  The source normalization is
`-(2π/q) ∫ g(x) Y₀(4π√(xy)/q) dx`; its Mellin multiplier is the
equal-sign branch above. -/
noncomputable def dfiVoronoiMinusTransform (q : ℕ) [NeZero q]
    (G : ℂ → ℂ) (n : ℕ) : ℂ :=
  VerticalIntegral' (fun z : ℂ =>
    ((n : ℂ) ^ (-(1 - z))) * dfiVoronoiMinusMultiplier q z * G z)
    (-(1 / 2 : ℝ))

/-- DFI's positive-sign modified-Bessel transform in canonical
Mellin--Barnes form.  Its source normalization is
`(4/q) ∫ g(x) K₀(4π√(xy)/q) dx`. -/
noncomputable def dfiVoronoiPlusTransform (q : ℕ) [NeZero q]
    (G : ℂ → ℂ) (n : ℕ) : ℂ :=
  VerticalIntegral' (fun z : ℂ =>
    ((n : ℂ) ^ (-(1 - z))) * dfiVoronoiPlusMultiplier q z * G z)
    (-(1 / 2 : ℝ))

/-- Pointwise split of the reflected Estermann integrand into the two
source-sign Bessel branches. -/
theorem periodicEstermannReflectedIntegrand_voronoiCharacter (q : ℕ)
    [NeZero q] (d : ZMod q) (hd : IsUnit d) (G : ℂ → ℂ) (z : ℂ) :
    periodicEstermannReflectedIntegrand q (dfiVoronoiCharacter q d) G z =
      periodicEstermann q (dfiVoronoiCharacter q (-d⁻¹)) (1 - z) *
          dfiVoronoiMinusMultiplier q z * G z +
        periodicEstermann q (dfiVoronoiCharacter q d⁻¹) (1 - z) *
          dfiVoronoiPlusMultiplier q z * G z := by
  unfold periodicEstermannReflectedIntegrand
  rw [periodicEstermannDual_voronoiCharacter q d hd]
  unfold dfiVoronoiMinusMultiplier dfiVoronoiPlusMultiplier
  ring

end RiemannZeta.GuthMaynard
