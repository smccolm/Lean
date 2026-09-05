import GafniTao.Pintz2023HalaszGram

/-!
# Pintz (2023), equation (4.18): literal Halász vectors

The two factors below are Pintz's `d_n` and `e_n^(nu)`.  Their product is
proved to recover the actual powered Dirichlet summand.  The individual
zero parameter `etaJ` remains in the second vector, so the later Gram entry
has exactly the shifted-zeta exponent appearing in (4.19).
-/

open Complex Finset
open scoped BigOperators ComplexConjugate

namespace GafniTao

noncomputable section

/-- The positive smoothing difference in Pintz (4.18). -/
noncomputable def pintz2023HalaszKernel (N n : ℕ) : ℝ :=
  Real.exp (-(n : ℝ) / (2 * N)) - Real.exp (-(n : ℝ) / N)

theorem pintz2023HalaszKernel_pos
    {N n : ℕ} (hN : 0 < N) (hn : 0 < n) :
    0 < pintz2023HalaszKernel N n := by
  have hNReal : (0 : ℝ) < N := by exact_mod_cast hN
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
  have hfrac : -(n : ℝ) / N < -(n : ℝ) / (2 * N) := by
    rw [div_lt_div_iff₀ hNReal (by positivity : (0 : ℝ) < 2 * N)]
    nlinarith
  unfold pintz2023HalaszKernel
  exact sub_pos.mpr (Real.exp_lt_exp.mpr hfrac)

/-- Pintz's common coefficient `d_n` from (4.18). -/
noncomputable def pintz2023HalaszD
    (b : ℕ → ℂ) (N : ℕ) (eta lambda : ℝ) (n : ℕ) : ℂ :=
  b n * ((Real.sqrt (pintz2023HalaszKernel N n) : ℝ) : ℂ)⁻¹ *
    (n : ℂ) ^ (-(((1 / 2 + 2 * eta + 1 / lambda : ℝ) : ℂ)))

/-- Pintz's zero-dependent vector `e_n^(nu)` from (4.18). -/
noncomputable def pintz2023HalaszE
    (N : ℕ) (eta etaJ gamma : ℝ) (n : ℕ) : ℂ :=
  ((Real.sqrt (pintz2023HalaszKernel N n) : ℝ) : ℂ) *
    (n : ℂ) ^
      (-(((1 / 2 - 2 * eta - etaJ : ℝ) : ℂ) + I * (gamma : ℂ)))

/-- Exact cancellation of the artificial square-root weight in (4.18).
The right side is the powered source term at the shifted zero
`1 - etaJ + 1/lambda + i gamma`. -/
theorem pintz2023HalaszD_mul_E
    {N n : ℕ} (b : ℕ → ℂ) (eta etaJ gamma lambda : ℝ)
    (hN : 0 < N) (hn : 0 < n) :
    pintz2023HalaszD b N eta lambda n *
        pintz2023HalaszE N eta etaJ gamma n =
      b n * (n : ℂ) ^
        (-(((1 - etaJ + 1 / lambda : ℝ) : ℂ) + I * (gamma : ℂ))) := by
  have hkernel : 0 < pintz2023HalaszKernel N n :=
    pintz2023HalaszKernel_pos hN hn
  have hsqrt : 0 < Real.sqrt (pintz2023HalaszKernel N n) :=
    Real.sqrt_pos.2 hkernel
  have hsqrtC :
      (((Real.sqrt (pintz2023HalaszKernel N n) : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast hsqrt.ne'
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold pintz2023HalaszD pintz2023HalaszE
  field_simp [hsqrtC]
  rw [mul_assoc, ← Complex.cpow_add _ _ hnC]
  congr 2
  push_cast
  ring

/-- A Gram entry formed from Pintz's vectors is the literal exponentially
smoothed shifted-zeta monomial in (4.19).  In particular, the real part is
`1 - etaJ - etaK - 4 * eta` and the height is `delta - gamma`. -/
theorem conj_pintz2023HalaszE_mul
    {N n : ℕ} (eta etaJ etaK gamma delta : ℝ)
    (hN : 0 < N) (hn : 0 < n) :
    conj (pintz2023HalaszE N eta etaJ gamma n) *
        pintz2023HalaszE N eta etaK delta n =
      ((pintz2023HalaszKernel N n : ℝ) : ℂ) *
        (n : ℂ) ^
          (-(((1 - etaJ - etaK - 4 * eta : ℝ) : ℂ) +
            I * ((delta - gamma : ℝ) : ℂ))) := by
  have hkernel : 0 < pintz2023HalaszKernel N n :=
    pintz2023HalaszKernel_pos hN hn
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hnArg : ((n : ℂ)).arg ≠ Real.pi := by
    rw [Complex.natCast_arg]
    exact Real.pi_ne_zero.symm
  let a : ℂ :=
    -(((1 / 2 - 2 * eta - etaJ : ℝ) : ℂ) + I * (gamma : ℂ))
  let c : ℂ :=
    -(((1 / 2 - 2 * eta - etaK : ℝ) : ℂ) + I * (delta : ℂ))
  have hpow : conj ((n : ℂ) ^ a) = (n : ℂ) ^ conj a := by
    simpa [a] using (Complex.cpow_conj (n : ℂ) a hnArg).symm
  let q : ℝ := Real.sqrt (pintz2023HalaszKernel N n)
  unfold pintz2023HalaszE
  change
    conj ((q : ℂ) * (n : ℂ) ^ a) *
      ((q : ℂ) * (n : ℂ) ^ c) = _
  have hsqrt :
      Real.sqrt (pintz2023HalaszKernel N n) ^ 2 =
        pintz2023HalaszKernel N n := Real.sq_sqrt hkernel.le
  have hexponent :
      conj a + c =
        -(((1 - etaJ - etaK - 4 * eta : ℝ) : ℂ) +
          I * ((delta - gamma : ℝ) : ℂ)) := by
    dsimp only [a, c]
    apply Complex.ext <;> simp <;> ring
  have hsqrtC :
      (q : ℂ) * (q : ℂ) =
        ((pintz2023HalaszKernel N n : ℝ) : ℂ) := by
    rw [← ofReal_mul, ← pow_two]
    dsimp only [q]
    exact_mod_cast hsqrt
  rw [map_mul, hpow, Complex.conj_ofReal]
  calc
    (q : ℂ) * (n : ℂ) ^ conj a *
          ((q : ℂ) * (n : ℂ) ^ c) =
        ((q : ℂ) * (q : ℂ)) *
          ((n : ℂ) ^ conj a * (n : ℂ) ^ c) := by ring
    _ = ((pintz2023HalaszKernel N n : ℝ) : ℂ) *
          (n : ℂ) ^ (conj a + c) := by
      rw [hsqrtC, ← Complex.cpow_add _ _ hnC]
    _ = _ := by rw [hexponent]

#print axioms pintz2023HalaszKernel_pos
#print axioms pintz2023HalaszD_mul_E
#print axioms conj_pintz2023HalaszE_mul

end

end GafniTao
