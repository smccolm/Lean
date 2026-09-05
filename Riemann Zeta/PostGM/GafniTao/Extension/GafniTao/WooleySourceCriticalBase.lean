import GafniTao.WooleySection10Theorem
import GafniTao.WooleySourceBoxing

/-!
# The source degree-one base case for Wooley Corollary 3.2

For a `p^c`-spaced linear system with `c ≥ 1`, equality of its values modulo
`p^B` is equivalent to equality of the source variables modulo `p^B`.  This
is the source-level base case needed by the degree induction; it is stronger
than the coefficient-one finite-box base case.
-/

open Finset Polynomial
open scoped BigOperators ComplexConjugate

namespace GafniTao

noncomputable section

/-- A degree-one spaced polynomial induces an injective map on every
`p^B` residue ring once the spacing depth is positive. -/
theorem wooley_spaced_degree_one_value_eq_iff
    {p c B : ℕ} {phi : WooleyPolynomialSystem 1}
    (hphi : phi.Spaced p c) (hc : 1 ≤ c) (n m : ℤ) :
    (((phi 0).eval n : ℤ) : ZMod (p ^ B)) =
        (((phi 0).eval m : ℤ) : ZMod (p ^ B)) ↔
      (n : ZMod (p ^ B)) = (m : ZMod (p ^ B)) := by
  obtain ⟨psi, hpsi⟩ := hphi
  obtain ⟨z, hz⟩ := Polynomial.sub_dvd_eval_sub n m (psi 0)
  have hpsiDiff :
      (psi 0).eval n - (psi 0).eval m = (n - m) * z := by
    simpa [mul_comm] using hz
  have hphi0 := hpsi (0 : Fin 1)
  constructor
  · intro h
    have hprod :
        ((1 + ((p : ZMod (p ^ B)) ^ c) * (z : ZMod (p ^ B))) *
            ((n : ZMod (p ^ B)) - (m : ZMod (p ^ B)))) = 0 := by
      have heval :
          ((((phi 0).eval n - (phi 0).eval m : ℤ) : ZMod (p ^ B))) = 0 := by
        push_cast
        exact sub_eq_zero.mpr h
      rw [hphi0] at heval
      simp only [eval_add, eval_pow, eval_X, eval_mul, eval_C] at heval
      push_cast at heval
      have hpsiCast :
          (((psi 0).eval n : ℤ) : ZMod (p ^ B)) -
              (((psi 0).eval m : ℤ) : ZMod (p ^ B)) =
            ((n : ZMod (p ^ B)) - (m : ZMod (p ^ B))) *
              (z : ZMod (p ^ B)) := by
        rw [← Int.cast_sub, hpsiDiff]
        push_cast
        rfl
      norm_num at heval
      rw [show
          (n : ZMod (p ^ B)) + (p : ZMod (p ^ B)) ^ c *
                (((psi 0).eval n : ℤ) : ZMod (p ^ B)) -
              ((m : ZMod (p ^ B)) + (p : ZMod (p ^ B)) ^ c *
                (((psi 0).eval m : ℤ) : ZMod (p ^ B))) =
            ((n : ZMod (p ^ B)) - (m : ZMod (p ^ B))) +
              (p : ZMod (p ^ B)) ^ c *
                ((((psi 0).eval n : ℤ) : ZMod (p ^ B)) -
                  (((psi 0).eval m : ℤ) : ZMod (p ^ B))) by ring] at heval
      rw [hpsiCast] at heval
      calc
        (1 + (p : ZMod (p ^ B)) ^ c * (z : ZMod (p ^ B))) *
              ((n : ZMod (p ^ B)) - (m : ZMod (p ^ B))) =
            ((n : ZMod (p ^ B)) - (m : ZMod (p ^ B))) +
              (p : ZMod (p ^ B)) ^ c *
                (((n : ZMod (p ^ B)) - (m : ZMod (p ^ B))) *
                  (z : ZMod (p ^ B))) := by ring
        _ = 0 := heval
    have hnil :
        (-(((p : ZMod (p ^ B)) ^ c) * (z : ZMod (p ^ B)))) ^ (B + 1) = 0 := by
      rw [neg_pow, mul_pow, wooley_primePowerScalar_pow_succ_eq_zero p c B hc]
      simp
    have hdiff := wooley_one_sub_mul_eq_zero_of_pow_eq_zero
      (-(((p : ZMod (p ^ B)) ^ c) * (z : ZMod (p ^ B))))
      ((n : ZMod (p ^ B)) - (m : ZMod (p ^ B))) (B + 1) hnil (by
        simpa only [sub_neg_eq_add] using hprod)
    exact sub_eq_zero.mp hdiff
  · intro h
    have hmod : Int.ModEq (p ^ B : ℤ) n m :=
      (ZMod.intCast_eq_intCast_iff n m (p ^ B)).mp h
    exact (ZMod.intCast_eq_intCast_iff _ _ (p ^ B)).mpr
      (Int.modEq_iff_dvd.mpr
        (dvd_trans hmod.dvd (Polynomial.sub_dvd_eval_sub m n (phi 0))))

/-- The product of two degree-one source phases is the character of the
difference of their polynomial values. -/
theorem wooley_degree_one_phase_mul_conj
    {q : ℕ} [NeZero q] (phi : WooleyPolynomialSystem 1)
    (alpha : Fin 1 → ZMod q) (n m : ℤ) :
    wooleySourcePolynomialPhase phi alpha n *
        conj (wooleySourcePolynomialPhase phi alpha m) =
      ZMod.stdAddChar
        (alpha 0 *
          ((((phi 0).eval n : ℤ) : ZMod q) -
            (((phi 0).eval m : ℤ) : ZMod q))) := by
  unfold wooleySourcePolynomialPhase
  simp only [Fin.sum_univ_one]
  rw [← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul]
  congr 1
  ring

/-- Exact degree-one Fourier orthogonality for an arbitrary finitely
supported source sequence. -/
theorem wooley_degree_one_raw_average_eq_collision
    {q : ℕ} [NeZero q] (phi : WooleyPolynomialSystem 1)
    (gamma : WooleySourceSequence) :
    ((q : ℂ)⁻¹) *
        ∑ alpha : Fin 1 → ZMod q,
          wooleySourcePolynomialSum phi gamma alpha *
            conj (wooleySourcePolynomialSum phi gamma alpha) =
      ∑ n ∈ gamma.support, ∑ m ∈ gamma.support,
        if (((phi 0).eval n : ℤ) : ZMod q) =
            (((phi 0).eval m : ℤ) : ZMod q) then
          gamma n * conj (gamma m)
        else 0 := by
  unfold wooleySourcePolynomialSum
  simp_rw [map_sum, map_mul]
  simp_rw [Finset.sum_mul_sum]
  rw [Finset.mul_sum]
  calc
    ∑ alpha : Fin 1 → ZMod q,
        (q : ℂ)⁻¹ *
          ∑ n ∈ gamma.support, ∑ m ∈ gamma.support,
            (gamma n * wooleySourcePolynomialPhase phi alpha n) *
              (conj (gamma m) *
                conj (wooleySourcePolynomialPhase phi alpha m)) =
      ∑ alpha : Fin 1 → ZMod q,
        ∑ n ∈ gamma.support, ∑ m ∈ gamma.support,
          (q : ℂ)⁻¹ *
            ((gamma n * wooleySourcePolynomialPhase phi alpha n) *
              (conj (gamma m) *
                conj (wooleySourcePolynomialPhase phi alpha m))) := by
      apply Finset.sum_congr rfl
      intro alpha halpha
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.mul_sum]
    _ = ∑ n ∈ gamma.support, ∑ m ∈ gamma.support,
        ∑ alpha : Fin 1 → ZMod q,
          (q : ℂ)⁻¹ *
            ((gamma n * wooleySourcePolynomialPhase phi alpha n) *
              (conj (gamma m) *
                conj (wooleySourcePolynomialPhase phi alpha m))) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro m hm
      calc
        ∑ alpha : Fin 1 → ZMod q,
            (q : ℂ)⁻¹ *
              ((gamma n * wooleySourcePolynomialPhase phi alpha n) *
                (conj (gamma m) *
                  conj (wooleySourcePolynomialPhase phi alpha m))) =
          gamma n * conj (gamma m) *
            ((q : ℂ)⁻¹ *
              ∑ alpha : Fin 1 → ZMod q,
                ZMod.stdAddChar
                  (alpha 0 *
                    ((((phi 0).eval n : ℤ) : ZMod q) -
                      (((phi 0).eval m : ℤ) : ZMod q)))) := by
            rw [Finset.mul_sum, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro alpha halpha
            calc
              (q : ℂ)⁻¹ *
                    ((gamma n * wooleySourcePolynomialPhase phi alpha n) *
                      (conj (gamma m) *
                        conj (wooleySourcePolynomialPhase phi alpha m))) =
                  (q : ℂ)⁻¹ * (gamma n * conj (gamma m) *
                    (wooleySourcePolynomialPhase phi alpha n *
                      conj (wooleySourcePolynomialPhase phi alpha m))) := by
                    ring
              _ = _ := by
                rw [wooley_degree_one_phase_mul_conj]
                ring
        _ = if (((phi 0).eval n : ℤ) : ZMod q) =
                (((phi 0).eval m : ℤ) : ZMod q) then
              gamma n * conj (gamma m)
            else 0 := by
          have hsum := wooley_normalized_grid_character q 1
            (fun _ : Fin 1 =>
              ((((phi 0).eval n : ℤ) : ZMod q) -
                (((phi 0).eval m : ℤ) : ZMod q)))
          have hsum' :
              (q : ℂ)⁻¹ *
                  ∑ alpha : Fin 1 → ZMod q,
                    ZMod.stdAddChar
                      (alpha 0 *
                        ((((phi 0).eval n : ℤ) : ZMod q) -
                          (((phi 0).eval m : ℤ) : ZMod q))) =
                if (((phi 0).eval n : ℤ) : ZMod q) =
                    (((phi 0).eval m : ℤ) : ZMod q) then 1 else 0 := by
            simp only [Fin.prod_univ_one, pow_one] at hsum
            by_cases hd : (((phi 0).eval n : ℤ) : ZMod q) =
                (((phi 0).eval m : ℤ) : ZMod q)
            · have hfun :
                  (fun _ : Fin 1 =>
                    ((((phi 0).eval n : ℤ) : ZMod q) -
                      (((phi 0).eval m : ℤ) : ZMod q))) = 0 := by
                  funext j
                  simp [hd]
              rw [if_pos hfun] at hsum
              rw [if_pos hd]
              exact hsum
            · have hfun :
                  (fun _ : Fin 1 =>
                    ((((phi 0).eval n : ℤ) : ZMod q) -
                      (((phi 0).eval m : ℤ) : ZMod q))) ≠ 0 := by
                  intro hzero
                  have := congrFun hzero (0 : Fin 1)
                  simp only [Pi.zero_apply, sub_eq_zero] at this
                  exact hd this
              rw [if_neg hfun] at hsum
              rw [if_neg hd]
              exact hsum
          rw [hsum']
          split_ifs <;> simp

/-- The residue collision energy to which both degree-one means reduce. -/
def wooleyDegreeOneResidueCollision (q : ℕ)
    (gamma : WooleySourceSequence) : ℂ :=
  ∑ n ∈ gamma.support, ∑ m ∈ gamma.support,
    if (n : ZMod q) = (m : ZMod q) then
      gamma n * conj (gamma m)
    else 0

/-- The normalized global degree-one mean is the residue collision energy
divided by the source mass. -/
theorem wooley_degree_one_sourceMean_eq_residueCollision
    {p c B : ℕ} [NeZero p] {phi : WooleyPolynomialSystem 1}
    (hphi : phi.Spaced p c) (hc : 1 ≤ c)
    (gamma : WooleySourceSequence) :
    ((wooleySourcePolynomialMean 1 (p ^ B) phi gamma : ℝ) : ℂ) =
      ((wooleySourceMassSq gamma : ℂ)⁻¹) *
        wooleyDegreeOneResidueCollision (p ^ B) gamma := by
  by_cases hmass : wooleySourceMassSq gamma = 0
  · simp [wooleySourcePolynomialMean,
      wooleySourceNormalizedPolynomialSum, hmass]
  · have hraw := wooley_degree_one_raw_average_eq_collision
      (q := p ^ B) phi gamma
    simp_rw [wooley_spaced_degree_one_value_eq_iff hphi hc] at hraw
    unfold wooleySourcePolynomialMean
    simp only [pow_one, Nat.cast_pow]
    simp_rw [norm_wooleySourceNormalizedPolynomialSum_pow_even
      phi gamma _ 1 hmass]
    simp only [pow_one]
    push_cast
    have hnorm (z : ℂ) : ((‖z‖ : ℝ) : ℂ) ^ 2 = z * conj z := by
      simpa only [pow_one] using (ford_pow_mul_conj_pow z 1).symm
    simp_rw [hnorm]
    have hraw' : ((p : ℂ) ^ B)⁻¹ *
          ∑ alpha : Fin 1 → ZMod (p ^ B),
            wooleySourcePolynomialSum phi gamma alpha *
              conj (wooleySourcePolynomialSum phi gamma alpha) =
        wooleyDegreeOneResidueCollision (p ^ B) gamma := by
      simpa only [Nat.cast_pow, wooleyDegreeOneResidueCollision] using hraw
    calc
      ((p : ℂ) ^ B)⁻¹ *
          ∑ alpha : Fin 1 → ZMod (p ^ B),
            (wooleySourceMassSq gamma : ℂ)⁻¹ *
              (wooleySourcePolynomialSum phi gamma alpha *
                conj (wooleySourcePolynomialSum phi gamma alpha)) =
        (wooleySourceMassSq gamma : ℂ)⁻¹ *
          (((p : ℂ) ^ B)⁻¹ *
            ∑ alpha : Fin 1 → ZMod (p ^ B),
              wooleySourcePolynomialSum phi gamma alpha *
                conj (wooleySourcePolynomialSum phi gamma alpha)) := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro alpha halpha
          ring
      _ = _ := by rw [hraw']

theorem wooley_degree_one_sourceMean_residueSequence
    {q qH : ℕ} [NeZero q] (phi : WooleyPolynomialSystem 1)
    (gamma : WooleySourceSequence) (xi : ZMod qH) :
    wooleySourcePolynomialMean 1 q phi
        (wooleySourceResidueSequence gamma qH xi) =
      wooleySourcePolynomialResidueMean 1 q qH phi gamma xi := by
  unfold wooleySourcePolynomialMean wooleySourcePolynomialResidueMean
  simp_rw [wooleySourceNormalizedPolynomialSum_residueSequence]

theorem wooleyDegreeOneResidueCollision_residueSequence
    (q : ℕ) (gamma : WooleySourceSequence) (xi : ZMod q) :
    wooleyDegreeOneResidueCollision q
        (wooleySourceResidueSequence gamma q xi) =
      ∑ n ∈ gamma.support.filter (fun n : ℤ => (n : ZMod q) = xi),
        ∑ m ∈ gamma.support.filter (fun m : ℤ => (m : ZMod q) = xi),
          gamma n * conj (gamma m) := by
  unfold wooleyDegreeOneResidueCollision
  rw [wooleySourceResidueSequence_support]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [Finset.mem_filter] at hn
  rw [wooleySourceResidueSequence_apply, if_pos hn.2]
  apply Finset.sum_congr rfl
  intro m hm
  simp only [Finset.mem_filter] at hm
  rw [wooleySourceResidueSequence_apply, if_pos hm.2]
  rw [if_pos (hn.2.trans hm.2.symm)]

theorem wooley_sum_residueCollision_residueSequence
    (q : ℕ) [NeZero q] (gamma : WooleySourceSequence) :
    ∑ xi : ZMod q,
        wooleyDegreeOneResidueCollision q
          (wooleySourceResidueSequence gamma q xi) =
      wooleyDegreeOneResidueCollision q gamma := by
  simp_rw [wooleyDegreeOneResidueCollision_residueSequence]
  unfold wooleyDegreeOneResidueCollision
  calc
    ∑ xi : ZMod q,
        ∑ n ∈ gamma.support.filter (fun n : ℤ => (n : ZMod q) = xi),
          ∑ m ∈ gamma.support.filter (fun m : ℤ => (m : ZMod q) = xi),
            gamma n * conj (gamma m) =
      ∑ xi : ZMod q,
        ∑ n ∈ gamma.support.filter (fun n : ℤ => (n : ZMod q) = xi),
          ∑ m ∈ gamma.support,
            if (n : ZMod q) = (m : ZMod q) then
              gamma n * conj (gamma m)
            else 0 := by
      apply Finset.sum_congr rfl
      intro xi hxi
      apply Finset.sum_congr rfl
      intro n hn
      simp only [Finset.mem_filter] at hn
      rw [← Finset.sum_filter]
      congr 1
      ext m
      simp [hn.2, eq_comm]
    _ = ∑ n ∈ gamma.support, ∑ m ∈ gamma.support,
        if (n : ZMod q) = (m : ZMod q) then
          gamma n * conj (gamma m)
        else 0 := by
      exact Finset.sum_fiberwise
        (s := gamma.support)
        (g := fun n : ℤ => (n : ZMod q))
        (f := fun n : ℤ =>
          ∑ m ∈ gamma.support,
            if (n : ZMod q) = (m : ZMod q) then
              gamma n * conj (gamma m)
            else 0)

/-- The fully conditioned degree-one source mean has the same normalized
residue collision expansion as the global mean. -/
theorem wooley_degree_one_conditionedMean_eq_residueCollision
    {p c B : ℕ} [NeZero p] {phi : WooleyPolynomialSystem 1}
    (hphi : phi.Spaced p c) (hc : 1 ≤ c)
    (gamma : WooleySourceSequence) :
    ((wooleySourcePolynomialConditionedMean 1 (p ^ B) (p ^ B)
        phi gamma : ℝ) : ℂ) =
      ((wooleySourceMassSq gamma : ℂ)⁻¹) *
        wooleyDegreeOneResidueCollision (p ^ B) gamma := by
  by_cases hmass : wooleySourceMassSq gamma = 0
  · simp [wooleySourcePolynomialConditionedMean, hmass]
  · have hweighted := wooleySourceMassSq_mul_conditionedMean
      (s := 1) (q := p ^ B) (qH := p ^ B) phi gamma
    have hterm (xi : ZMod (p ^ B)) :
        (wooleySourceResidueMassSq gamma (p ^ B) xi : ℂ) *
            (wooleySourcePolynomialResidueMean 1 (p ^ B) (p ^ B)
              phi gamma xi : ℂ) =
          wooleyDegreeOneResidueCollision (p ^ B)
            (wooleySourceResidueSequence gamma (p ^ B) xi) := by
      rw [← wooley_degree_one_sourceMean_residueSequence]
      have hformula := wooley_degree_one_sourceMean_eq_residueCollision
        (B := B) hphi hc (wooleySourceResidueSequence gamma (p ^ B) xi)
      rw [wooleySourceMassSq_residueSequence] at hformula
      by_cases hxi : wooleySourceResidueMassSq gamma (p ^ B) xi = 0
      · rw [hxi]
        have hseq := (wooleySourceResidueSequence_eq_zero_iff
          gamma (p ^ B) xi).mpr hxi
        simp [hseq, wooleyDegreeOneResidueCollision]
      · rw [hformula]
        rw [← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hxi), one_mul]
    have hsumCast :
        ((∑ xi : ZMod (p ^ B),
            wooleySourceResidueMassSq gamma (p ^ B) xi *
              wooleySourcePolynomialResidueMean 1 (p ^ B) (p ^ B)
                phi gamma xi : ℝ) : ℂ) =
          ∑ xi : ZMod (p ^ B),
              wooleyDegreeOneResidueCollision (p ^ B)
              (wooleySourceResidueSequence gamma (p ^ B) xi) := by
      push_cast
      apply Finset.sum_congr rfl
      intro xi hxi
      exact hterm xi
    have hweightedC :
        (wooleySourceMassSq gamma : ℂ) *
            (wooleySourcePolynomialConditionedMean 1 (p ^ B) (p ^ B)
              phi gamma : ℂ) =
          ∑ xi : ZMod (p ^ B),
            wooleyDegreeOneResidueCollision (p ^ B)
              (wooleySourceResidueSequence gamma (p ^ B) xi) := by
      calc
        (wooleySourceMassSq gamma : ℂ) *
              (wooleySourcePolynomialConditionedMean 1 (p ^ B) (p ^ B)
                phi gamma : ℂ) =
            ((wooleySourceMassSq gamma *
              wooleySourcePolynomialConditionedMean 1 (p ^ B) (p ^ B)
                phi gamma : ℝ) : ℂ) := by
                  norm_cast
        _ = ((∑ xi : ZMod (p ^ B),
              wooleySourceResidueMassSq gamma (p ^ B) xi *
                wooleySourcePolynomialResidueMean 1 (p ^ B) (p ^ B)
                  phi gamma xi : ℝ) : ℂ) := by rw [hweighted]
        _ = _ := hsumCast
    rw [wooley_sum_residueCollision_residueSequence] at hweightedC
    have hmassC : (wooleySourceMassSq gamma : ℂ) ≠ 0 := by
      exact_mod_cast hmass
    calc
      ((wooleySourcePolynomialConditionedMean 1 (p ^ B) (p ^ B)
          phi gamma : ℝ) : ℂ) =
        (wooleySourceMassSq gamma : ℂ)⁻¹ *
          ((wooleySourceMassSq gamma : ℂ) *
            (wooleySourcePolynomialConditionedMean 1 (p ^ B) (p ^ B)
              phi gamma : ℂ)) := by
                rw [← mul_assoc, inv_mul_cancel₀ hmassC, one_mul]
      _ = _ := by rw [hweightedC]

/-- At degree one, full conditioning loses nothing: both sides are the same
normalized residue collision energy. -/
theorem wooley_degree_one_sourceMean_eq_conditionedMean
    {p c B : ℕ} [NeZero p] {phi : WooleyPolynomialSystem 1}
    (hphi : phi.Spaced p c) (hc : 1 ≤ c)
    (gamma : WooleySourceSequence) :
    wooleySourcePolynomialMean (wooleyTriangular 1) (p ^ B) phi gamma =
      wooleySourcePolynomialConditionedMean (wooleyTriangular 1)
        (p ^ B) (p ^ (B ⌈/⌉ 1)) phi gamma := by
  have hceil : B ⌈/⌉ 1 = B := by
    simp
  rw [show wooleyTriangular 1 = 1 by decide, hceil]
  apply Complex.ofReal_injective
  rw [wooley_degree_one_sourceMean_eq_residueCollision hphi hc,
    wooley_degree_one_conditionedMean_eq_residueCollision hphi hc]

/-- The exact source-level `k=1` base case of Wooley Corollary 3.2. -/
theorem wooleyPolynomialCorollary32At_degree_one
    (p : ℕ) (hpPrime : p.Prime) :
    @WooleyPolynomialCorollary32At 1 p ⟨hpPrime.ne_zero⟩ := by
  letI : NeZero p := ⟨hpPrime.ne_zero⟩
  intro tau epsilon htau hepsilon
  obtain ⟨B0 : ℕ, hB0⟩ := exists_nat_ge (1 / tau)
  refine ⟨1, by norm_num, B0, ?_⟩
  intro B phi gamma hB hphi hgamma
  obtain ⟨c, hspaced, hscale⟩ := hphi
  have htauB : (1 : ℝ) ≤ tau * B := by
    have hBreal : (B0 : ℝ) ≤ B := by exact_mod_cast hB
    have hdiv : 1 / tau ≤ (B : ℝ) := hB0.trans hBreal
    rw [div_le_iff₀ htau] at hdiv
    simpa only [one_mul, mul_comm] using hdiv
  have hc : 1 ≤ c := by
    exact_mod_cast htauB.trans hscale
  rw [wooley_degree_one_sourceMean_eq_conditionedMean hspaced hc]
  simp only [one_mul]
  have hpOne : (1 : ℝ) ≤ (p : ℝ) ^ B := by
    exact one_le_pow₀ (by exact_mod_cast hpPrime.one_le)
  have hloss : (1 : ℝ) ≤ (p ^ B : ℝ) ^ epsilon :=
    Real.one_le_rpow hpOne hepsilon.le
  have hcond : 0 ≤ wooleySourcePolynomialConditionedMean
      (wooleyTriangular 1) (p ^ B) (p ^ (B ⌈/⌉ 1)) phi gamma :=
    wooleySourcePolynomialConditionedMean_nonneg phi _ _ _ gamma
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hloss hcond

/-- Vanishing of the operational critical exponent gives the exact
source-form Corollary 3.2 estimate.  This is the infimum-to-eventual-bound
bridge used after the Section 10 contradiction. -/
theorem wooleyPolynomialCorollary32At_of_criticalExponent_eq_zero
    {k p : ℕ} [NeZero p] (hk : 1 ≤ k)
    (hcritical : wooleyCriticalExponent k p = 0) :
    WooleyPolynomialCorollary32At k p := by
  intro tau epsilon htau hepsilon
  have habove : wooleyCriticalExponent k p < epsilon := by
    rw [hcritical]
    exact hepsilon
  obtain ⟨C, hC, B0, hbound⟩ :=
    wooley_uniformExponentBound_above_critical hk habove tau htau
  refine ⟨C, hC, B0, ?_⟩
  intro B phi gamma hB hphi hgamma
  have hold := hbound B phi gamma hB hphi hgamma
  have hceil : B ⌈/⌉ k ≤ B := by
    rw [ceilDiv_le_iff_le_mul (by omega : 0 < k)]
    exact Nat.le_mul_of_pos_left B (by omega : 0 < k)
  have hpowNat : p ^ (B ⌈/⌉ k) ≤ p ^ B :=
    Nat.pow_le_pow_right (NeZero.pos p) hceil
  have hpowReal :
      ((p ^ (B ⌈/⌉ k) : ℕ) : ℝ) ≤ (p ^ B : ℕ) := by
    exact_mod_cast hpowNat
  have hbase : (0 : ℝ) ≤ ((p ^ (B ⌈/⌉ k) : ℕ) : ℝ) := by positivity
  have hloss :
      (((p ^ (B ⌈/⌉ k) : ℕ) : ℝ) ^ epsilon) ≤
        ((p ^ B : ℕ) : ℝ) ^ epsilon :=
    Real.rpow_le_rpow hbase hpowReal hepsilon.le
  have hcond : 0 ≤ wooleySourcePolynomialConditionedMean
      (wooleyTriangular k) (p ^ B) (p ^ (B ⌈/⌉ k)) phi gamma :=
    wooleySourcePolynomialConditionedMean_nonneg phi _ _ _ gamma
  exact hold.trans (by
    simpa only [mul_assoc, Nat.cast_pow] using
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hloss hcond) hC.le)

/-- Wooley Corollary 3.2, proved by the degree-one collision identity and
strong induction through the source-faithful Sections 7--10 descent. -/
theorem wooleyPolynomialCorollary32_native :
    WooleyPolynomialCorollary32 := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro p hpPrime hk hkp
      letI : NeZero p := ⟨hpPrime.ne_zero⟩
      by_cases hkOne : k = 1
      · subst k
        exact wooleyPolynomialCorollary32At_degree_one p hpPrime
      · have hkTwo : 2 ≤ k := by omega
        have hlower : ∀ r, 1 ≤ r → r < k →
            WooleyPolynomialCorollary32At r p := by
          intro r hr hrk
          exact ih r hrk p hpPrime hr (hrk.trans hkp)
        exact wooleyPolynomialCorollary32At_of_criticalExponent_eq_zero hk
          (wooleyCriticalExponent_eq_zero_of_lower hpPrime hkTwo hkp hlower)

#print axioms wooley_spaced_degree_one_value_eq_iff
#print axioms wooley_degree_one_phase_mul_conj
#print axioms wooley_degree_one_raw_average_eq_collision
#print axioms wooley_degree_one_sourceMean_eq_residueCollision
#print axioms wooley_degree_one_conditionedMean_eq_residueCollision
#print axioms wooley_degree_one_sourceMean_eq_conditionedMean
#print axioms wooleyPolynomialCorollary32At_degree_one
#print axioms wooleyPolynomialCorollary32At_of_criticalExponent_eq_zero
#print axioms wooleyPolynomialCorollary32_native

end

end GafniTao
