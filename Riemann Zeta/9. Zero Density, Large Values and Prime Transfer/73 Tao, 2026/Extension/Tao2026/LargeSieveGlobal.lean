import Tao2026.LargeSieveTensor

/-!
# Finite duality for the global large sieve

This file isolates the finite functional-analytic core of the classical large
sieve.  An arbitrary finite family of analysis vectors is controlled by Schur
row and column bounds for its Gram matrix.  The later arithmetic layer only
has to estimate the Gram entries for separated circle frequencies.
-/

open Finset
open scoped BigOperators ComplexConjugate

namespace Tao2026

noncomputable section

variable {A : Type*}

/-- A weighted arithmetic--geometric mean estimate for one Gram summand. -/
theorem gramTerm_norm_le
    (G : A → A → ℂ) (z : A → ℂ) (a b : A) :
    ‖starRingEnd ℂ (z a) * G a b * z b‖ ≤
      ‖G a b‖ * (Complex.normSq (z a) + Complex.normSq (z b)) / 2 := by
  rw [norm_mul, norm_mul, starRingEnd_apply, norm_star,
    Complex.normSq_eq_norm_sq,
    Complex.normSq_eq_norm_sq]
  have hsquare : 2 * ‖z a‖ * ‖z b‖ ≤ ‖z a‖ ^ 2 + ‖z b‖ ^ 2 := by
    nlinarith [sq_nonneg (‖z a‖ - ‖z b‖)]
  have hG : 0 ≤ ‖G a b‖ := norm_nonneg _
  calc
    ‖z a‖ * ‖G a b‖ * ‖z b‖ =
        ‖G a b‖ * (2 * ‖z a‖ * ‖z b‖) / 2 := by ring
    _ ≤ ‖G a b‖ * (‖z a‖ ^ 2 + ‖z b‖ ^ 2) / 2 := by
      gcongr

/-- Schur's test for a finite complex Gram quadratic form. -/
theorem norm_gramQuadratic_le
    [Fintype A] (G : A → A → ℂ) (z : A → ℂ) (B : ℝ)
    (hrow : ∀ a, ∑ b, ‖G a b‖ ≤ B)
    (hcol : ∀ b, ∑ a, ‖G a b‖ ≤ B) :
    ‖∑ a, ∑ b, starRingEnd ℂ (z a) * G a b * z b‖ ≤
      B * ∑ a, Complex.normSq (z a) := by
  calc
    ‖∑ a, ∑ b, starRingEnd ℂ (z a) * G a b * z b‖ ≤
        ∑ a, ∑ b, ‖starRingEnd ℂ (z a) * G a b * z b‖ := by
      exact norm_sum_le_of_le _ fun a _ => norm_sum_le _ _
    _ ≤ ∑ a, ∑ b,
        ‖G a b‖ * (Complex.normSq (z a) + Complex.normSq (z b)) / 2 := by
      exact sum_le_sum fun a _ => sum_le_sum fun b _ =>
        gramTerm_norm_le G z a b
    _ = ((∑ a, Complex.normSq (z a) * ∑ b, ‖G a b‖) +
          (∑ b, Complex.normSq (z b) * ∑ a, ‖G a b‖)) / 2 := by
      simp_rw [mul_add, add_div, sum_add_distrib, sum_div]
      simp_rw [mul_sum]
      congr 1
      · apply sum_congr rfl
        intro a _
        rw [sum_div]
        apply sum_congr rfl
        intro b _
        ring
      · rw [sum_comm]
        apply sum_congr rfl
        intro a _
        rw [sum_div]
        apply sum_congr rfl
        intro b _
        ring
    _ ≤ ((∑ a, Complex.normSq (z a) * B) +
          (∑ b, Complex.normSq (z b) * B)) / 2 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      apply add_le_add
      · exact sum_le_sum fun a _ =>
          mul_le_mul_of_nonneg_left (hrow a) (Complex.normSq_nonneg _)
      · exact sum_le_sum fun b _ =>
          mul_le_mul_of_nonneg_left (hcol b) (Complex.normSq_nonneg _)
    _ = B * ∑ a, Complex.normSq (z a) := by
      simp_rw [← sum_mul]
      ring

/-- Coordinate Cauchy--Schwarz, stated using `Complex.normSq`. -/
theorem normSq_sum_mul_le {I : Type*} [Fintype I]
    (a b : I → ℂ) :
    Complex.normSq (∑ i, a i * b i) ≤
      (∑ i, Complex.normSq (a i)) *
        ∑ i, Complex.normSq (b i) := by
  rw [Complex.normSq_eq_norm_sq]
  calc
    ‖∑ i, a i * b i‖ ^ 2 ≤
        (∑ i, ‖a i‖ * ‖b i‖) ^ 2 := by
      gcongr
      exact (norm_sum_le _ _).trans
        (sum_le_sum fun i _ => le_of_eq (norm_mul (a i) (b i)))
    _ ≤ (∑ i, ‖a i‖ ^ 2) * ∑ i, ‖b i‖ ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun i => ‖a i‖) (fun i => ‖b i‖)
    _ = (∑ i, Complex.normSq (a i)) *
        ∑ i, Complex.normSq (b i) := by
      simp_rw [Complex.normSq_eq_norm_sq]

theorem normSq_starRingEnd (z : ℂ) :
    Complex.normSq (starRingEnd ℂ z) = Complex.normSq z := by
  rw [starRingEnd_apply]
  exact Complex.normSq_conj z

/-- Analysis against a finite family of complex vectors. -/
noncomputable def finiteAnalysis {I : Type*} [Fintype I]
    (u : A → I → ℂ) (f : I → ℂ) (a : A) : ℂ :=
  ∑ i, starRingEnd ℂ (u a i) * f i

/-- The adjoint synthesis map for `finiteAnalysis`. -/
noncomputable def finiteSynthesis {I : Type*} [Fintype I]
    [Fintype A] (u : A → I → ℂ) (z : A → ℂ) (i : I) : ℂ :=
  ∑ a, u a i * z a

/-- Gram matrix of a finite family of complex vectors. -/
noncomputable def finiteGram {I : Type*} [Fintype I]
    (u : A → I → ℂ) (a b : A) : ℂ :=
  ∑ i, starRingEnd ℂ (u a i) * u b i

/-- Exact analysis/synthesis pairing identity. -/
theorem finiteAnalysis_synthesis_identity {I : Type*} [Fintype I]
    [Fintype A] (u : A → I → ℂ) (f : I → ℂ) :
    ((∑ a, Complex.normSq (finiteAnalysis u f a) : ℝ) : ℂ) =
      ∑ i, starRingEnd ℂ (f i) *
        finiteSynthesis u (finiteAnalysis u f) i := by
  unfold finiteAnalysis finiteSynthesis
  push_cast
  simp_rw [Complex.normSq_eq_conj_mul_self, map_sum, map_mul]
  simp_rw [sum_mul, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro j _
  simp
  ring

/-- Exact synthesis-energy expansion through the Gram matrix. -/
theorem finiteSynthesis_gram_identity {I : Type*} [Fintype I]
    [Fintype A] (u : A → I → ℂ) (z : A → ℂ) :
    ((∑ i, Complex.normSq (finiteSynthesis u z i) : ℝ) : ℂ) =
      ∑ a, ∑ b, starRingEnd ℂ (z a) * finiteGram u a b * z b := by
  unfold finiteSynthesis finiteGram
  push_cast
  simp_rw [Complex.normSq_eq_conj_mul_self, map_sum, map_mul]
  simp_rw [sum_mul, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  rw [sum_comm]
  apply sum_congr rfl
  intro b _
  rw [sum_mul]
  apply sum_congr rfl
  intro i _
  ring

/-- Schur Gram bounds directly control the energy of the finite synthesis
map. -/
theorem finiteSynthesis_energy_le_of_gram_bounds
    {I : Type*} [Fintype I] [Fintype A]
    (u : A → I → ℂ) (z : A → ℂ) (B : ℝ)
    (hrow : ∀ a, ∑ b, ‖finiteGram u a b‖ ≤ B)
    (hcol : ∀ b, ∑ a, ‖finiteGram u a b‖ ≤ B) :
    ∑ i, Complex.normSq (finiteSynthesis u z i) ≤
      B * ∑ a, Complex.normSq (z a) := by
  let W : ℝ := ∑ i, Complex.normSq (finiteSynthesis u z i)
  have hWnonneg : 0 ≤ W := by
    exact sum_nonneg fun _ _ => Complex.normSq_nonneg _
  have hgram : (W : ℂ) =
      ∑ a, ∑ b, starRingEnd ℂ (z a) * finiteGram u a b * z b := by
    simpa only [W] using finiteSynthesis_gram_identity u z
  calc
    W = ‖(W : ℂ)‖ := by
      simp only [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hWnonneg]
    _ = ‖∑ a, ∑ b,
        starRingEnd ℂ (z a) * finiteGram u a b * z b‖ := by rw [hgram]
    _ ≤ B * ∑ a, Complex.normSq (z a) :=
      norm_gramQuadratic_le (finiteGram u) z B hrow hcol

/-- Finite operator duality in the form used by the large sieve.  Any uniform
energy bound for the synthesis map gives the same bound for its adjoint
analysis map. -/
theorem finiteAnalysis_energy_le_of_synthesis_bound
    {I : Type*} [Fintype I] [Fintype A]
    (u : A → I → ℂ) (f : I → ℂ) (B : ℝ)
    (hB : 0 ≤ B)
    (hsynthesis : ∀ z : A → ℂ,
      ∑ i, Complex.normSq (finiteSynthesis u z i) ≤
        B * ∑ a, Complex.normSq (z a)) :
    ∑ a, Complex.normSq (finiteAnalysis u f a) ≤
      B * ∑ i, Complex.normSq (f i) := by
  let z : A → ℂ := finiteAnalysis u f
  let w : I → ℂ := finiteSynthesis u z
  let E : ℝ := ∑ a, Complex.normSq (z a)
  let F : ℝ := ∑ i, Complex.normSq (f i)
  let W : ℝ := ∑ i, Complex.normSq (w i)
  have hEnonneg : 0 ≤ E := by
    exact sum_nonneg fun _ _ => Complex.normSq_nonneg _
  have hFnonneg : 0 ≤ F := by
    exact sum_nonneg fun _ _ => Complex.normSq_nonneg _
  have hinner : (E : ℂ) =
      ∑ i, starRingEnd ℂ (f i) * w i := by
    simpa only [E, z, w] using finiteAnalysis_synthesis_identity u f
  have hW : W ≤ B * E := by
    simpa only [W, w, E] using hsynthesis z
  have hEFW : E ^ 2 ≤ F * W := by
    calc
      E ^ 2 = Complex.normSq (E : ℂ) := by
        rw [Complex.normSq_ofReal]
        ring
      _ = Complex.normSq
          (∑ i, starRingEnd ℂ (f i) * w i) := by rw [hinner]
      _ ≤ (∑ i, Complex.normSq (starRingEnd ℂ (f i))) *
          ∑ i, Complex.normSq (w i) :=
        normSq_sum_mul_le (fun i => starRingEnd ℂ (f i)) w
      _ = F * W := by
        simp only [normSq_starRingEnd, F, W]
  have hEFB : E ^ 2 ≤ F * (B * E) :=
    hEFW.trans (mul_le_mul_of_nonneg_left hW hFnonneg)
  by_cases hEzero : E = 0
  · rw [show ∑ a, Complex.normSq (finiteAnalysis u f a) = 0 by
      simpa only [z, E] using hEzero]
    exact mul_nonneg hB hFnonneg
  · have hEpos : 0 < E := lt_of_le_of_ne hEnonneg (Ne.symm hEzero)
    have hcancel : E ≤ B * F := by
      apply le_of_mul_le_mul_right _ hEpos
      simpa only [pow_two, mul_assoc, mul_comm, mul_left_comm] using hEFB
    simpa only [z, E, F, mul_comm] using hcancel

/-- Finite Bombieri duality: a Schur bound for the Gram matrix controls the
square energy of every analysis vector. -/
theorem bombieri_inequality {I : Type*} [Fintype I]
    [Fintype A] (u : A → I → ℂ) (f : I → ℂ) (B : ℝ)
    (hB : 0 ≤ B)
    (hrow : ∀ a, ∑ b, ‖finiteGram u a b‖ ≤ B)
    (hcol : ∀ b, ∑ a, ‖finiteGram u a b‖ ≤ B) :
    ∑ a, Complex.normSq (finiteAnalysis u f a) ≤
      B * ∑ i, Complex.normSq (f i) := by
  apply finiteAnalysis_energy_le_of_synthesis_bound u f B hB
  intro z
  exact finiteSynthesis_energy_le_of_gram_bounds u z B hrow hcol

/-- The Gram matrix of a finite family is Hermitian.  We state the consequence
at the level of norms, which is exactly what converts the row bound in the
Bombieri--Halász--Montgomery lemma into the column bound needed by Schur's
test. -/
theorem norm_finiteGram_comm {I : Type*} [Fintype I]
    (u : A → I → ℂ) (a b : A) :
    ‖finiteGram u a b‖ = ‖finiteGram u b a‖ := by
  unfold finiteGram
  have hconj :
      conj (∑ i, starRingEnd ℂ (u a i) * u b i) =
        ∑ i, starRingEnd ℂ (u b i) * u a i := by
    simp only [map_sum, map_mul, starRingEnd_apply]
    apply sum_congr rfl
    intro i _hi
    simp
    ring
  calc
    ‖∑ i, starRingEnd ℂ (u a i) * u b i‖ =
        ‖star (∑ i, starRingEnd ℂ (u a i) * u b i)‖ :=
      (norm_star _).symm
    _ = ‖∑ i, starRingEnd ℂ (u b i) * u a i‖ :=
      congrArg norm hconj

/-- Finite Bombieri--Halász--Montgomery inequality in its source form: because
the Gram matrix is Hermitian, a uniform absolute row-sum bound alone controls
the square energy of all scalar products.  This is Lemma 5.3 of Tao's paper
after choosing coordinates in the finite weighted pre-Hilbert space. -/
theorem bombieri_halasz_montgomery_inequality
    {I : Type*} [Fintype I] [Fintype A]
    (u : A → I → ℂ) (f : I → ℂ) (B : ℝ)
    (hB : 0 ≤ B)
    (hrow : ∀ a, ∑ b, ‖finiteGram u a b‖ ≤ B) :
    ∑ a, Complex.normSq (finiteAnalysis u f a) ≤
      B * ∑ i, Complex.normSq (f i) := by
  apply bombieri_inequality u f B hB hrow
  intro b
  calc
    (∑ a, ‖finiteGram u a b‖) =
        ∑ a, ‖finiteGram u b a‖ := by
      apply sum_congr rfl
      intro a _ha
      exact norm_finiteGram_comm u a b
    _ ≤ B := hrow b

end

end Tao2026
