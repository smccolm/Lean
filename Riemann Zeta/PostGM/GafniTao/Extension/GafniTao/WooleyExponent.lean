import GafniTao.WooleySourceBoxing
import GafniTao.WooleyPolynomialBasic
import GafniTao.WooleyNormalization

/-!
# Wooley's operational critical exponent

The source defines `lambda*` and `lambda` by two limsups in (3.12)--(3.13).
For the proof itself, the used content is the equivalent threshold
formulation: exponents above the threshold give a uniform eventual estimate,
while every exponent below it has arbitrarily large counterexamples.  This
file defines that threshold directly from the literal source mean.  The
definition quantifies over the actual polynomial systems and coefficient
sequences; it is not a certificate supplied to the final theorem.
-/

namespace GafniTao

noncomputable section

/-- Exact eventual estimate whose infimum is Wooley's critical exponent at
fixed degree and prime.  Constants may depend on `k`, `p`, and `tau`, as in
(3.11)--(3.13), but not on `B`, the polynomial system, or coefficients. -/
def WooleyUniformExponentBoundAt (k p : ℕ) [NeZero p]
    (Lambda : ℝ) : Prop :=
  ∀ tau : ℝ, 0 < tau →
    ∃ C : ℝ, 0 < C ∧ ∃ B0 : ℕ,
      ∀ (B : ℕ) (phi : WooleyPolynomialSystem k)
        (gamma : WooleySourceSequence),
        B0 ≤ B → phi.InPhiTau p B tau → gamma.Admissible →
          wooleySourcePolynomialMean (wooleyTriangular k) (p ^ B)
              phi gamma ≤
            C * (((p ^ (B ⌈/⌉ k) : ℕ) : ℝ) ^ Lambda) *
              wooleySourcePolynomialConditionedMean
                (wooleyTriangular k) (p ^ B)
                  (p ^ (B ⌈/⌉ k)) phi gamma

/-- Source equation (3.10) for the integer-indexed, finitely supported
coefficient model. -/
theorem wooleySourcePolynomial_equation_3_10
    {k p B : ℕ} [NeZero p] [NeZero (p ^ B)]
    (phi : WooleyPolynomialSystem k) (gamma : WooleySourceSequence)
    (hk : 1 ≤ k) :
    wooleySourcePolynomialMean (wooleyTriangular k) (p ^ B) phi gamma ≤
      ((p ^ (B ⌈/⌉ k) : ℕ) : ℝ) ^ (wooleyTriangular k) *
        wooleySourcePolynomialConditionedMean
          (wooleyTriangular k) (p ^ B) (p ^ (B ⌈/⌉ k)) phi gamma := by
  have hs : 1 ≤ wooleyTriangular k := by
    unfold wooleyTriangular
    have hkpos : 0 < k := by omega
    have htwo : 2 ≤ k * (k + 1) := by nlinarith
    omega
  rw [wooleySourcePolynomialMean_eq_boxed,
    wooleySourcePolynomialConditionedMean_eq_boxed]
  exact wooleyPolynomial_equation_3_10
    (qB := p ^ B) (qH := p ^ (B ⌈/⌉ k))
      (wooleyBoxedPolynomialSystem phi gamma)
        (wooleySourceBoxCoefficients gamma) hs

/-- Equation (3.10) makes the set of uniform exponents nonempty. -/
theorem wooley_uniformExponentBound_trivial
    {k p : ℕ} [NeZero p] (hk : 1 ≤ k) :
    WooleyUniformExponentBoundAt k p (wooleyTriangular k : ℝ) := by
  intro tau htau
  refine ⟨1, by norm_num, 0, ?_⟩
  intro B phi gamma hB hphi hgamma
  have h310 := wooleySourcePolynomial_equation_3_10
    (k := k) (p := p) (B := B) phi gamma hk
  simpa only [one_mul, Real.rpow_natCast] using h310

/-- Uniform exponent bounds are upward closed. -/
theorem WooleyUniformExponentBoundAt.mono
    {k p : ℕ} [NeZero p] {Lambda Lambda' : ℝ}
    (h : WooleyUniformExponentBoundAt k p Lambda)
    (hLambda : Lambda ≤ Lambda') :
    WooleyUniformExponentBoundAt k p Lambda' := by
  intro tau htau
  obtain ⟨C, hC, B0, hbound⟩ := h tau htau
  refine ⟨C, hC, B0, ?_⟩
  intro B phi gamma hB hphi hgamma
  have hold := hbound B phi gamma hB hphi hgamma
  have hp : 1 ≤ p := Nat.one_le_iff_ne_zero.mpr (NeZero.ne p)
  have hbase : (1 : ℝ) ≤ ((p ^ (B ⌈/⌉ k) : ℕ) : ℝ) := by
    exact_mod_cast (Nat.one_le_pow (B ⌈/⌉ k) p hp)
  have hpow :
      (((p ^ (B ⌈/⌉ k) : ℕ) : ℝ) ^ Lambda) ≤
        (((p ^ (B ⌈/⌉ k) : ℕ) : ℝ) ^ Lambda') :=
    Real.rpow_le_rpow_of_exponent_le hbase hLambda
  have hmean0 : 0 ≤ wooleySourcePolynomialConditionedMean
      (wooleyTriangular k) (p ^ B) (p ^ (B ⌈/⌉ k)) phi gamma := by
    exact wooleySourcePolynomialConditionedMean_nonneg
      phi (wooleyTriangular k) (p ^ B) (p ^ (B ⌈/⌉ k)) gamma
  exact hold.trans (by
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hpow hmean0) hC.le)

/-- The set used to define the nonnegative critical exponent. -/
def wooleyUniformExponentSet (k p : ℕ) [NeZero p] : Set ℝ :=
  {Lambda | 0 ≤ Lambda ∧ WooleyUniformExponentBoundAt k p Lambda}

/-- Operational form of Wooley's `lambda(s,k)` at the critical value
`s=k(k+1)/2`. -/
def wooleyCriticalExponent (k p : ℕ) [NeZero p] : ℝ :=
  sInf (wooleyUniformExponentSet k p)

theorem wooleyUniformExponentSet_nonempty
    {k p : ℕ} [NeZero p] (hk : 1 ≤ k) :
    (wooleyUniformExponentSet k p).Nonempty := by
  refine ⟨(wooleyTriangular k : ℝ), Nat.cast_nonneg _, ?_⟩
  exact wooley_uniformExponentBound_trivial hk

theorem wooleyUniformExponentSet_bddBelow
    (k p : ℕ) [NeZero p] :
    BddBelow (wooleyUniformExponentSet k p) := by
  refine ⟨0, ?_⟩
  intro Lambda hLambda
  exact hLambda.1

theorem wooleyCriticalExponent_nonneg
    {k p : ℕ} [NeZero p] (hk : 1 ≤ k) :
    0 ≤ wooleyCriticalExponent k p := by
  unfold wooleyCriticalExponent
  apply le_csInf (wooleyUniformExponentSet_nonempty hk)
  intro Lambda hLambda
  exact hLambda.1

theorem wooleyCriticalExponent_le_triangular
    {k p : ℕ} [NeZero p] (hk : 1 ≤ k) :
    wooleyCriticalExponent k p ≤ (wooleyTriangular k : ℝ) := by
  unfold wooleyCriticalExponent
  exact csInf_le (wooleyUniformExponentSet_bddBelow k p)
    ⟨Nat.cast_nonneg _, wooley_uniformExponentBound_trivial hk⟩

/-- Every exponent strictly above the critical exponent supplies the
literal uniform eventual estimate. -/
theorem wooley_uniformExponentBound_above_critical
    {k p : ℕ} [NeZero p] (hk : 1 ≤ k)
    {Lambda : ℝ} (hLambda : wooleyCriticalExponent k p < Lambda) :
    WooleyUniformExponentBoundAt k p Lambda := by
  have hsetNonempty := wooleyUniformExponentSet_nonempty (k := k) (p := p) hk
  have hsetBdd := wooleyUniformExponentSet_bddBelow k p
  obtain ⟨x, hx, hxlt⟩ :=
    (csInf_lt_iff hsetBdd hsetNonempty).mp hLambda
  exact hx.2.mono hxlt.le

/-- Below the critical exponent, a fixed constant and starting scale can
always be defeated by an actual source system and coefficient sequence. -/
theorem wooley_counterexample_below_critical
    {k p : ℕ} [NeZero p]
    {Lambda : ℝ} (hLambda0 : 0 ≤ Lambda)
    (hLambda : Lambda < wooleyCriticalExponent k p) :
    ¬ WooleyUniformExponentBoundAt k p Lambda := by
  intro hbound
  have hmem : Lambda ∈ wooleyUniformExponentSet k p := ⟨hLambda0, hbound⟩
  exact (notMem_of_lt_csInf hLambda
    (wooleyUniformExponentSet_bddBelow k p)) hmem

/-- A below-critical exponent supplies one fixed source `tau` and defeats
every constant and starting modulus.  This is the form needed when the small
iteration parameter `epsilon` is chosen only after that `tau` is known. -/
theorem wooley_arbitrarilyLarge_counterexamples_below
    {k p : ℕ} [NeZero p]
    {Lambda : ℝ} (hLambda0 : 0 ≤ Lambda)
    (hLambda : Lambda < wooleyCriticalExponent k p) :
    ∃ tau : ℝ, 0 < tau ∧
      ∀ C : ℝ, 0 < C → ∀ B0 : ℕ,
        ∃ (B : ℕ) (phi : WooleyPolynomialSystem k)
          (gamma : WooleySourceSequence),
          B0 ≤ B ∧ phi.InPhiTau p B tau ∧ gamma.Admissible ∧
          C * (((p ^ (B ⌈/⌉ k) : ℕ) : ℝ) ^ Lambda) *
              wooleySourcePolynomialConditionedMean
                (wooleyTriangular k) (p ^ B) (p ^ (B ⌈/⌉ k)) phi gamma <
            wooleySourcePolynomialMean (wooleyTriangular k) (p ^ B)
              phi gamma := by
  have hnot := wooley_counterexample_below_critical hLambda0 hLambda
  unfold WooleyUniformExponentBoundAt at hnot
  push Not at hnot
  obtain ⟨tau, htau, hfail⟩ := hnot
  exact ⟨tau, htau, hfail⟩

/-- Membership in `Phi_tau(B)` is monotone when the lower spacing parameter
is decreased. -/
theorem WooleyPolynomialSystem.InPhiTau.mono
    {k p B : ℕ} {phi : WooleyPolynomialSystem k} {tau tau' : ℝ}
    (hphi : phi.InPhiTau p B tau) (htau' : tau' ≤ tau) :
    phi.InPhiTau p B tau' := by
  obtain ⟨c, hc, hscale⟩ := hphi
  refine ⟨c, hc, ?_⟩
  exact (mul_le_mul_of_nonneg_right htau' (Nat.cast_nonneg B)).trans hscale

/-- Operational source form of equations (6.2)--(6.3): if the critical
exponent is positive, lowering it by a smaller positive `epsilon` produces
actual counterexamples at arbitrarily large moduli, for one fixed positive
`tau`. -/
theorem wooley_arbitrarilyLarge_counterexamples
    {k p : ℕ} [NeZero p]
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hepsilonCritical : epsilon < wooleyCriticalExponent k p) :
    ∃ tau : ℝ, 0 < tau ∧
      ∀ C : ℝ, 0 < C → ∀ B0 : ℕ,
        ∃ (B : ℕ) (phi : WooleyPolynomialSystem k)
          (gamma : WooleySourceSequence),
          B0 ≤ B ∧ phi.InPhiTau p B tau ∧ gamma.Admissible ∧
          C * (((p ^ (B ⌈/⌉ k) : ℕ) : ℝ) ^
              (wooleyCriticalExponent k p - epsilon)) *
              wooleySourcePolynomialConditionedMean
                (wooleyTriangular k) (p ^ B) (p ^ (B ⌈/⌉ k)) phi gamma <
            wooleySourcePolynomialMean (wooleyTriangular k) (p ^ B)
              phi gamma := by
  have hnonneg : 0 ≤ wooleyCriticalExponent k p - epsilon :=
    sub_nonneg.mpr hepsilonCritical.le
  have hbelow : wooleyCriticalExponent k p - epsilon <
      wooleyCriticalExponent k p := by linarith
  have hnot := wooley_counterexample_below_critical hnonneg hbelow
  unfold WooleyUniformExponentBoundAt at hnot
  push Not at hnot
  obtain ⟨tau, htau, hfail⟩ := hnot
  refine ⟨tau, htau, ?_⟩
  intro C hC B0
  obtain ⟨B, phi, gamma, hB, hphi, hgamma, hstrict⟩ :=
    hfail C hC B0
  exact ⟨B, phi, gamma, hB, hphi, hgamma, hstrict⟩

#print axioms wooleySourcePolynomial_equation_3_10
#print axioms wooley_uniformExponentBound_trivial
#print axioms WooleyUniformExponentBoundAt.mono
#print axioms wooleyCriticalExponent_nonneg
#print axioms wooleyCriticalExponent_le_triangular
#print axioms wooley_uniformExponentBound_above_critical
#print axioms wooley_counterexample_below_critical
#print axioms wooley_arbitrarilyLarge_counterexamples_below
#print axioms WooleyPolynomialSystem.InPhiTau.mono
#print axioms wooley_arbitrarilyLarge_counterexamples

end

end GafniTao
