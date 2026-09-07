import RiemannZeta.GuthMaynard.ClassicalLargeValues
import RiemannZeta.GuthMaynard.FiniteDensityExponents

namespace RiemannZeta.GuthMaynard

/-!
# Finite scale and exponent assembly for the classical endpoints

This module isolates the exact real-arithmetic content of ANTEDB
Corollaries 11.8--11.10.  It does not assert the still-open finite
zero-density-from-large-values reduction.  Instead it packages the concrete
MHH exponent, the bounded two-or-three-fold subdivision choice, the endpoint
windows, and the exceptional zeta-polynomial alternatives which that
reduction will consume.
-/

/-- The exponent supplied by the finite Montgomery--Halász--Huxley estimate
after writing `T = N^τ` and `V = N^σ`, before epsilon losses. -/
def classicalMHHExponent (σ τ : ℝ) : ℝ :=
  max (2 - 2 * σ) (min (τ + 1 - 2 * σ) (τ + 4 - 6 * σ))

/-- The subdivision envelope obtained from a Montgomery range ending at
`τ₀ + σ - 1`. -/
def corollary1110Envelope (σ τ₀ τ : ℝ) : ℝ :=
  max (2 - 2 * σ) (3 - 3 * σ + τ - τ₀)

/-- The bounded power choice used in Corollary 11.8: every scale in the
raised window is returned to the basic window by dividing its exponent by
either two or three. -/
theorem exists_two_or_three_scale_reduction
    {τ₀ τ : ℝ} (hτLower : 4 * τ₀ / 3 ≤ τ)
    (hτUpper : τ ≤ 8 * τ₀ / 3) :
    (2 * τ₀ / 3 ≤ τ / 2 ∧ τ / 2 ≤ τ₀) ∨
      (2 * τ₀ / 3 ≤ τ / 3 ∧ τ / 3 ≤ τ₀) := by
  by_cases hτ : τ ≤ 2 * τ₀
  · left
    constructor <;> nlinarith
  · right
    constructor <;> nlinarith

/-- Literal finite-scale form of `exists_two_or_three_scale_reduction`.
For every base at least one, raising to the selected half- or third-exponent
lands between the two endpoint powers of the basic window. -/
theorem exists_two_or_three_power_scale_reduction
    {Q τ₀ τ : ℝ} (hQ : 1 ≤ Q) (hτLower : 4 * τ₀ / 3 ≤ τ)
    (hτUpper : τ ≤ 8 * τ₀ / 3) :
    (Q ^ (2 * τ₀ / 3) ≤ Q ^ (τ / 2) ∧ Q ^ (τ / 2) ≤ Q ^ τ₀) ∨
      (Q ^ (2 * τ₀ / 3) ≤ Q ^ (τ / 3) ∧ Q ^ (τ / 3) ≤ Q ^ τ₀) := by
  rcases exists_two_or_three_scale_reduction hτLower hτUpper with hTwo | hThree
  · left
    exact ⟨Real.rpow_le_rpow_of_exponent_le hQ hTwo.1,
      Real.rpow_le_rpow_of_exponent_le hQ hTwo.2⟩
  · right
    exact ⟨Real.rpow_le_rpow_of_exponent_le hQ hThree.1,
      Real.rpow_le_rpow_of_exponent_le hQ hThree.2⟩

/-- The second-moment branch gives the Montgomery exponent throughout
`τ ≤ 1`. -/
theorem classicalMHHExponent_le_montgomery_of_tau_le_one
    {σ τ : ℝ} (hτ : τ ≤ 1) :
    classicalMHHExponent σ τ ≤ 2 - 2 * σ := by
  rw [classicalMHHExponent, max_le_iff]
  constructor
  · exact le_rfl
  · exact (min_le_left _ _).trans (by linarith)

/-- The sixth-power branch gives the Montgomery exponent throughout
`τ ≤ 4σ-2`. -/
theorem classicalMHHExponent_le_montgomery_of_tau_le_four_sigma_sub_two
    {σ τ : ℝ} (hτ : τ ≤ 4 * σ - 2) :
    classicalMHHExponent σ τ ≤ 2 - 2 * σ := by
  rw [classicalMHHExponent, max_le_iff]
  constructor
  · exact le_rfl
  · exact (min_le_right _ _).trans (by linarith)

/-- Exact finite arithmetic behind Corollary 11.10.  Subdivision of a
Montgomery range controls the entire basic window by the target line. -/
theorem corollary1110Envelope_le_target
    {σ τ₀ τ : ℝ} (hσ : σ ≤ 1) (hτ₀ : 0 < τ₀)
    (hBase : 3 - 3 * σ ≤ τ₀)
    (hτLower : 2 * τ₀ / 3 ≤ τ) (hτUpper : τ ≤ τ₀) :
    corollary1110Envelope σ τ₀ τ ≤
      (3 - 3 * σ) * τ / τ₀ := by
  rw [corollary1110Envelope, max_le_iff]
  have hOneMinus : 0 ≤ 1 - σ := by linarith
  have hTargetFirst : 2 - 2 * σ ≤ (3 - 3 * σ) * τ / τ₀ := by
    rw [le_div_iff₀ hτ₀]
    nlinarith
  have hTargetSecond :
      3 - 3 * σ + τ - τ₀ ≤ (3 - 3 * σ) * τ / τ₀ := by
    rw [le_div_iff₀ hτ₀]
    nlinarith
  exact ⟨hTargetFirst, hTargetSecond⟩

/-- Literal finite-power consequence of the Corollary 11.10 exponent
assembly. -/
theorem rpow_corollary1110Envelope_le_target
    {Q σ τ₀ τ : ℝ} (hQ : 1 ≤ Q) (hσ : σ ≤ 1) (hτ₀ : 0 < τ₀)
    (hBase : 3 - 3 * σ ≤ τ₀)
    (hτLower : 2 * τ₀ / 3 ≤ τ) (hτUpper : τ ≤ τ₀) :
    Q ^ corollary1110Envelope σ τ₀ τ ≤
      Q ^ ((3 - 3 * σ) * τ / τ₀) :=
  Real.rpow_le_rpow_of_exponent_le hQ
    (corollary1110Envelope_le_target hσ hτ₀ hBase hτLower hτUpper)

/-- The exceptional zeta-polynomial window is either empty or lies in the
proved Weyl-exclusion range. -/
def ZetaWindowResolved (σ τ₀ : ℝ) : Prop :=
  ∀ τ : ℝ, 2 ≤ τ → τ < 4 * τ₀ / 3 → False ∨ τ < 6 * σ - 3

/-- A complete endpoint scale certificate.  Its fields are precisely the
finite exponent obligations left after the zero-density-from-large-values
reduction has produced a large-value pattern. -/
structure EndpointScaleCertificate (σ τ₀ : ℝ) : Prop where
  tau0_pos : 0 < τ₀
  density_base_le_tau0 : 3 - 3 * σ ≤ τ₀
  mhh_window : ∀ τ : ℝ, 0 ≤ τ → τ ≤ τ₀ + σ - 1 →
    classicalMHHExponent σ τ ≤ 2 - 2 * σ
  subdivision_window : ∀ τ : ℝ,
    2 * τ₀ / 3 ≤ τ → τ ≤ τ₀ →
      corollary1110Envelope σ τ₀ τ ≤ (3 - 3 * σ) * τ / τ₀
  raised_scale_window : ∀ τ : ℝ,
    4 * τ₀ / 3 ≤ τ → τ ≤ 8 * τ₀ / 3 →
      (2 * τ₀ / 3 ≤ τ / 2 ∧ τ / 2 ≤ τ₀) ∨
        (2 * τ₀ / 3 ≤ τ / 3 ∧ τ / 3 ≤ τ₀)
  zeta_window : ZetaWindowResolved σ τ₀

/-- Ingham's choice `τ₀ = 2-σ` satisfies every finite scale and exponent
obligation in the interior of its range. -/
theorem ingham_endpoint_scale_certificate
    {σ : ℝ} (hσLower : 1 / 2 < σ) (hσUpper : σ < 1) :
    EndpointScaleCertificate σ (2 - σ) := by
  refine ⟨by linarith, by linarith, ?_, ?_, ?_, ?_⟩
  · intro τ _hτNonneg hτ
    apply classicalMHHExponent_le_montgomery_of_tau_le_one
    linarith
  · intro τ hτLower hτUpper
    exact corollary1110Envelope_le_target hσUpper.le (by linarith)
      (by linarith) hτLower hτUpper
  · intro τ hτLower hτUpper
    exact exists_two_or_three_scale_reduction hτLower hτUpper
  · intro τ hτLower hτUpper
    left
    exact ingham_zeta_polynomial_range_empty hσLower hτLower hτUpper

/-- Huxley's choice `τ₀ = 3σ-1` satisfies every finite scale and exponent
obligation in the interior of its range. -/
theorem huxley_endpoint_scale_certificate
    {σ : ℝ} (hσLower : 3 / 4 < σ) (hσUpper : σ < 1) :
    EndpointScaleCertificate σ (3 * σ - 1) := by
  refine ⟨by linarith, by linarith, ?_, ?_, ?_, ?_⟩
  · intro τ _hτNonneg hτ
    apply classicalMHHExponent_le_montgomery_of_tau_le_four_sigma_sub_two
    linarith
  · intro τ hτLower hτUpper
    exact corollary1110Envelope_le_target hσUpper.le (by linarith)
      (by linarith) hτLower hτUpper
  · intro τ hτLower hτUpper
    exact exists_two_or_three_scale_reduction hτLower hτUpper
  · intro τ hτLower hτUpper
    by_cases hσ : σ ≤ 5 / 6
    · left
      exact huxley_zeta_polynomial_range_empty hσ hτLower hτUpper
    · right
      exact huxley_zeta_polynomial_range_below_weyl (lt_of_not_ge hσ) hτUpper

/-- The complete, concrete finite scale/exponent assembly used by both
classical endpoints.  The analytic MHH input is included here as the actual
kernel-checked theorem rather than as a new assumption. -/
def ClassicalFiniteScaleExponentAssembly : Prop :=
  ClassicalMontgomeryHalaszHuxley ∧
    (∀ σ : ℝ, 1 / 2 < σ → σ < 1 →
      EndpointScaleCertificate σ (2 - σ)) ∧
    (∀ σ : ℝ, 3 / 4 < σ → σ < 1 →
      EndpointScaleCertificate σ (3 * σ - 1))

theorem classical_finite_scale_exponent_assembly_native :
    ClassicalFiniteScaleExponentAssembly := by
  refine ⟨classical_montgomery_halasz_huxley_native, ?_, ?_⟩
  · intro σ hσLower hσUpper
    exact ingham_endpoint_scale_certificate hσLower hσUpper
  · intro σ hσLower hσUpper
    exact huxley_endpoint_scale_certificate hσLower hσUpper

end RiemannZeta.GuthMaynard
