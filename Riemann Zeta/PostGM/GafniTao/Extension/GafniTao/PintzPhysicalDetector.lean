import GafniTao.PintzFiniteDensity

/-!
# Pintz's detector on the physical zeta-zero set

The source variables `eta_j` and `gamma_j` are recovered here from an actual
member of `zeroSet (1-eta) T`.  The uniform three-regime zeta window then
discharges both horizontal edges and the equation-(4.8) factor.
-/

open Complex Set

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

/-- General membership data for the frozen symmetric zero set. -/
theorem mem_zeroSet_data {sigma T : ℝ} {rho : ℂ}
    (hrho : rho ∈ zeroSet sigma T) :
    sigma ≤ rho.re ∧ rho.re ≤ 1 ∧ -T ≤ rho.im ∧
      rho.im ≤ T ∧ riemannZeta rho = 0 := by
  change rho ∈ RiemannZeta.GuthMaynard.zerosInRect sigma 1 (-T) T at hrho
  rw [RiemannZeta.GuthMaynard.zerosInRect,
    Set.Finite.mem_toFinset, Set.mem_inter_iff] at hrho
  have hrect :=
    (RiemannZeta.GuthMaynard.mem_ZeroRectangle sigma 1 (-T) T rho).mp hrho.1
  exact ⟨hrect.1, hrect.2.1, hrect.2.2.1, hrect.2.2.2, hrho.2⟩

/-- The strictly positive zeta envelope used simultaneously on the horizontal
edges and inside equation (4.8). -/
noncomputable def pintzPhysicalZetaMajorant (eta T : ℝ) : ℝ :=
  1 + pintzHorizontalZetaMajorant eta T

theorem pintzPhysicalZetaMajorant_pos
    {eta T : ℝ} (hT : 1 / 2 ≤ T) :
    0 < pintzPhysicalZetaMajorant eta T := by
  unfold pintzPhysicalZetaMajorant
  have := pintzHorizontalZetaMajorant_nonneg (eta := eta) hT
  linarith

/-- The physical lower bound furnished by equations (4.8)--(4.10). -/
noncomputable def pintzDetectedLowerBound (eta lambda T : ℝ) : ℝ :=
  1 / (32 * lambda *
    ((pintzPhysicalZetaMajorant eta T / eta) *
      Real.exp (1 / 4 - lambda * eta)))

/-- A single actual zeta zero in the near-one rectangle produces a large
value of Pintz's literal finite Möbius polynomial.  The remaining explicit
contour error is named as such and is discharged asymptotically in the next
module. -/
theorem exists_large_pintzDetectedPolynomial_of_mem_zeroSet
    {eta T lambda : ℝ} {rho : ℂ}
    (heta : 0 < eta) (hetaUpper : eta ≤ 1 / 4)
    (hlambda : pintzMobiusLambdaThreshold ≤ lambda)
    (hWindowLower : 2 * lambda + 3 < |rho.im|)
    (hWindowUpper : 2 * lambda ≤ T)
    (hrho : rho ∈ zeroSet (1 - eta) T)
    (hError : pintzEquation46ErrorBound (1 - rho.re) rho.im lambda
      (pintzPhysicalZetaMajorant eta T)
      (pintzPhysicalZetaMajorant eta T) ≤ 1 / 4) :
    ∃ u : ℝ, |rho.im - u| ≤ 2 * lambda ∧
      pintzDetectedLowerBound eta lambda T ≤
        ‖pintzDetectedPolynomialIcc (2 * eta)
          (pintzMobiusCutoff lambda) u‖ := by
  have hdata := mem_zeroSet_data hrho
  let etaJ : ℝ := 1 - rho.re
  let Z : ℝ := pintzPhysicalZetaMajorant eta T
  let F : ℝ := (Z / eta) * Real.exp (1 / 4 - lambda * eta)
  have hlambdaEight : 8 ≤ lambda :=
    pintzMobiusLambdaThreshold_ge_eight.trans hlambda
  have hlambdaPos : 0 < lambda := by linarith
  have hlambdaOne : 1 ≤ lambda := by linarith
  have hTpos : 0 < T := by
    have him : |rho.im| ≤ T := by
      rw [abs_le]
      exact ⟨hdata.2.2.1, hdata.2.2.2.1⟩
    have himPos : 0 < |rho.im| := by linarith
    exact himPos.trans_le him
  have hTOne : (1 : ℝ) ≤ T := by
    linarith
  have hetaJNonneg : 0 ≤ etaJ := by dsimp [etaJ]; linarith
  have hetaJUpper : etaJ ≤ eta := by dsimp [etaJ]; linarith
  have hdeltaJ : 0 ≤ pintzDeltaJ eta etaJ := by
    unfold pintzDeltaJ
    linarith
  have hxi : pintzXi eta eta ≤ 1 / 2 := by
    unfold pintzXi
    linarith
  have hleftLower : -3 ≤ pintzLeftEdge eta eta etaJ := by
    unfold pintzLeftEdge pintzDeltaJ
    linarith
  have hleftUpper : pintzLeftEdge eta eta etaJ ≤ 3 := by
    unfold pintzLeftEdge pintzDeltaJ
    linarith
  have hheight : 2 * lambda < |rho.im| := by linarith
  have hZpos : 0 < Z := by
    dsimp [Z]
    exact pintzPhysicalZetaMajorant_pos (eta := eta) (by linarith)
  have hFpos : 0 < F := by
    dsimp [F]
    positivity
  have hShiftedHeight (R : ℝ) (hR : |R| ≤ 2 * lambda) :
      3 < |rho.im + R| ∧ |rho.im + R| ≤ 2 * T := by
    have hlower : |rho.im| - |R| ≤ |rho.im + R| := by
      have hraw := abs_sub_abs_le_abs_sub rho.im (-R)
      simpa [sub_neg_eq_add, abs_neg] using hraw
    have hupper : |rho.im + R| ≤ |rho.im| + |R| := abs_add_le _ _
    have him : |rho.im| ≤ T := by
      rw [abs_le]
      exact ⟨hdata.2.2.1, hdata.2.2.2.1⟩
    constructor <;> linarith
  have hHorizontal (R : ℝ) (hR : |R| = 2 * lambda) :
      ∀ x ∈ Set.Icc (pintzLeftEdge eta eta etaJ) 3,
        ‖riemannZeta (pintzRho etaJ rho.im +
          ((x : ℂ) + (R : ℂ) * I))‖ ≤ Z := by
    intro x hx
    have hheightR := hShiftedHeight R hR.le
    have hsigma : 1 - 2 * eta ≤ rho.re + x := by
      have hxLower := hx.1
      dsimp [etaJ] at hxLower
      unfold pintzLeftEdge pintzDeltaJ at hxLower
      linarith
    have hzeta := norm_riemannZeta_le_pintzHorizontalZetaMajorant
      heta.le hetaUpper hsigma hheightR.1 hheightR.2
    have hmajor : pintzHorizontalZetaMajorant eta T ≤ Z := by
      dsimp only [Z]
      unfold pintzPhysicalZetaMajorant
      linarith
    have hzeta' := hzeta.trans hmajor
    simpa [pintzRho, etaJ, mul_add, mul_comm, add_comm, add_left_comm,
      add_assoc] using hzeta'
  have hminus : ∀ x ∈ Set.Icc (pintzLeftEdge eta eta etaJ) 3,
      ‖riemannZeta (pintzRho etaJ rho.im +
        ((x : ℂ) + ((-2 * lambda : ℝ) : ℂ) * I))‖ ≤ Z :=
    hHorizontal (-2 * lambda) (by
      rw [abs_of_nonpos (by linarith : -2 * lambda ≤ 0)]
      ring)
  have hplus : ∀ x ∈ Set.Icc (pintzLeftEdge eta eta etaJ) 3,
      ‖riemannZeta (pintzRho etaJ rho.im +
        ((x : ℂ) + ((2 * lambda : ℝ) : ℂ) * I))‖ ≤ Z :=
    hHorizontal (2 * lambda) (abs_of_nonneg (by linarith))
  have hPintzZero : riemannZeta (pintzRho etaJ rho.im) = 0 := by
    rw [show pintzRho etaJ rho.im = rho by
      apply Complex.ext <;> simp [pintzRho, etaJ]]
    exact hdata.2.2.2.2
  have hlower := one_quarter_le_norm_pintzEquation46Integral
    (Delta := eta) (eta := eta) (etaJ := etaJ) (gamma := rho.im)
    (lambda := lambda) (Zminus := Z) (Zplus := Z)
    hPintzZero
    heta hdeltaJ hetaUpper hxi hlambda hheight hleftLower hleftUpper
    hZpos.le hZpos.le hminus hplus (by simpa [etaJ, Z] using hError)
  have hFpoint : ∀ t ∈ Set.Icc (-2 * lambda) (2 * lambda),
      ‖pintzF eta eta etaJ rho.im lambda t‖ ≤ F := by
    intro t ht
    have hheightT := hShiftedHeight t (by
      rw [abs_le]
      simpa [neg_mul] using ht)
    have hzeta := norm_riemannZeta_le_pintzHorizontalZetaMajorant
      heta.le hetaUpper (sigma := 1 - 2 * eta)
      (by linarith) hheightT.1 hheightT.2
    have hmajor : pintzHorizontalZetaMajorant eta T ≤ Z := by
      dsimp only [Z]
      unfold pintzPhysicalZetaMajorant
      linarith
    have hzetaZ := hzeta.trans hmajor
    have hraw := norm_pintzF_le
      (Delta := eta) (eta := eta) (etaJ := etaJ) (gamma := rho.im)
      (lambda := lambda) (t := t) (Z := Z)
      heta hdeltaJ hetaJNonneg hxi hlambdaOne
      hZpos.le (by
        simpa only [pintzXi, two_mul, Complex.ofReal_add] using hzetaZ)
    simpa [F, Z] using hraw
  obtain ⟨u, hu, hlarge⟩ := exists_large_pintzDetectedPolynomial
    (Delta := eta) (eta := eta) (etaJ := etaJ) (gamma := rho.im)
    (lambda := lambda) (F := F)
    hPintzZero
    heta hdeltaJ hlambdaPos hFpos hlower hFpoint
  refine ⟨u, ?_, ?_⟩
  · rw [abs_le]
    constructor <;> linarith [hu.1, hu.2]
  · rw [← pintzDetectedPolynomial_eq_Icc]
    have hxiEq : pintzXi eta eta = 2 * eta := by
      unfold pintzXi
      ring
    rw [← hxiEq]
    simpa [pintzDetectedLowerBound, F, Z] using hlarge

#print axioms mem_zeroSet_data
#print axioms exists_large_pintzDetectedPolynomial_of_mem_zeroSet

end

end GafniTao
