import Dubon2026.SourceOriginalFiberContourSums
import Dubon2026.SourceComplexFiberContourDerivative

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi -> principal
divisor kernel -> constancy of the exact weighted fiber contour. These
functions are the literal contour sums on the actual original chart disks.
Their comparison, derivative and vanishing are proved separately under
the existing limits, retaining the exact coefficients and multiplicities.
Adapted from S_AlgebraicCurve_eventually_abelJacobiDiv_fibre_sub_mem_pathPeriodLattice,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Filter Set Metric KaehlerDifferential ComplexFiberContour
open scoped Topology
variable (N : ℕ) [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ
attribute [local instance] placeTopology

theorem hasDerivAt_originalFiberContourSum {n : ℕ} (bb : Fin n → Ω[F⁄ℂ])
    (P₀ : Place ℂ F) (f : F) (h : Fin n → F) (t₀ : ℂ) (Z₀ : Finset (Place ℂ F))
    (Z : ℂ → Divisor ℂ F) (j : OriginalFiberIndexing N bb P₀ f h t₀ Z₀ Z)
    {t : ℂ} (ht : t ∈ ball t₀ j.ε) :
    HasDerivAt (originalFiberContourSum N bb P₀ f h t₀ Z₀ Z j)
      (originalFiberContourDerivative N bb P₀ f h t₀ Z₀ Z j t) t := by
  classical
  let Λ := pathPeriodLattice N bb
  obtain ⟨⟨⟨O, ρ, Φ, hρ, hOdisj, htar, hOf, hΦd, hAJloc, hRan, hRc, hpunct⟩,
    r, ε, Zf, hε, hzeros, hr, hcb, hbb', hsph, hΦan, hΨan, hcirc', hZf, hI0, hIΦ⟩,
    hfibA, hfibB, hsurj, hmem, hinj, hmult⟩ := j

  set A : Place ℂ F → (Fin n → ℂ) := fun v => abelJacobiVec N bb P₀ v with hAdef
  set Φc : Place ℂ F → (Fin n → ℂ) := fun v i => Φ v i ((0 : ℂ)) with hΦcdef
  set m : Place ℂ F → ℂ → ℂ → ℕ := fun v t a =>
    analyticOrderNatAt (fun z => chartRead N v f z - t) a with hmdef
  set sy : Place ℂ F → ℂ → Place ℂ F := fun v a => (placeChart N v).symm a with hsydef

  have h2pi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  set k : ℂ := (2 * Real.pi * Complex.I : ℂ)⁻¹ with hkdef
  set L : ℂ → (Fin n → ℂ) := fun t => ∑ v ∈ Z₀,
      ((k * ∮ z in C((0 : ℂ), r v),
          (fun _ => (1 : ℂ)) z * deriv (chartRead N v f) z / (chartRead N v f z - t)) • (A v - Φc v) +
        k • fun i => ∮ z in C((0 : ℂ), r v),
          Φ v i z * deriv (chartRead N v f) z / (chartRead N v f z - t)) with hLdef
  set L' : ℂ → (Fin n → ℂ) := fun t => ∑ v ∈ Z₀,
      ((k * ∮ z in C((0 : ℂ), r v),
          deriv (fun _ => (1 : ℂ)) z / (chartRead N v f z - t)) • (A v - Φc v) +
        k • fun i => ∮ z in C((0 : ℂ), r v),
          deriv (Φ v i) z / (chartRead N v f z - t)) with hL'def

  change HasDerivAt L (L' t) t
  simp only [hLdef, hL'def]
  refine HasDerivAt.fun_sum fun v hv => ?_
  have hsphR : ∀ z ∈ Metric.sphere ((0 : ℂ)) (r v),
      AnalyticAt ℂ (chartRead N v f) z := fun z hz => hRan v hv z (hsph v hz)
  have hB0 := hasDerivAt_circleIntegral_mul_deriv_div_sub (G := fun _ => (1 : ℂ))
    (hr v) hsphR (fun z _ => analyticAt_const) (hcirc' t ht v hv)
  have hBi : ∀ i, HasDerivAt (fun s => ∮ z in C((0 : ℂ), r v),
        Φ v i z * deriv (chartRead N v f) z / (chartRead N v f z - s))
      (∮ z in C((0 : ℂ), r v), deriv (Φ v i) z / (chartRead N v f z - t)) t :=
    fun i => hasDerivAt_circleIntegral_mul_deriv_div_sub (hr v) hsphR
      (fun z hz => hΦan v hv i z (hsph v hz)) (hcirc' t ht v hv)
  exact ((hB0.const_mul k).smul_const _).add
    (HasDerivAt.const_smul k (hasDerivAt_pi.2 fun i => hBi i))


end
end Dubon2026.SourceFunctionField.OriginalChart
