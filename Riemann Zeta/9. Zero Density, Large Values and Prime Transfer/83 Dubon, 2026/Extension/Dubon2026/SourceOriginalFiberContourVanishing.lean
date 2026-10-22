import Dubon2026.SourceOriginalFiberContourSums
import Dubon2026.SourceOriginalSimpleFiberSum
import Dubon2026.SourceOriginalFiberCoefficients
import Dubon2026.SourceComplexSimpleFiberContour

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

attribute [local instance] originalFiberDifferentialModule

theorem originalFiberContourDerivative_eq_zero {n : ℕ} (bb : Fin n → Ω[F⁄ℂ])
    (P₀ : Place ℂ F) (f : F) (h : Fin n → F) (t₀ : ℂ) (Z₀ : Finset (Place ℂ F))
    (Z : ℂ → Divisor ℂ F) (j : OriginalFiberIndexing N bb P₀ f h t₀ Z₀ Z)
    (hhreg : ∀ i, (h i • D ℂ F f : Ω[F⁄ℂ]) ∈ regularDifferentials ℂ F)
    (hZ : ∀ (t : ℂ) (v : Place ℂ F), Z t v = max (v.ord (f - algebraMap ℂ F t)) 0)
    {t : ℂ} (ht : t ∈ ball t₀ j.ε) (htne : t ≠ t₀) :
    originalFiberContourDerivative N bb P₀ f h t₀ Z₀ Z j t = 0 := by
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

  have hsupp : ∀ (t : ℂ) (w : Place ℂ F), w ∈ (Z t).support ↔ 0 < w.ord (f - algebraMap ℂ F t) := by
    intro t w
    rw [Finsupp.mem_support_iff, hZ t w]
    omega
  change L' t = 0
  have hJ0 : ∀ v : Place ℂ F, (∮ z in C((0 : ℂ), r v),
      deriv (fun _ : ℂ => (1 : ℂ)) z / (chartRead N v f z - t)) = 0 := fun v => by
    simp [circleIntegral]

  have hsimpleZ : ∀ v ∈ Z₀, ∀ a ∈ Zf v t, a ≠ (0 : ℂ) ∧
      deriv (chartRead N v f) a ≠ 0 ∧
      ∀ i, readDifferential N v (bb i) a = chartRead N v (h i) a * deriv (chartRead N v f) a := by
    intro v hv a ha
    obtain ⟨-, -, haball, hRa, -⟩ := hfibB t ht v hv a ha
    have hac : a ≠ (0 : ℂ) := fun h0 => htne (by rw [← hRa, h0, hRc v hv])
    exact ⟨hac, (hpunct v hv a (hbb' v haball) hac).2⟩
  have hJ : ∀ v ∈ Z₀, ∀ i, (∮ z in C((0 : ℂ), r v),
      deriv (Φ v i) z / (chartRead N v f z - t)) =
      2 * Real.pi * Complex.I * ∑ a ∈ Zf v t, originalPlaceEval N ℂ (sy v a) (h i) := by
    intro v hv i
    have h1 : (∮ z in C((0 : ℂ), r v), deriv (Φ v i) z / (chartRead N v f z - t)) =
        ∮ z in C((0 : ℂ), r v),
          readDifferential N v (bb i) z / (chartRead N v f z - t) := by
      refine circleIntegral.integral_congr (hr v).le fun z hz => ?_
      simp only [(hΦd v hv i z (hsph v hz)).deriv]
    rw [h1, circleIntegral_div_sub_eq_sum (hr v) (fun z hz => hRan v hv z (hcb v hz))
      (fun z hz => hΨan v hv i z (hcb v hz)) (hcirc' t ht v hv) (Zf v t) (hZf v hv t ht)
      (fun a ha => (hsimpleZ v hv a ha).2.1)]
    congr 1
    refine Finset.sum_congr rfl fun a ha => ?_
    obtain ⟨-, hda, hread⟩ := hsimpleZ v hv a ha
    rw [hread i, mul_div_cancel_right₀ _ hda, chartRead]
    rfl

  have hsimple : ∀ w : Place ℂ F, 0 < w.ord (f - algebraMap ℂ F t) →
      w.ord (f - algebraMap ℂ F t) = 1 := by
    intro w hw
    obtain ⟨v, hv, hwsrc, ha, hord⟩ := hfibA t ht w hw
    obtain ⟨-, hda, -⟩ := hsimpleZ v hv _ ha
    obtain ⟨-, -, haball, hRa, -⟩ := hfibB t ht v hv _ ha
    have h1 : analyticOrderAt (fun z => chartRead N v f z - t) (placeChart N v w) = 1 := by
      have := (hRan v hv _ (hbb' v haball)).analyticOrderAt_sub_eq_one_of_deriv_ne_zero hda
      rwa [hRa] at this
    have hm1 : m v t (placeChart N v w) = 1 := by
      simp only [hmdef, analyticOrderNatAt, h1, ENat.toNat_one]
    rw [hord]
    exact_mod_cast hm1
  have htrace : ∀ i, ∑ w ∈ (Z t).support, originalPlaceEval N ℂ w (h i) = 0 := fun i =>
    original_sum_simple_fiber_eq_zero N f (h i)
      (hhreg i) t hsimple (Z t).support (hsupp t)

  have hv_eq : ∀ v ∈ Z₀,
      ((k * ∮ z in C((0 : ℂ), r v),
          deriv (fun _ => (1 : ℂ)) z / (chartRead N v f z - t)) • (A v - Φc v) +
        k • fun i => ∮ z in C((0 : ℂ), r v),
          deriv (Φ v i) z / (chartRead N v f z - t)) =
      fun i => ∑ a ∈ Zf v t, originalPlaceEval N ℂ (sy v a) (h i) := by
    intro v hv
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hJ0 v, hJ v hv i, mul_zero, zero_mul,
      zero_add]
    rw [← mul_assoc, hkdef, inv_mul_cancel₀ h2pi, one_mul]
  simp only [hL'def]
  rw [Finset.sum_congr rfl hv_eq]
  funext i
  rw [Finset.sum_apply, Pi.zero_apply,
    ← sum_eq_sum_sum (Z t).support Z₀ (fun v => Zf v t) sy (hsurj t ht) (hmem t ht) (hinj t ht)
      (fun w => originalPlaceEval N ℂ w (h i))]
  exact htrace i


end
end Dubon2026.SourceFunctionField.OriginalChart
