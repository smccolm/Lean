import Dubon2026.SourceComplexDipolePairing

/-! Adapted from anthropics/fermats-last-theorem (Apache-2.0), pinned
S_UpperHalfPlane_exists_localModel_pair_integral_mul_dbarLogDeriv_eq.
DUB-17/18 -> original all-weight arithmetic association -> actual Gamma1
Picard/H1 -> Abel-Jacobi converse -> analytic reciprocity -> smooth invariant
comparison function -> compact dipole with exact integer local orders.
The existing wedge/residue identity and antiholomorphic derivative are reused.
This constructs a smooth local comparison, without assuming meromorphic
realization or the desired principal-divisor converse. -/
namespace Dubon2026.SourceComplexReciprocity.Dipole
noncomputable section
open Complex MeasureTheory Filter Set Metric DbarFundamental
open scoped Real Topology Manifold ContDiff
local notation "𝕌" => UpperHalfPlane.upperHalfPlaneSet



theorem exists_cutoff {A B : Set ℂ} (hA : IsClosed A) (hB : IsOpen B) (hAB : A ⊆ B) :
    ∃ f : ℂ → ℝ, ContDiff ℝ 2 f ∧ (∀ z ∈ A, f z = 1) ∧ (∀ z ∉ B, f z = 0) ∧
      ∀ z, f z ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨f, h0, h1, h01⟩ := exists_contMDiffMap_zero_one_of_isClosed 𝓘(ℝ, ℂ) hB.isClosed_compl hA
    (disjoint_compl_left_iff.2 hAB) (n := 2)
  exact ⟨f, contMDiff_iff_contDiff.1 f.contMDiff, fun z hz => h1 hz, fun z hz => h0 hz, h01⟩

theorem exists_localModel_pair (b s : ℂ) (hb : 0 < b.im) (hs : 0 < s.im) (hbs : b ≠ s) :
    ∃ d F : ℂ → ℂ, ∃ K : Set ℂ, IsCompact K ∧ K ⊆ 𝕌 ∧
      (∀ z ∉ K, d z = 1) ∧
      (∀ τ : ℂ, 0 < τ.im → ∃ Ψ : ℂ → ℂ, ContDiffAt ℝ 1 Ψ τ ∧ Ψ τ ≠ 0 ∧
        d =ᶠ[𝓝 τ] fun z =>
          (z - τ) ^ ((if τ = s then (1 : ℤ) else 0) - (if τ = b then (1 : ℤ) else 0)) * Ψ z) ∧
      Continuous F ∧ HasCompactSupport F ∧ tsupport F ⊆ K ∧
      (∀ z : ℂ, 0 < z.im → z ≠ b →
        (fderiv ℝ d z 1 + I * fderiv ℝ d z I) / 2 / d z = F z) ∧
      ∀ E E' : ℂ → ℂ, (∀ z : ℂ, 0 < z.im → HasDerivAt E (E' z) z) →
        Integrable (fun z : ℂ => E' z * F z) ∧ ∫ z : ℂ, E' z * F z = π * (E s - E b) := by
  have hUo : IsOpen (𝕌 : Set ℂ) := Complex.continuous_im.isOpen_preimage _ isOpen_Ioi
  set Seg := segment ℝ b s with hSegdef
  have hSegc : IsCompact Seg := by
    rw [hSegdef, segment_eq_image]
    exact isCompact_Icc.image (by continuity)
  obtain ⟨δ, hδ, hδU⟩ := hSegc.exists_cthickening_subset_open hUo ((convex_halfSpace_im_gt 0).segment_subset hb hs)
  set ε := δ / 4 with hε
  have hε0 : 0 < ε := by positivity

  set O := thickening ε Seg with hOdef
  set K := cthickening (2 * ε) Seg with hKdef
  set O' := thickening (3 * ε) Seg with hO'def
  have hO : IsOpen O := isOpen_thickening
  have hO'o : IsOpen O' := isOpen_thickening
  have hSegO : Seg ⊆ O := self_subset_thickening hε0 _
  have hOK : O ⊆ K := (thickening_mono (by linarith) _).trans (thickening_subset_cthickening _ _)
  have hKc : IsCompact K := hSegc.cthickening
  have hKO' : K ⊆ O' := cthickening_subset_thickening' (by linarith) (by linarith) _
  have hK4 : cthickening (4 * ε) Seg ⊆ 𝕌 := by
    have : 4 * ε = δ := by rw [hε]; ring
    rw [this]; exact hδU
  have hKU : K ⊆ 𝕌 := (cthickening_mono (by linarith) _).trans hK4

  obtain ⟨χ, hχ, hχ1, hχ0, h01⟩ := exists_cutoff (A := cthickening ε Seg) (B := thickening (2 * ε) Seg)
    isClosed_cthickening isOpen_thickening (cthickening_subset_thickening' (by linarith) (by linarith) _)
  have hχ1' : ∀ z ∈ O, χ z = 1 := fun z hz => hχ1 z (thickening_subset_cthickening _ _ hz)
  have hχK : tsupport χ ⊆ K := by
    refine closure_minimal (fun z hz => ?_) isClosed_cthickening
    exact thickening_subset_cthickening _ _ (by by_contra h; exact hz (hχ0 z h))
  obtain ⟨η₀, hη₀, hη1, hη0, -⟩ := exists_cutoff (A := cthickening (3 * ε) Seg)
    (B := thickening (4 * ε) Seg) isClosed_cthickening isOpen_thickening
    (cthickening_subset_thickening' (by linarith) (by linarith) _)
  set η : ℂ → ℂ := fun z => (η₀ z : ℂ) with hηdef
  have hη : ContDiff ℝ 2 η := ofRealCLM.contDiff.comp hη₀
  have hηt : tsupport η ⊆ cthickening (4 * ε) Seg := by
    have : tsupport η = tsupport η₀ := by
      simp only [tsupport, hηdef]; congr 1; ext z; simp
    rw [this]
    refine closure_minimal (fun z hz => ?_) isClosed_cthickening
    exact thickening_subset_cthickening _ _ (by by_contra h; exact hz (hη0 z h))
  have hηs : HasCompactSupport η := (hSegc.cthickening).of_isClosed_subset (isClosed_tsupport _) hηt
  have hηU : tsupport η ⊆ 𝕌 := hηt.trans hK4
  have hη1' : ∀ z ∈ O', η z = 1 := fun z hz => by
    simp [hηdef, hη1 z (thickening_subset_cthickening _ _ hz)]
  have hbK : b ∈ K := hOK (hSegO (left_mem_segment _ _ _))
  refine ⟨dfun b s χ, Ffun b s χ, K, hKc, hKU, fun z hz => dfun_eq_one hχK hz hbK,
    fun τ _ => dfun_localModel hbs hχ hO hSegO hχ1' h01 τ,
    continuous_Ffun hχ hO hSegO hχ1' h01,
    hKc.of_isClosed_subset (isClosed_tsupport _) (tsupport_Ffun_subset isClosed_cthickening hχK),
    tsupport_Ffun_subset isClosed_cthickening hχK,
    fun z _ hz => dbar_dfun_div hχ hO hSegO hχ1' h01 hz, fun E E' hE => ?_⟩
  exact pairing hbs hχ hO hSegO hχ1' hOK isClosed_cthickening hχK h01 hη hηs hηU hO'o hKO'
    hη1' E E' hE

end
end Dubon2026.SourceComplexReciprocity.Dipole
