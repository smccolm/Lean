import Dubon2026.Gamma0EisensteinUnfolding
import Dubon2026.CuspCosetTrace

/-! # Genuine Eisenstein unfolding of a full-level invariant finite cusp trace -/

namespace Dubon2026

open UpperHalfPlane Matrix.SpecialLinearGroup CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ENNReal

noncomputable section

/-- At level one the actual projective subgroup exhausts the modular group. -/
theorem mem_projectiveGamma0_one (g : PSL(2, ℤ)) : g ∈ projectiveGamma0 1 := by
  induction g using Quotient.inductionOn with | h δ => ?_
  exact ⟨δ, by change δ ∈ Gamma0 1; rw [Gamma0_mem]; exact Subsingleton.elim _ _, rfl⟩

/-- The standard open domain is a genuine domain for the actual level-one projective subgroup. -/
theorem isFundamentalDomain_fdo_projectiveGamma0_one :
    IsFundamentalDomain (projectiveGamma0 1) (ModularGroup.fdo : Set ℍ) (volume : Measure ℍ) := by
  let e : projectiveGamma0 1 ≃ PSL(2, ℤ) := {
    toFun := Subtype.val
    invFun := fun g => ⟨g, mem_projectiveGamma0_one g⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have h := isFundamentalDomain_fdo_PSL.image_of_equiv (Equiv.refl ℍ)
    (Measure.QuasiMeasurePreserving.id _) e (fun _ _ => rfl)
  simpa using h

/-- The genuine full-level primitive Eisenstein series unfolds every measurable invariant nonnegative weight. -/
theorem fullLevel_eisenstein_weight_unfold (G : ℍ → ℝ≥0∞) (hG : Measurable G)
    (hInv : ∀ (g : SL(2, ℤ)) z, G (g • z) = G z) {σ : ℝ} (hσ : 1 < σ) :
    (∫⁻ z in ModularGroup.fdo, ENNReal.ofReal (gamma0Eisenstein 1 (σ : ℂ) z).re * G z) =
      ∫⁻ z in upperHalfPlaneUnitStrip, ENNReal.ofReal (z.im ^ σ) * G z := by
  have hP (g : projectiveGamma0 1) (z : ℍ) : G (g • z) = G z := by
    obtain ⟨δ, _, he⟩ := g.property
    change G (g.val • z) = _
    rw [← he]
    exact hInv δ z
  have hpow : Continuous (fun z : ℍ => z.im ^ σ) :=
    UpperHalfPlane.continuous_im.rpow_const (fun z => Or.inl z.im_ne_zero)
  have hF : Measurable (fun z : ℍ => ENNReal.ofReal (z.im ^ σ) * G z) :=
    hpow.measurable.ennreal_ofReal.mul hG
  have ht : ∀ (g : gamma0ProjectiveTranslations 1) z,
      ENNReal.ofReal ((g • z).im ^ σ) * G (g • z) = ENNReal.ofReal (z.im ^ σ) * G z := by
    intro g z
    rw [show G (g • z) = G z from hP g.val z]
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp g.property
    have hi : (g • z).im = z.im := by
      change (g.val • z).im = _
      rw [← hn, gamma0ProjectiveT_zpow_smul, vadd_im]
    rw [hi]
  have hu := fundamentalDomain_subgroup_unfold_lintegral (gamma0ProjectiveTranslations 1)
    isFundamentalDomain_fdo_projectiveGamma0_one (isFundamentalDomain_gamma0Translations 1)
    _ hF ht
  simp_rw [gamma0Eisenstein_re_eq_cosetNN 1 hσ]
  convert hu using 1
  apply lintegral_congr
  intro z
  rw [gamma0CosetEisensteinNN, ← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro q
  rw [hP q.out⁻¹ z]

/-- The actual finite cusp Petersson trace is a legitimate full-level unfolding weight. -/
theorem fullLevel_eisenstein_cuspTrace_unfold {N : ℕ} {H : Subgroup SL(2, ℤ)}
    [Fintype (SL(2, ℤ) ⧸ H)] (hH : Gamma N ≤ H) {k : ℤ}
    (f : CuspForm (H.map (mapGL ℝ)) k) {σ : ℝ} (hσ : 1 < σ) :
    (∫⁻ z in ModularGroup.fdo, ENNReal.ofReal (gamma0Eisenstein 1 (σ : ℂ) z).re *
      ENNReal.ofReal (∑ q : SL(2, ℤ) ⧸ H,
        ‖petersson k (cuspCosetFamily hH f q) (cuspCosetFamily hH f q) z‖)) =
      ∫⁻ z in upperHalfPlaneUnitStrip, ENNReal.ofReal (z.im ^ σ) *
        ENNReal.ofReal (∑ q : SL(2, ℤ) ⧸ H,
          ‖petersson k (cuspCosetFamily hH f q) (cuspCosetFamily hH f q) z‖) := by
  apply fullLevel_eisenstein_weight_unfold _ _ _ hσ
  · exact (continuous_finsetSum _ (fun q _ =>
      (petersson_continuous k (ModularFormClass.continuous (cuspCosetFamily hH f q))
        (ModularFormClass.continuous (cuspCosetFamily hH f q))).norm)).measurable.ennreal_ofReal
  · intro g z
    rw [cusp_petersson_trace_invariant hH f g z]

end
end Dubon2026
