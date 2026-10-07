import Dubon2026.ProjectiveTranslationStrip
import Dubon2026.FundamentalDomainUnfolding

/-! # Actual Γ₀ coset unfolding for the Petersson density -/

namespace Dubon2026

open UpperHalfPlane CongruenceSubgroup MeasureTheory Set
open scoped MatrixGroups ENNReal ModularForm

noncomputable section

/-- Actual parabolic cosets form a countable index set. -/
instance gamma0ProjectiveTranslationCosetsCountable (Q : ℕ) :
    Countable ((projectiveGamma0 Q) ⧸ gamma0ProjectiveTranslations Q) :=
  Quotient.countable

/-- The actual nonnegative parabolic-coset Eisenstein sum for real parameters. -/
def gamma0CosetEisensteinNN (Q : ℕ) (σ : ℝ) (z : ℍ) : ℝ≥0∞ :=
  ∑' q : (projectiveGamma0 Q) ⧸ gamma0ProjectiveTranslations Q,
    ENNReal.ofReal ((q.out⁻¹ • z).im ^ σ)

/-- The literal unit strip unfolds every measurable translation-invariant nonnegative function. -/
theorem gamma0_translation_coset_unfold (Q : ℕ) [NeZero Q]
    (F : ℍ → ℝ≥0∞) (hF : Measurable F)
    (hFinv : ∀ (g : gamma0ProjectiveTranslations Q) z, F (g • z) = F z) :
    (∫⁻ z in gamma0FundamentalDomain Q,
      ∑' q : (projectiveGamma0 Q) ⧸ gamma0ProjectiveTranslations Q, F (q.out⁻¹ • z)) =
      ∫⁻ z in upperHalfPlaneUnitStrip, F z :=
  fundamentalDomain_subgroup_unfold_lintegral (gamma0ProjectiveTranslations Q)
    (isFundamentalDomain_gamma0 Q) (isFundamentalDomain_gamma0Translations Q) F hF hFinv

/-- The genuine Petersson density unfolds with the actual parabolic-coset Eisenstein series. -/
theorem gamma0_petersson_coset_unfold {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k) (σ : ℝ) :
    (∫⁻ z in gamma0FundamentalDomain Q,
      gamma0CosetEisensteinNN Q σ z * ENNReal.ofReal ‖petersson k f f z‖) =
    ∫⁻ z in upperHalfPlaneUnitStrip,
      ENNReal.ofReal (z.im ^ σ) * ENNReal.ofReal ‖petersson k f f z‖ := by
  have hpow : Continuous (fun z : ℍ => z.im ^ σ) :=
    UpperHalfPlane.continuous_im.rpow_const (fun z => Or.inl z.im_ne_zero)
  have hF : Measurable (fun z : ℍ =>
      ENNReal.ofReal (z.im ^ σ) * ENNReal.ofReal ‖petersson k f f z‖) :=
    hpow.measurable.ennreal_ofReal.mul
      (petersson_continuous k (ModularFormClass.continuous f)
        (ModularFormClass.continuous f)).norm.measurable.ennreal_ofReal
  have hinv : ∀ (g : gamma0ProjectiveTranslations Q) z,
      ENNReal.ofReal ((g • z).im ^ σ) * ENNReal.ofReal ‖petersson k f f (g • z)‖ =
        ENNReal.ofReal (z.im ^ σ) * ENNReal.ofReal ‖petersson k f f z‖ := by
    intro g z
    have hp := petersson_projectiveGamma0_invariant Q f f g.val z
    change petersson k f f (g • z) = _ at hp
    rw [hp]
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp g.property
    have hi : (g • z).im = z.im := by
      change (g.val • z).im = _
      rw [← hn, gamma0ProjectiveT_zpow_smul, vadd_im]
    rw [hi]
  have hu := gamma0_translation_coset_unfold Q _ hF hinv
  convert hu using 1
  apply lintegral_congr
  intro z
  rw [gamma0CosetEisensteinNN, ← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro q
  rw [petersson_projectiveGamma0_invariant Q f f q.out⁻¹ z]

end
end Dubon2026
