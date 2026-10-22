import Dubon2026.SourceCellSixArcTrigonometry
import Dubon2026.SourceCellBoundaryGeometry

/-! DUB-17/18 -> original Abel-Jacobi -> paired analytic cell dissection.
The exact six-arc radial rectangle has prescribed split side segments,
endpoints, smooth pieces and segment-valued subarcs. These properties feed
ordinary grid-cell construction and neighboring-cell pairing.
Adapted from anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.RectSixArcs
open Real RectRadial

theorem r6_loop_re (R : RadialRegion) (φ : ℝ) :
    (R.loop φ).re = R.q.re + R.r φ * Real.cos φ := by
  simp only [RadialRegion.loop, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, zero_mul,
    sub_zero]

theorem r6_loop_im (R : RadialRegion) (φ : ℝ) :
    (R.loop φ).im = R.q.im + R.r φ * Real.sin φ := by
  simp only [RadialRegion.loop, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, zero_mul,
    add_zero]

theorem r6_re_cos {R : RadialRegion} {p : ℂ} (hq : R.q = p) {a φ : ℝ}
    (hcos : Real.cos φ ≠ 0) (hr : R.r φ = (Real.cos φ / a)⁻¹) : (R.loop φ).re = p.re + a := by
  rw [r6_loop_re, hq, hr, inv_div, div_mul_cancel₀ _ hcos]

theorem r6_im_cos {R : RadialRegion} {p : ℂ} (hq : R.q = p) {a φ : ℝ}
    (hr : R.r φ = (Real.cos φ / a)⁻¹) : (R.loop φ).im = p.im + a * Real.tan φ := by
  rw [r6_loop_im, hq, hr, inv_div, Real.tan_eq_sin_div_cos]
  ring

theorem r6_re_negcos {R : RadialRegion} {p : ℂ} (hq : R.q = p) {b φ : ℝ}
    (hcos : Real.cos φ ≠ 0) (hr : R.r φ = (-Real.cos φ / b)⁻¹) : (R.loop φ).re = p.re - b := by
  rw [r6_loop_re, hq, hr, inv_div, div_neg, neg_mul, div_mul_cancel₀ _ hcos, sub_eq_add_neg]

theorem r6_im_negcos {R : RadialRegion} {p : ℂ} (hq : R.q = p) {b φ : ℝ}
    (hr : R.r φ = (-Real.cos φ / b)⁻¹) : (R.loop φ).im = p.im - b * Real.tan φ := by
  rw [r6_loop_im, hq, hr, inv_div, div_neg, Real.tan_eq_sin_div_cos]
  ring

theorem r6_im_sin {R : RadialRegion} {p : ℂ} (hq : R.q = p) {c φ : ℝ}
    (hsin : Real.sin φ ≠ 0) (hr : R.r φ = (Real.sin φ / c)⁻¹) : (R.loop φ).im = p.im + c := by
  rw [r6_loop_im, hq, hr, inv_div, div_mul_cancel₀ _ hsin]

theorem r6_re_sin {R : RadialRegion} {p : ℂ} (hq : R.q = p) {c φ : ℝ}
    (hr : R.r φ = (Real.sin φ / c)⁻¹) :
    (R.loop φ).re = p.re + c * (Real.cos φ / Real.sin φ) := by
  rw [r6_loop_re, hq, hr, inv_div]
  ring

theorem r6_im_negsin {R : RadialRegion} {p : ℂ} (hq : R.q = p) {d φ : ℝ}
    (hsin : Real.sin φ ≠ 0) (hr : R.r φ = (-Real.sin φ / d)⁻¹) : (R.loop φ).im = p.im - d := by
  rw [r6_loop_im, hq, hr, inv_div, div_neg, neg_mul, div_mul_cancel₀ _ hsin, sub_eq_add_neg]

theorem r6_re_negsin {R : RadialRegion} {p : ℂ} (hq : R.q = p) {d φ : ℝ}
    (hr : R.r φ = (-Real.sin φ / d)⁻¹) :
    (R.loop φ).re = p.re - d * (Real.cos φ / Real.sin φ) := by
  rw [r6_loop_re, hq, hr, inv_div, div_neg]
  ring

/- As constructed below. -/
/-- Exact side image, injectivity, endpoints and straight subarcs of a radial boundary piece. -/
structure ArcData (R : RadialRegion) (u v : ℝ) (S : Set ℂ) (zu zv : ℂ) : Prop where
  image_eq : R.loop '' Set.Icc u v = S
  injOn : Set.InjOn R.loop (Set.Icc u v)
  loop_left : R.loop u = zu
  loop_right : R.loop v = zv
  image_sub : ∀ t₁ t₂ : ℝ, t₁ ∈ Set.Icc u v → t₂ ∈ Set.Icc u v → t₁ ≤ t₂ →
    R.loop '' Set.Icc t₁ t₂ = segment ℝ (R.loop t₁) (R.loop t₂)

theorem r6_image_mono {g : ℝ → ℝ} {u v cu cv : ℝ} (huv : u ≤ v)
    (hgc : ContinuousOn g (Set.Icc u v)) (hg : StrictMonoOn g (Set.Icc u v))
    (hgu : g u = cu) (hgv : g v = cv) : g '' Set.Icc u v = Set.Icc cu cv := by
  subst hgu
  subst hgv
  have hu : u ∈ Set.Icc u v := ⟨le_rfl, huv⟩
  have hv : v ∈ Set.Icc u v := ⟨huv, le_rfl⟩
  refine Set.Subset.antisymm ?_ (intermediate_value_Icc huv hgc)
  rintro _ ⟨φ, hφ, rfl⟩
  exact ⟨hg.monotoneOn hu hφ hφ.1, hg.monotoneOn hφ hv hφ.2⟩

theorem r6_image_anti {g : ℝ → ℝ} {u v cu cv : ℝ} (huv : u ≤ v)
    (hgc : ContinuousOn g (Set.Icc u v)) (hg : StrictAntiOn g (Set.Icc u v))
    (hgu : g u = cu) (hgv : g v = cv) : g '' Set.Icc u v = Set.Icc cv cu := by
  subst hgu
  subst hgv
  have hu : u ∈ Set.Icc u v := ⟨le_rfl, huv⟩
  have hv : v ∈ Set.Icc u v := ⟨huv, le_rfl⟩
  refine Set.Subset.antisymm ?_ (intermediate_value_Icc' huv hgc)
  rintro _ ⟨φ, hφ, rfl⟩
  exact ⟨hg.antitoneOn hφ hv hφ.2, hg.antitoneOn hu hφ hφ.1⟩

theorem r6_contOn_of_im (R : RadialRegion) {S : Set ℝ} {g : ℝ → ℝ}
    (him : ∀ φ ∈ S, (R.loop φ).im = g φ) : ContinuousOn g S := by
  have h : ContinuousOn (fun φ => (R.loop φ).im) S :=
    (Complex.continuous_im.comp (R.continuous_loop)).continuousOn
  exact h.congr fun φ hφ => (him φ hφ).symm

theorem r6_contOn_of_re (R : RadialRegion) {S : Set ℝ} {g : ℝ → ℝ}
    (hre : ∀ φ ∈ S, (R.loop φ).re = g φ) : ContinuousOn g S := by
  have h : ContinuousOn (fun φ => (R.loop φ).re) S :=
    (Complex.continuous_re.comp (R.continuous_loop)).continuousOn
  exact h.congr fun φ hφ => (hre φ hφ).symm

theorem r6_lineMap_vert (x c : ℝ) :
    AffineMap.lineMap (k := ℝ) (⟨x, 0⟩ : ℂ) (⟨x, 1⟩ : ℂ) c = (⟨x, c⟩ : ℂ) := by
  rw [AffineMap.lineMap_apply_module']
  apply Complex.ext
  · simp
  · simp

theorem r6_lineMap_horiz (y c : ℝ) :
    AffineMap.lineMap (k := ℝ) (⟨0, y⟩ : ℂ) (⟨1, y⟩ : ℂ) c = (⟨c, y⟩ : ℂ) := by
  rw [AffineMap.lineMap_apply_module']
  apply Complex.ext
  · simp
  · simp

theorem r6_loop_eq_vert (R : RadialRegion) {S : Set ℝ} {x : ℝ} {g : ℝ → ℝ}
    (hre : ∀ φ ∈ S, (R.loop φ).re = x) (him : ∀ φ ∈ S, (R.loop φ).im = g φ) :
    ∀ φ ∈ S, R.loop φ = AffineMap.lineMap (k := ℝ) (⟨x, 0⟩ : ℂ) (⟨x, 1⟩ : ℂ) (g φ) := by
  intro φ hφ
  rw [r6_lineMap_vert]
  exact Complex.ext (hre φ hφ) (him φ hφ)

theorem r6_loop_eq_horiz (R : RadialRegion) {S : Set ℝ} {y : ℝ} {g : ℝ → ℝ}
    (him : ∀ φ ∈ S, (R.loop φ).im = y) (hre : ∀ φ ∈ S, (R.loop φ).re = g φ) :
    ∀ φ ∈ S, R.loop φ = AffineMap.lineMap (k := ℝ) (⟨0, y⟩ : ℂ) (⟨1, y⟩ : ℂ) (g φ) := by
  intro φ hφ
  rw [r6_lineMap_horiz]
  exact Complex.ext (hre φ hφ) (him φ hφ)

theorem r6_image_Icc_eq_segment (R : RadialRegion) {u v : ℝ} {g : ℝ → ℝ}
    {A : ℝ →ᵃ[ℝ] ℂ} (hL : ∀ φ ∈ Set.Icc u v, R.loop φ = A (g φ))
    (hgc : ContinuousOn g (Set.Icc u v))
    (hg : StrictMonoOn g (Set.Icc u v) ∨ StrictAntiOn g (Set.Icc u v))
    {t₁ t₂ : ℝ} (h₁ : t₁ ∈ Set.Icc u v) (h₂ : t₂ ∈ Set.Icc u v) (h : t₁ ≤ t₂) :
    R.loop '' Set.Icc t₁ t₂ = segment ℝ (R.loop t₁) (R.loop t₂) := by
  have hsub : Set.Icc t₁ t₂ ⊆ Set.Icc u v := Set.Icc_subset_Icc h₁.1 h₂.2
  have hgc' : ContinuousOn g (Set.Icc t₁ t₂) := hgc.mono hsub
  have hgI : g '' Set.Icc t₁ t₂ = segment ℝ (g t₁) (g t₂) := by
    rcases hg with hg | hg
    · have hg' : StrictMonoOn g (Set.Icc t₁ t₂) := by
        intro a ha b hb hab
        exact hg (hsub ha) (hsub hb) hab
      have hI : g '' Set.Icc t₁ t₂ = Set.Icc (g t₁) (g t₂) := r6_image_mono h hgc' hg' rfl rfl
      have hle : g t₁ ≤ g t₂ := hg.monotoneOn h₁ h₂ h
      have hseg : segment ℝ (g t₁) (g t₂) = Set.Icc (g t₁) (g t₂) := segment_eq_Icc hle
      exact hI.trans hseg.symm
    · have hg' : StrictAntiOn g (Set.Icc t₁ t₂) := by
        intro a ha b hb hab
        exact hg (hsub ha) (hsub hb) hab
      have hI : g '' Set.Icc t₁ t₂ = Set.Icc (g t₂) (g t₁) := r6_image_anti h hgc' hg' rfl rfl
      have hge : g t₂ ≤ g t₁ := hg.antitoneOn h₁ h₂ h
      have hsymm : segment ℝ (g t₁) (g t₂) = segment ℝ (g t₂) (g t₁) := segment_symm ℝ (g t₁) (g t₂)
      have hseg : segment ℝ (g t₂) (g t₁) = Set.Icc (g t₂) (g t₁) := segment_eq_Icc hge
      exact hI.trans (hsymm.trans hseg).symm
  calc R.loop '' Set.Icc t₁ t₂ = (fun φ => A (g φ)) '' Set.Icc t₁ t₂ :=
        Set.image_congr fun φ hφ => hL φ (hsub hφ)
    _ = A '' (g '' Set.Icc t₁ t₂) := by rw [Set.image_image]
    _ = A '' segment ℝ (g t₁) (g t₂) := by rw [hgI]
    _ = segment ℝ (A (g t₁)) (A (g t₂)) := image_segment ℝ A (g t₁) (g t₂)
    _ = segment ℝ (R.loop t₁) (R.loop t₂) := by rw [hL t₁ h₁, hL t₂ h₂]

theorem r6_vert_arc (R : RadialRegion) {u v x lo hi cu cv : ℝ} {g : ℝ → ℝ} (huv : u ≤ v)
    (hre : ∀ φ ∈ Set.Icc u v, (R.loop φ).re = x)
    (him : ∀ φ ∈ Set.Icc u v, (R.loop φ).im = g φ)
    (hgS : g '' Set.Icc u v = Set.Icc lo hi)
    (hg : StrictMonoOn g (Set.Icc u v) ∨ StrictAntiOn g (Set.Icc u v))
    (hgu : g u = cu) (hgv : g v = cv) :
    ArcData R u v {z : ℂ | z.re = x ∧ z.im ∈ Set.Icc lo hi} ⟨x, cu⟩ ⟨x, cv⟩ := by
  have hu : u ∈ Set.Icc u v := ⟨le_rfl, huv⟩
  have hv : v ∈ Set.Icc u v := ⟨huv, le_rfl⟩
  have hginj : Set.InjOn g (Set.Icc u v) := hg.elim (fun h => h.injOn) (fun h => h.injOn)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ext z
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨φ, hφ, rfl⟩
      refine ⟨hre φ hφ, ?_⟩
      rw [him φ hφ, ← hgS]
      exact Set.mem_image_of_mem g hφ
    · rintro ⟨hzre, hzim⟩
      rw [← hgS] at hzim
      obtain ⟨φ, hφ, hgφ⟩ := hzim
      exact ⟨φ, hφ, Complex.ext ((hre φ hφ).trans hzre.symm) ((him φ hφ).trans hgφ)⟩
  · intro φ hφ ψ hψ hφψ
    apply hginj hφ hψ
    rw [← him φ hφ, ← him ψ hψ, hφψ]
  · exact Complex.ext (hre u hu) ((him u hu).trans hgu)
  · exact Complex.ext (hre v hv) ((him v hv).trans hgv)
  · intro t₁ t₂ h₁ h₂ h
    exact r6_image_Icc_eq_segment R (r6_loop_eq_vert R hre him) (r6_contOn_of_im R him) hg h₁ h₂ h

theorem r6_horiz_arc (R : RadialRegion) {u v y lo hi cu cv : ℝ} {g : ℝ → ℝ} (huv : u ≤ v)
    (him : ∀ φ ∈ Set.Icc u v, (R.loop φ).im = y)
    (hre : ∀ φ ∈ Set.Icc u v, (R.loop φ).re = g φ)
    (hgS : g '' Set.Icc u v = Set.Icc lo hi)
    (hg : StrictMonoOn g (Set.Icc u v) ∨ StrictAntiOn g (Set.Icc u v))
    (hgu : g u = cu) (hgv : g v = cv) :
    ArcData R u v {z : ℂ | z.im = y ∧ z.re ∈ Set.Icc lo hi} ⟨cu, y⟩ ⟨cv, y⟩ := by
  have hu : u ∈ Set.Icc u v := ⟨le_rfl, huv⟩
  have hv : v ∈ Set.Icc u v := ⟨huv, le_rfl⟩
  have hginj : Set.InjOn g (Set.Icc u v) := hg.elim (fun h => h.injOn) (fun h => h.injOn)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ext z
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨φ, hφ, rfl⟩
      refine ⟨him φ hφ, ?_⟩
      rw [hre φ hφ, ← hgS]
      exact Set.mem_image_of_mem g hφ
    · rintro ⟨hzim, hzre⟩
      rw [← hgS] at hzre
      obtain ⟨φ, hφ, hgφ⟩ := hzre
      exact ⟨φ, hφ, Complex.ext ((hre φ hφ).trans hgφ) ((him φ hφ).trans hzim.symm)⟩
  · intro φ hφ ψ hψ hφψ
    apply hginj hφ hψ
    rw [← hre φ hφ, ← hre ψ hψ, hφψ]
  · exact Complex.ext ((hre u hu).trans hgu) (him u hu)
  · exact Complex.ext ((hre v hv).trans hgv) (him v hv)
  · intro t₁ t₂ h₁ h₂ h
    exact r6_image_Icc_eq_segment R (r6_loop_eq_horiz R him hre) (r6_contOn_of_re R hre) hg h₁ h₂ h


end Dubon2026.SourceFunctionField.CellGeometry.RectSixArcs
