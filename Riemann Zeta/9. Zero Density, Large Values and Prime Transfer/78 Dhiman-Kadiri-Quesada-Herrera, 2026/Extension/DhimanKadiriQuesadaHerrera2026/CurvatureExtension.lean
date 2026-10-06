import DhimanKadiriQuesadaHerrera2026.StationaryTaylor
import Mathlib.Topology.UnitInterval

namespace DhimanKadiriQuesadaHerrera2026
open MeasureTheory

/-- Extend the actual curvature constantly beyond the two endpoints by projection. -/
noncomputable def extendedCurvature (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b) (x : ℝ) : ℝ :=
  deriv (deriv f) (Set.projIcc a b hab x)

/-- The extended first derivative is the primitive of the clamped actual curvature. -/
noncomputable def extendedSlope (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b) (c x : ℝ) : ℝ :=
  deriv f c + ∫ u in c..x, extendedCurvature f a b hab u

/-- Twice integrating the extended curvature constructs an actual extension of the source phase. -/
noncomputable def extendedPhase (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b) (c x : ℝ) : ℝ :=
  f c + ∫ u in c..x, extendedSlope f a b hab c u

/-- Projection leaves the curvature unchanged on the original interval, including both endpoints. -/
theorem extendedCurvature_eq {f : ℝ → ℝ} {a b x : ℝ} (hab : a ≤ b) (hx : x ∈ Set.Icc a b) :
    extendedCurvature f a b hab x = deriv (deriv f) x := by
  simp only [extendedCurvature, Set.projIcc_of_mem hab hx]

/-- The clamped curvature is continuous on the whole real line. -/
theorem continuous_extendedCurvature {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn (deriv (deriv f)) (Set.Icc a b)) :
    Continuous (extendedCurvature f a b hab) := by
  exact hf.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
    (fun x => (Set.projIcc a b hab x).property)

/-- The global slope primitive has the clamped curvature as its ordinary derivative. -/
theorem extendedSlope_hasDerivAt {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn (deriv (deriv f)) (Set.Icc a b)) (c x : ℝ) :
    HasDerivAt (extendedSlope f a b hab c) (extendedCurvature f a b hab x) x := by
  have hC := continuous_extendedCurvature hab hf
  exact (intervalIntegral.integral_hasDerivAt_right (hC.intervalIntegrable c x)
    hC.stronglyMeasurable.stronglyMeasurableAtFilter hC.continuousAt).const_add (deriv f c)

/-- The constructed phase has its specified first derivative globally. -/
theorem extendedPhase_hasDerivAt {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn (deriv (deriv f)) (Set.Icc a b)) (c x : ℝ) :
    HasDerivAt (extendedPhase f a b hab c) (extendedSlope f a b hab c x) x := by
  have hS : Continuous (extendedSlope f a b hab c) :=
    continuous_iff_continuousAt.mpr (fun x => (extendedSlope_hasDerivAt hab hf c x).continuousAt)
  exact (intervalIntegral.integral_hasDerivAt_right (hS.intervalIntegrable c x)
    hS.stronglyMeasurable.stronglyMeasurableAtFilter hS.continuousAt).const_add (f c)

/-- The ordinary second derivative of the extension is exactly its clamped curvature. -/
theorem extendedPhase_second_deriv {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn (deriv (deriv f)) (Set.Icc a b)) (c x : ℝ) :
    deriv (deriv (extendedPhase f a b hab c)) x = extendedCurvature f a b hab x := by
  have he : deriv (extendedPhase f a b hab c) = extendedSlope f a b hab c :=
    funext fun u => (extendedPhase_hasDerivAt hab hf c u).deriv
  rw [he, (extendedSlope_hasDerivAt hab hf c x).deriv]

/-- The extension preserves the actual first derivative everywhere in the source interval. -/
theorem extendedSlope_eq {f : ℝ → ℝ} {a b c x : ℝ} (hab : a ≤ b)
    (hc : c ∈ Set.Icc a b) (hx : x ∈ Set.Icc a b)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hfc : ContinuousOn (deriv (deriv f)) (Set.Icc a b)) :
    extendedSlope f a b hab c x = deriv f x := by
  have hs : Set.uIcc c x ⊆ Set.Icc a b := Set.uIcc_subset_Icc hc hx
  have he : (∫ u in c..x, extendedCurvature f a b hab u) = ∫ u in c..x, deriv (deriv f) u :=
    intervalIntegral.integral_congr (fun u hu => extendedCurvature_eq hab (hs hu))
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u hu => (hf' u (hs hu)).hasDerivAt)
    ((hfc.mono hs).intervalIntegrable)
  rw [extendedSlope, he, hi]
  ring

/-- The extension agrees with the actual original phase on its entire closed interval. -/
theorem extendedPhase_eq {f : ℝ → ℝ} {a b c x : ℝ} (hab : a ≤ b)
    (hc : c ∈ Set.Icc a b) (hx : x ∈ Set.Icc a b)
    (hf : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ f u)
    (hf' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv f) u)
    (hfc : ContinuousOn (deriv (deriv f)) (Set.Icc a b)) :
    extendedPhase f a b hab c x = f x := by
  have hs : Set.uIcc c x ⊆ Set.Icc a b := Set.uIcc_subset_Icc hc hx
  have he : (∫ u in c..x, extendedSlope f a b hab c u) = ∫ u in c..x, deriv f u :=
    intervalIntegral.integral_congr (fun u hu => extendedSlope_eq hab hc (hs hu) hf' hfc)
  have hfd : ContinuousOn (deriv f) (Set.Icc a b) := fun u hu => (hf' u hu).continuousAt.continuousWithinAt
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u hu => (hf u (hs hu)).hasDerivAt)
    ((hfd.mono hs).intervalIntegrable)
  rw [extendedPhase, he, hi]
  ring

/-- Every original curvature bound persists globally under the explicit extension. -/
theorem extendedCurvature_bounds {f : ℝ → ℝ} {a b L U : ℝ} (hab : a ≤ b)
    (hf : ∀ u ∈ Set.Icc a b, L ≤ deriv (deriv f) u ∧ deriv (deriv f) u ≤ U) (x : ℝ) :
    L ≤ extendedCurvature f a b hab x ∧ extendedCurvature f a b hab x ≤ U :=
  hf _ (Set.projIcc a b hab x).property

/-- A bound on the genuine third derivative makes the extended curvature globally Lipschitz. -/
theorem extendedCurvature_lipschitz {f : ℝ → ℝ} {a b D : ℝ} (hab : a ≤ b)
    (hf'' : ∀ u ∈ Set.Icc a b, DifferentiableAt ℝ (deriv (deriv f)) u)
    (hD : ∀ u ∈ Set.Icc a b, |deriv (deriv (deriv f)) u| ≤ D) (x y : ℝ) :
    |extendedCurvature f a b hab x - extendedCurvature f a b hab y| ≤ D * |x - y| := by
  have hDn : 0 ≤ D := (abs_nonneg _).trans (hD a (Set.left_mem_Icc.mpr hab))
  have h := Convex.norm_image_sub_le_of_norm_deriv_le hf'' hD (convex_Icc a b)
    (Set.projIcc a b hab y).property (Set.projIcc a b hab x).property
  apply h.trans
  exact mul_le_mul_of_nonneg_left (Set.abs_projIcc_sub_projIcc hab) hDn

end DhimanKadiriQuesadaHerrera2026
