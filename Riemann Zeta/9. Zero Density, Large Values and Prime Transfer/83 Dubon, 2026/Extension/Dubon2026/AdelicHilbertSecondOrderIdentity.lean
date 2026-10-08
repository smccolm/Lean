import Dubon2026.AdelicL2SecondOrderIdentity
import Dubon2026.LinearMapSmoothJets
import Dubon2026.AdelicHilbertGeodesicSmoothness

/-! # The original second-order identity between genuine Hilbert orbit jets -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ContDiff

/-- The faithful original realization retains every genuine Hilbert derivative of each smooth original orbit. -/
theorem adelicCyclicHilbertGenerator_iteratedDeriv_toL2 {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (c : ℝ → SL(2, ℝ))
    (h : ContDiff ℝ ∞ (fun t : ℝ => adelicCyclicHilbertRepresentation f
      (adelicRealSL2Embedding (c t)) (adelicCyclicHilbertGenerator f))) (n : ℕ) (t : ℝ) :
    adelicCyclicHilbertToL2 f (iteratedDeriv n (fun u : ℝ => adelicCyclicHilbertRepresentation f
      (adelicRealSL2Embedding (c u)) (adelicCyclicHilbertGenerator f)) t) =
    iteratedDeriv n (fun u : ℝ => adelicProjectiveCyclicToL2 N f
      ((adelicLiftCyclicRepresentation N k f).toRepresentation
        (adelicRealSL2Embedding (c u)) (adelicCyclicGenerator N f))) t := by
  have he := @iteratedDeriv_continuousLinearMap (AdelicCyclicHilbert f)
    (Lp ℂ 2 (adelicProjectiveMeasure.restrict (adelicProjectiveGamma0Domain N)))
    inferInstance inferInstance inferInstance inferInstance
    ((adelicCyclicHilbertToL2 f).restrictScalars ℝ) _ h n
  have ht := congrFun he t
  simpa only [ContinuousLinearMap.coe_restrictScalars',
    adelicCyclicHilbertGenerator_orbit_toL2] using ht.symm

/-- Every actual unipotent Hilbert jet is faithfully realized as its original quotient L2 jet. -/
theorem adelicCyclicHilbertGenerator_unipotent_jet_toL2 {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (n : ℕ) (t : ℝ) :
    adelicCyclicHilbertToL2 f (iteratedDeriv n (fun u : ℝ => adelicCyclicHilbertRepresentation f
      (adelicRealSL2Embedding (realUpperUnipotent u)) (adelicCyclicHilbertGenerator f)) t) =
    iteratedDeriv n (fun u : ℝ => adelicProjectiveCyclicToL2 N f
      ((adelicLiftCyclicRepresentation N k f).toRepresentation
        (adelicRealSL2Embedding (realUpperUnipotent u)) (adelicCyclicGenerator N f))) t :=
  adelicCyclicHilbertGenerator_iteratedDeriv_toL2 f realUpperUnipotent
    (adelicCyclicHilbertGenerator_unipotent_contDiff f) n t

/-- Every actual geodesic Hilbert jet is faithfully realized as its original quotient L2 jet. -/
theorem adelicCyclicHilbertGenerator_geodesic_jet_toL2 {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (n : ℕ) (t : ℝ) :
    adelicCyclicHilbertToL2 f (iteratedDeriv n (fun u : ℝ => adelicCyclicHilbertRepresentation f
      (adelicRealSL2Embedding (realGeodesicCurve u)) (adelicCyclicHilbertGenerator f)) t) =
    iteratedDeriv n (fun u : ℝ => adelicProjectiveCyclicToL2 N f
      ((adelicLiftCyclicRepresentation N k f).toRepresentation
        (adelicRealSL2Embedding (realGeodesicCurve u)) (adelicCyclicGenerator N f))) t :=
  adelicCyclicHilbertGenerator_iteratedDeriv_toL2 f realGeodesicCurve
    (adelicCyclicHilbertGenerator_geodesic_contDiff f) n t

private theorem linearMap_second_order_relation {V W : Type*}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (L : V →ₗ[ℂ] W) (hi : Function.Injective L) (A₂ A₁ U₂ U₁ v : V) (b a : ℂ)
    (h : L A₂ - L A₁ + L U₂ - b • L U₁ = a • L v) :
    A₂ - A₁ + U₂ - b • U₁ = a • v := by
  apply hi
  simpa only [map_sub, map_add, map_smul] using h

/-- The actual completed generator satisfies the original second-order holomorphic relation in its genuine Hilbert norm. -/
theorem adelicCyclicHilbertGenerator_second_order_identity {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    iteratedDeriv 2 (fun t : ℝ => adelicCyclicHilbertRepresentation f
      (adelicRealSL2Embedding (realGeodesicCurve t)) (adelicCyclicHilbertGenerator f)) 0 -
    iteratedDeriv 1 (fun t : ℝ => adelicCyclicHilbertRepresentation f
      (adelicRealSL2Embedding (realGeodesicCurve t)) (adelicCyclicHilbertGenerator f)) 0 +
    iteratedDeriv 2 (fun t : ℝ => adelicCyclicHilbertRepresentation f
      (adelicRealSL2Embedding (realUpperUnipotent t)) (adelicCyclicHilbertGenerator f)) 0 -
    ((k : ℂ) * Complex.I) • iteratedDeriv 1 (fun t : ℝ => adelicCyclicHilbertRepresentation f
      (adelicRealSL2Embedding (realUpperUnipotent t)) (adelicCyclicHilbertGenerator f)) 0 =
      (((k : ℂ) / 2) * ((k : ℂ) / 2 - 1)) • adelicCyclicHilbertGenerator f := by
  apply linearMap_second_order_relation (adelicCyclicHilbertToL2 f).toLinearMap
    (adelicCyclicHilbertToL2_injective f)
  change adelicCyclicHilbertToL2 f _ - adelicCyclicHilbertToL2 f _ +
    adelicCyclicHilbertToL2 f _ - ((k : ℂ) * Complex.I) • adelicCyclicHilbertToL2 f _ =
      (((k : ℂ) / 2) * ((k : ℂ) / 2 - 1)) • adelicCyclicHilbertToL2 f (adelicCyclicHilbertGenerator f)
  simp only [adelicCyclicHilbertGenerator_geodesic_jet_toL2,
    adelicCyclicHilbertGenerator_unipotent_jet_toL2]
  change _ = (((k : ℂ) / 2) * ((k : ℂ) / 2 - 1)) • adelicCyclicHilbertToL2 f
    (adelicCyclicHilbertEmbedding f (adelicCyclicGenerator N f))
  rw [adelicCyclicHilbertToL2_embedding]
  exact adelicCyclicGenerator_L2_second_order_identity N f

end
end Dubon2026
