import Dubon2026.AdelicL2HolomorphicIdentity

/-! # The original holomorphic infinitesimal identity in the genuine completed adelic space -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

/-- The actual Hilbert-to-L2 realization sends each proved original orbit derivative to its literal quotient L2 derivative. -/
theorem adelicCyclicHilbertGenerator_deriv_toL2 {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (c : ℝ → SL(2, ℝ))
    (h : DifferentiableAt ℝ (fun t : ℝ => adelicCyclicHilbertRepresentation f
      (adelicRealSL2Embedding (c t)) (adelicCyclicHilbertGenerator f)) 0) :
    adelicCyclicHilbertToL2 f (deriv (fun t : ℝ => adelicCyclicHilbertRepresentation f
      (adelicRealSL2Embedding (c t)) (adelicCyclicHilbertGenerator f)) 0) =
    deriv (fun t : ℝ => adelicProjectiveCyclicToL2 N f
      ((adelicLiftCyclicRepresentation N k f).toRepresentation
        (adelicRealSL2Embedding (c t)) (adelicCyclicGenerator N f))) 0 := by
  let L := (adelicCyclicHilbertToL2 f).restrictScalars ℝ
  let C := fun t : ℝ => adelicCyclicHilbertRepresentation f
    (adelicRealSL2Embedding (c t)) (adelicCyclicHilbertGenerator f)
  have hc := @DifferentiableAt.hasDerivAt ℝ inferInstance (AdelicCyclicHilbert f)
    inferInstance inferInstance C 0 h
  have hm : HasDerivAt (L ∘ C) (L (deriv C 0)) 0 :=
    @HasFDerivAt.comp_hasDerivAt ℝ inferInstance (AdelicCyclicHilbert f)
      inferInstance inferInstance _ inferInstance inferInstance C (deriv C 0) 0 L L
      L.hasFDerivAt hc
  have hd := hm.deriv
  simpa only [L, C, Function.comp_def, ContinuousLinearMap.coe_restrictScalars',
    adelicCyclicHilbertGenerator_orbit_toL2] using hd.symm


/-- The actual Hilbert norm derivatives of the original completed cusp generator satisfy its precise holomorphic infinitesimal identity. -/
theorem adelicCyclicHilbertGenerator_holomorphic_identity {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) :
    deriv (fun t : ℝ => adelicCyclicHilbertRepresentation f
      (adelicRealSL2Embedding (realGeodesicCurve t)) (adelicCyclicHilbertGenerator f)) 0 -
    Complex.I • deriv (fun t : ℝ => adelicCyclicHilbertRepresentation f
      (adelicRealSL2Embedding (realUpperUnipotent t)) (adelicCyclicHilbertGenerator f)) 0 =
    ((k : ℂ) / 2) • adelicCyclicHilbertGenerator f := by
  apply adelicCyclicHilbertToL2_injective f
  rw [map_sub, map_smul, map_smul,
    adelicCyclicHilbertGenerator_deriv_toL2 f realGeodesicCurve
      (adelicCyclicHilbertGenerator_geodesic_differentiableAt f),
    adelicCyclicHilbertGenerator_deriv_toL2 f realUpperUnipotent
      (adelicCyclicHilbertGenerator_unipotent_differentiableAt f)]
  change _ = ((k : ℂ) / 2) • adelicCyclicHilbertToL2 f
    (adelicCyclicHilbertEmbedding f (adelicCyclicGenerator N f))
  rw [adelicCyclicHilbertToL2_embedding]
  exact adelicCyclicGenerator_L2_holomorphic_identity N f

end
end Dubon2026
