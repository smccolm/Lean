import Dubon2026.AdelicLocalOpenFixed

/-! # Genuine compact local fixed projectors preserve the original smooth algebraic core -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- The actual orthogonal projector onto the original subgroup-fixed local Hilbert space. -/
def adelicLocalSubgroupProjection (v : HeightOneSpectrum ℤ)
    (J : Subgroup (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))) :
    AdelicCyclicHilbert f →L[ℂ] AdelicCyclicHilbert f :=
  @Submodule.starProjection ℂ (AdelicCyclicHilbert f) inferInstance inferInstance inferInstance
    (adelicLocalSubgroupFixedSpace f v J) inferInstance

/-- Genuine compact local averaging of an original smooth core vector remains in its actual finite orbit span. -/
theorem adelicLocalSubgroupProjection_core_orbit (v : HeightOneSpectrum ℤ)
    (J : Subgroup (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)))
    (hJ : IsCompact (J : Set (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))))
    (x : AdelicCyclicHilbert f) (hx : x ∈ adelicLocalCyclicCore f v) :
    adelicLocalSubgroupProjection f v J x ∈
      Submodule.span ℂ (Set.range (fun g : J => adelicCyclicLocalRepresentation f v g.val x)) := by
  letI : CompactSpace J := isCompact_iff_compactSpace.mp hJ
  have hproj : @Submodule.HasOrthogonalProjection ℂ (AdelicCyclicHilbert f)
      inferInstance inferInstance inferInstance (adelicLocalSubgroupFixedSpace f v J) := inferInstance
  obtain ⟨H, hHo, hHx⟩ := adelicLocalCyclicCore_smooth f v x hx
  let K : Subgroup J := H.comap J.subtype
  have hK : IsOpen (K : Set J) := hHo.preimage continuous_subtype_val
  exact @compactInvariantProjection_mem_orbitSpan J (AdelicCyclicHilbert f)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    ((adelicCyclicLocalRepresentation f v).comp J.subtype)
    (fun g x y => adelicCyclicLocalRepresentation_inner f v g.val x y)
    hproj K hK x (fun g hg => hHx g.val hg)

/-- Every genuine compact local fixed projector preserves the literal original local algebraic orbit core. -/
theorem adelicLocalSubgroupProjection_core (v : HeightOneSpectrum ℤ)
    (J : Subgroup (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)))
    (hJ : IsCompact (J : Set (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))))
    (x : AdelicCyclicHilbert f) (hx : x ∈ adelicLocalCyclicCore f v) :
    adelicLocalSubgroupProjection f v J x ∈ adelicLocalCyclicCore f v := by
  have hs : Submodule.span ℂ (Set.range (fun g : J =>
      adelicCyclicLocalRepresentation f v g.val x)) ≤ adelicLocalCyclicCore f v := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g, rfl⟩
    exact adelicLocalCyclicCore_invariant f v g.val x hx
  exact hs (adelicLocalSubgroupProjection_core_orbit f v J hJ x hx)

end
end Dubon2026
