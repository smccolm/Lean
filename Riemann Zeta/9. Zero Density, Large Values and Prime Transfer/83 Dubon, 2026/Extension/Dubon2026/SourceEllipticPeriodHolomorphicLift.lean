import Dubon2026.SourceEllipticPeriodCovering
import Dubon2026.SourceEllipticPeriodUniformization
import Mathlib.Analysis.Convex.Contractible

/-! Local holomorphic lifts of an actual homomorphism between period curves
assemble to a global holomorphic lift normalized at zero. The local lifts
remain explicit inputs here; SourceEllipticPeriodQuotientGerm supplies
them for the actual odd norm. Native covering-space lifting replaces general algebraic-place
machinery in this DUB-17/18 quotient-product dependency.
Adapted from the frozen Apache-2.0 FLT differentiable point-map lift proof. -/

namespace Dubon2026.SourceEllipticPeriod
open Complex Filter Set
open scoped Topology

theorem exists_holomorphic_lift (L M : PeriodPair)
    [(periodCurve L).IsElliptic] [(periodCurve M).IsElliptic]
    (ψ : (periodCurve L).toAffine.Point →+ (periodCurve M).toAffine.Point)
    (hloc : ∀ z₀ : ℂ, ∃ U ∈ 𝓝 z₀, ∃ G : ℂ → ℂ, DifferentiableOn ℂ G U ∧
      ∀ z ∈ U, periodHom M (G z) = ψ (periodHom L z)) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ F 0 = 0 ∧
      ∀ z, periodHom M (F z) = ψ (periodHom L z) := by
  let g : ℂ → ℂ ⧸ M.lattice.toAddSubgroup :=
    fun z => (periodQuotientEquiv M).symm (ψ (periodHom L z))
  have hgloc : ∀ z₀ : ℂ, ∃ U ∈ 𝓝 z₀, ∃ G : ℂ → ℂ, DifferentiableOn ℂ G U ∧
      ∀ z ∈ U, g z = QuotientAddGroup.mk (G z) := by
    intro z₀
    obtain ⟨U, hU, G, hGd, hGint⟩ := hloc z₀
    refine ⟨U, hU, G, hGd, fun z hz => ?_⟩
    change (periodQuotientEquiv M).symm (ψ (periodHom L z)) = _
    rw [← hGint z hz]
    exact (periodQuotientEquiv M).symm_apply_apply (QuotientAddGroup.mk (G z))
  have hmkc : Continuous (QuotientAddGroup.mk (s := M.lattice.toAddSubgroup)) :=
    (isCoveringMap_mk_lattice M).continuous
  have hgc : Continuous g := continuous_iff_continuousAt.mpr fun z₀ => by
    obtain ⟨U, hU, G, hGd, heq⟩ := hgloc z₀
    exact ((hmkc.comp_continuousOn hGd.continuousOn).congr
      (fun z hz => heq z hz)).continuousAt hU
  have hg0 : (QuotientAddGroup.mk (0 : ℂ) : ℂ ⧸ M.lattice.toAddSubgroup) =
      (⟨g, hgc⟩ : C(ℂ, ℂ ⧸ M.lattice.toAddSubgroup)) 0 := by
    simp only [ContinuousMap.coe_mk, g, map_zero, QuotientAddGroup.mk_zero]
  obtain ⟨F, ⟨hF0, hFlift⟩, -⟩ :=
    (isCoveringMap_mk_lattice M).existsUnique_continuousMap_lifts ⟨g, hgc⟩ 0 0 hg0
  have hFliftz : ∀ z, (QuotientAddGroup.mk (F z) : ℂ ⧸ M.lattice.toAddSubgroup) = g z :=
    fun z => congrFun hFlift z
  refine ⟨F, ?_, hF0, ?_⟩
  · apply differentiable_of_local_lifts M F.continuous
    intro z₀
    obtain ⟨U, hU, G, hGd, heq⟩ := hgloc z₀
    exact ⟨U, hU, G, hGd, fun z hz => (hFliftz z).trans (heq z hz)⟩
  · intro z
    change periodQuotientEquiv M (QuotientAddGroup.mk (F z)) = _
    rw [hFliftz z]
    exact (periodQuotientEquiv M).apply_symm_apply _

end Dubon2026.SourceEllipticPeriod
