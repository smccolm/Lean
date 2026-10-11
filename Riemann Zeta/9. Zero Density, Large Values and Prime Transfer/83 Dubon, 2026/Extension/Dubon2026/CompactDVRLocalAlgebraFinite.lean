import Dubon2026.CompactSeparatedLocalAdicTopology
import Dubon2026.CompactFiniteResidueModule
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-! # Faithful local algebras between actual compact discrete valuation rings are finite -/

namespace Dubon2026
noncomputable section

open IsLocalRing

variable {R S : Type} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
  [IsDiscreteValuationRing R] [IsDiscreteValuationRing S]
  [Algebra R S] [FaithfulSMul R S] [IsLocalHom (algebraMap R S)]
  [TopologicalSpace R] [TopologicalSpace S] [IsTopologicalRing R] [IsTopologicalRing S]
  [CompactSpace R] [CompactSpace S] [T2Space R] [T2Space S]
  [IsHausdorff (maximalIdeal R) R] [IsHausdorff (maximalIdeal S) S]

/-- The original local algebra map between compact separated discrete
valuation rings makes the extension a finite module. Finiteness follows from
actual residue representatives and compact coefficient spans, not an assumed
integral-closure or finite-module structure. -/
theorem compactDVRLocalAlgebra_module_finite : Module.Finite R S := by
  have hf : Continuous (algebraMap R S) :=
    compactSeparatedLocalRingHom_continuous (algebraMap R S)
  haveI : ContinuousSMul R S := {
    continuous_smul := by
      simpa only [Algebra.smul_def] using (hf.comp continuous_fst).mul continuous_snd }
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hπ0 : algebraMap R S π ≠ 0 := by
    intro h
    apply hπ.ne_zero
    exact (FaithfulSMul.algebraMap_injective R S) (h.trans (map_zero _).symm)
  have hJ : (Ideal.span {algebraMap R S π} : Ideal S) ≠ ⊥ := by
    intro h
    exact hπ0 (Ideal.span_singleton_eq_bot.mp h)
  haveI : Finite (S ⧸ Ideal.span {algebraMap R S π}) :=
    IsLocalRing.isOpen_iff_finite_quotient.mp (IsDedekindDomain.isOpen_of_ne_bot hJ)
  have hπm : algebraMap R S π ∈ maximalIdeal S :=
    map_nonunit (algebraMap R S) π (by simpa using hπ.not_isUnit)
  exact compactFiniteResidue_module_finite (maximalIdeal S) π hπm

end
end Dubon2026
