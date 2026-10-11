import Dubon2026.EmbeddedNormalGaloisRestriction
import Mathlib.FieldTheory.KrullTopology
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # Continuity of the actual embedded normal-field restriction

A finite subextension of the original target has a finite vector-space basis.
Adjoining the images of that basis over the original source base gives a finite
source subextension whose fixing subgroup maps into the target fixing subgroup.
-/

namespace Dubon2026
noncomputable section
open scoped Topology

variable {k E F K : Type*} [Field k] [Field E] [Field F] [Field K]
  [Algebra k E] [Normal k E] [Algebra k F] [Algebra F K] [Algebra k K]
  [IsScalarTower k F K] [Algebra.IsAlgebraic F K]

/-- The original embedded restriction is continuous for the two actual Krull
topologies. A basis of each finite original target extension supplies a genuine
finite original source extension; its fixing subgroup gives the neighborhood
comparison through the proved original field-element action. -/
theorem embeddedNormalGaloisRestriction_continuous (e : E →ₐ[k] K) :
    Continuous (embeddedNormalGaloisRestriction (F := F) e) := by
  classical
  apply continuous_of_continuousAt_one _ (continuousAt_def.mpr _)
  intro N hN
  rw [map_one, krullTopology_mem_nhds_one_iff] at hN
  obtain ⟨L, hL, hN⟩ := hN
  letI : FiniteDimensional k L := hL
  let b := Module.finBasis k L
  let S : Finset K := Finset.univ.image (fun i => e (b i : E))
  let J := IntermediateField.adjoin F (S : Set K)
  letI : FiniteDimensional F J :=
    IntermediateField.finiteDimensional_adjoin
      (fun x _ => Algebra.IsIntegral.isIntegral (R := F) x)
  apply mem_nhds_iff.mpr
  refine ⟨J.fixingSubgroup, ?_, IntermediateField.fixingSubgroup_isOpen J,
    J.fixingSubgroup.one_mem⟩
  intro g hg
  apply hN
  have hgfix := (IntermediateField.mem_fixingSubgroup_iff J g).mp hg
  apply (IntermediateField.mem_fixingSubgroup_iff L _).mpr
  intro x hx
  have hlin :
      (embeddedNormalGaloisRestriction e g).toLinearMap.comp L.val.toLinearMap =
        L.val.toLinearMap := by
    apply b.ext
    intro i
    apply e.injective
    change e (embeddedNormalGaloisRestriction e g (b i : E)) = e (b i : E)
    rw [embeddedNormalGaloisRestriction_commutes]
    apply hgfix
    apply IntermediateField.subset_adjoin
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  exact LinearMap.congr_fun hlin ⟨x, hx⟩

end
end Dubon2026
