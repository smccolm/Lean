import Dubon2026.ContinuousFiniteCoefficientSplitting
import Dubon2026.ContinuousTwoCocyclePeriodInvariants
import Mathlib.FieldTheory.Galois.Profinite

/-! # One actual finite Galois field for original finite coefficients and cocycles

This is the finite descent needed to relate the original arithmetic H2 classes
to the proved unramified-stage vanishing, before finite local support and
DUB-17 global reciprocity. It retains the full original coefficient action.
-/

namespace Dubon2026
noncomputable section

variable {R K Ω : Type} [CommRing R] [TopologicalSpace R]
  [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (A : Rep.{0} R Gal(Ω/K)) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  [ContinuousSMul R A] (hA : Continuous (fun z : Gal(Ω/K) × A => A.ρ z.1 z.2))

include hA in
/-- A single original finite Galois stage contains the kernel data for both
the actual coefficient action and both variables of the original cocycle. -/
theorem continuousFiniteCoefficientTwoCocycle_exists_finiteField
    (c : continuousRepresentationCocyclesTwo A) :
    ∃ F : FiniteGaloisIntermediateField K Ω,
      (∀ u : Gal(Ω/K), AlgEquiv.restrictNormalHom F u = 1 → ∀ a : A, A.ρ u a = a) ∧
      (∀ g h u v : Gal(Ω/K), AlgEquiv.restrictNormalHom F u = 1 →
        AlgEquiv.restrictNormalHom F v = 1 → c.val (g * u, h * v) = c.val (g, h)) := by
  obtain ⟨V, hperiod, _hfixed⟩ := continuousTwoCocycle_exists_openNormal_periods_and_fixed A c
  let W : OpenNormalSubgroup Gal(Ω/K) :=
    { toSubgroup := A.ρ.asGroupHom.ker
      isOpen' := continuousFiniteCoefficient_kernel_isOpen A hA
      isNormal' := inferInstance }
  let U := V ⊓ W
  let H : ClosedSubgroup Gal(Ω/K) := ⟨U.toSubgroup, U.isClosed⟩
  let L := IntermediateField.fixedField U.toSubgroup
  have hfix : L.fixingSubgroup = U.toSubgroup :=
    InfiniteGalois.fixingSubgroup_fixedField H
  letI : FiniteDimensional K L := by
    apply (InfiniteGalois.isOpen_iff_finite L).mp
    simpa only [hfix] using U.isOpen
  letI : IsGalois K L := by
    apply (InfiniteGalois.normal_iff_isGalois L).mp
    rw [hfix]
    infer_instance
  let F : FiniteGaloisIntermediateField K Ω := {
    toIntermediateField := L
    finiteDimensional := inferInstance
    isGalois := inferInstance }
  have hmem (u : Gal(Ω/K)) (hu : AlgEquiv.restrictNormalHom F u = 1) : u ∈ U := by
    have h := (FiniteGaloisIntermediateField.mem_fixingSubgroup_iff u F).mpr hu
    change u ∈ L.fixingSubgroup at h
    rwa [hfix] at h
  refine ⟨F, ?_, ?_⟩
  · intro u hu a
    have he : A.ρ.asGroupHom u = 1 := (hmem u hu).2
    exact congrArg (fun v : Units (A →ₗ[R] A) => v.val a) he
  · intro g h u v hu hv
    exact hperiod g h u v (hmem u hu).1 (hmem v hv).1

end
end Dubon2026
