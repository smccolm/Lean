import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Tactic

/-! DUB-17/18 -> Picard torsion injectivity -> Kummer power lifting ->
genus inequality -> constants in the common residue chart. A finite module
over the coefficient valuation ring has one nonzero scalar killing all its
torsion. This will be applied to the overlap modulo the two integral charts.
Native flatness, local freeness and projective splitting discharge the
finite-torsion assertion. Adapted from Apache-2.0 FLT commit
6e837e75355538c7f80bab5b956861e86c4eacc2. -/
namespace Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
noncomputable section
open Submodule

theorem exists_uniform_torsion_annihilator
    {R : Type*} [CommRing R] [IsDomain R] [ValuationRing R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M] :
    ∃ a : R, a ≠ 0 ∧ ∀ m : M, (∃ c : R, c ≠ 0 ∧ c • m = 0) → a • m = 0 := by
  classical

  set T : Submodule R M := torsion R M with hT
  haveI : Module.Finite R (M ⧸ T) := inferInstance
  haveI : Module.Flat R (M ⧸ T) :=
    (Module.Flat.flat_iff_torsion_eq_bot_of_isBezout).mpr (Submodule.QuotientTorsion.torsion_eq_bot)
  haveI : Module.Free R (M ⧸ T) := Module.free_of_flat_of_isLocalRing
  haveI : Module.Projective R (M ⧸ T) := Module.Projective.of_free

  obtain ⟨s, hs⟩ := Module.projective_lifting_property T.mkQ (LinearMap.id : M ⧸ T →ₗ[R] M ⧸ T)
    (Submodule.mkQ_surjective T)

  set φ : M →ₗ[R] M := LinearMap.id - s ∘ₗ T.mkQ with hφ
  have hrange : LinearMap.range φ = T := by
    apply le_antisymm
    · rintro _ ⟨m, rfl⟩
      have : T.mkQ (φ m) = 0 := by
        have h1 : T.mkQ (s (T.mkQ m)) = T.mkQ m := by
          have := LinearMap.congr_fun hs (T.mkQ m)
          simpa using this
        simp only [Submodule.mkQ_apply] at h1
        simp only [hφ, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
          Submodule.mkQ_apply, Submodule.Quotient.mk_sub, h1, sub_self]
      simpa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using this
    · intro t ht
      refine ⟨t, ?_⟩
      have : T.mkQ t = 0 := by simpa [Submodule.Quotient.mk_eq_zero] using ht
      simp [hφ, this]
  haveI hTfin : Module.Finite R T := by
    rw [← hrange]
    exact Module.Finite.range φ

  have hTtors : Module.IsTorsion R T := by
    intro t
    obtain ⟨c, hc⟩ := (mem_torsion_iff (t : M)).mp t.2
    exact ⟨c, Subtype.ext (by simpa using hc)⟩
  obtain ⟨a, ha, ha0⟩ := Submodule.annihilator_top_inter_nonZeroDivisors hTtors
  refine ⟨a, nonZeroDivisors.ne_zero ha0, fun m hm => ?_⟩
  obtain ⟨c, hc0, hcm⟩ := hm
  have hmT : m ∈ T := (mem_torsion_iff m).mpr ⟨⟨c, mem_nonZeroDivisors_of_ne_zero hc0⟩, hcm⟩
  have := Submodule.mem_annihilator.mp ha ⟨m, hmT⟩ Submodule.mem_top
  simpa using congrArg Subtype.val this


end
end Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
