import Dubon2026.SourceConstantFieldCoordinateMap
import Mathlib.LinearAlgebra.Dimension.OrzechProperty

/-! DUB-17/18 -> original arithmetic Picard injectivity -> principal-divisor
descent -> finite-basis trace reconstruction. Adapted from
S_AlgebraicCurve_mem_span_range_algebraMap_of_constantFieldExtension,
anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2, coordinate-map and basis sections.
The existing original degree base change supplies independence from spanning;
the external polynomial denominator-clearing independence proof is omitted.
-/
namespace Dubon2026.SourceCurve.ConstantField
noncomputable section
open Polynomial
variable {K F K' F' : Type*} [Field K] [Field F] [Field K'] [Field F'] [Algebra K F]
  [Algebra K' F'] [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F']
  [IsScalarTower K F F']

theorem coordinate_span_of_adjoin_top
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (x : F) [FiniteDimensional (IntermediateField.adjoin K (Set.singleton x)) F]
    {n : ℕ} (y : Module.Basis (Fin n) (IntermediateField.adjoin K (Set.singleton x)) F) :
    ⊤ ≤ Submodule.span (IntermediateField.adjoin K' (Set.singleton (algebraMap F F' x)))
      (Set.range fun i => algebraMap F F' (y i)) := by
  classical
  let kx : IntermediateField K F := IntermediateField.adjoin K {x}
  let kx' : IntermediateField K' F' := IntermediateField.adjoin K' {algebraMap F F' x}
  have hφ : ∀ f : F, algebraMap F F' f ∈
      Submodule.span kx' (Set.range fun i => algebraMap F F' (y i)) := by
    intro f
    rw [← y.sum_repr f, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [algebraMap_smul (K' := K') (F' := F')]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  haveI : Algebra.IsIntegral kx F := Algebra.IsIntegral.of_finite kx F
  have halg : ∀ g ∈ Set.range (algebraMap F F'), IsAlgebraic kx' g := by
    rintro _ ⟨f, rfl⟩
    have hint : IsIntegral kx f := Algebra.IsIntegral.isIntegral f
    have hcomp : (algebraMap kx' F').comp (iota K K' F' x) =
        (algebraMap F F').comp (algebraMap kx F) := by ext a; rfl
    have : IsIntegral kx' (algebraMap F F' f) :=
      hint.map_of_comp_eq (iota K K' F' x) (algebraMap F F') hcomp
    exact this.isAlgebraic
  have hmem : ∀ z : F', z ∈ Submodule.span kx' (Set.range (algebraMap F F')) := by
    intro z
    set E : IntermediateField kx' F' := IntermediateField.adjoin kx' (Set.range (algebraMap F F'))
      with hE
    have hzE : z ∈ E := by
      have hle : IntermediateField.adjoin K' (Set.range (algebraMap F F')) ≤
          IntermediateField.restrictScalars K' E :=
        IntermediateField.adjoin_le_iff.mpr (IntermediateField.subset_adjoin _ _)
      have := hle (hgen ▸ IntermediateField.mem_top (x := z))
      exact (IntermediateField.mem_restrictScalars K').1 this
    have hzA : z ∈ Algebra.adjoin kx' (Set.range (algebraMap F F')) := by
      rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic halg]
      exact hzE
    have : z ∈ Subalgebra.toSubmodule (Algebra.adjoin kx' (Set.range (algebraMap F F'))) := hzA
    rwa [span_range_eq_adjoin] at this
  intro z _
  have := hmem z
  refine (Submodule.span_le.2 ?_) this
  rintro _ ⟨f, rfl⟩
  exact hφ f

theorem exists_coordinate_basis_of_finrank_eq
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (x : F) [FiniteDimensional (IntermediateField.adjoin K (Set.singleton x)) F]
    {n : ℕ} (y : Module.Basis (Fin n) (IntermediateField.adjoin K (Set.singleton x)) F)
    (hdim : n = Module.finrank
      (IntermediateField.adjoin K' (Set.singleton (algebraMap F F' x))) F') :
    ∃ y' : Module.Basis (Fin n)
        (IntermediateField.adjoin K' (Set.singleton (algebraMap F F' x))) F',
      ∀ i, y' i = algebraMap F F' (y i) := by
  have hsp := coordinate_span_of_adjoin_top hgen x y
  have hli := linearIndependent_of_top_le_span_of_card_eq_finrank hsp
    ((Fintype.card_fin n).trans hdim)
  exact ⟨Module.Basis.mk hli hsp, fun i => Module.Basis.mk_apply hli hsp i⟩

end
end Dubon2026.SourceCurve.ConstantField
