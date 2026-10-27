import Dubon2026.SourceFrickeCyclotomicHolomorphicAlgebra
import Mathlib.LinearAlgebra.Basis.Submodule

/-! DUB-17/18 -> actual Gamma1 cusp realization -> rational cusp-form spanning
-> coefficient twists. Extend a basis of the original cyclotomic holomorphic
Fricke algebra to a complex basis of its actual function span, using the
proved scalar-extension independence and native span-of-span theorem. -/
namespace Dubon2026.SourceFricke
noncomputable section
open Module
open UpperHalfPlane SourceFunctionField

theorem exists_complex_basis_of_cyclotomic_fricke_basis
    {N : ℕ} [NeZero N] {ι : Type}
    (b : Basis ι (kN N) (cyclotomicHolomorphicFrickeAlgebra N).toSubmodule) :
    ∃ B : Basis ι ℂ (Submodule.span ℂ (holomorphicCyclotomicFrickeFractions N)),
      ∀ i, (B i : ℍ → ℂ) = (b i : ℍ → ℂ) := by
  let A := cyclotomicHolomorphicFrickeAlgebra N
  let v : ι → ℍ → ℂ := fun i => b i
  have hK : LinearIndependent (kN N) v :=
    b.linearIndependent.map' A.toSubmodule.subtype (Submodule.ker_subtype _)
  have hC : LinearIndependent ℂ v :=
    linearIndependent_holomorphic_cyclotomic_fricke_fractions (fun i => (b i).property) hK
  have hKs : Submodule.span (kN N) (Set.range v) = A.toSubmodule := by
    change Submodule.span (kN N) (Set.range (A.toSubmodule.subtype ∘ b)) = A.toSubmodule
    rw [Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hCs : Submodule.span ℂ (Set.range v) =
      Submodule.span ℂ (holomorphicCyclotomicFrickeFractions N) := by
    rw [← Submodule.span_span_of_tower (kN N) ℂ (Set.range v), hKs]
    rfl
  refine ⟨(Basis.span hC).map (LinearEquiv.ofEq _ _ hCs), fun i => ?_⟩
  simp only [Basis.map_apply, LinearEquiv.coe_ofEq_apply, Basis.coe_span_apply]
  rfl

/-- A complex basis induced from a basis of the original cyclotomic Fricke algebra. -/
def cyclotomicFrickeComplexBasis (N : ℕ) [NeZero N] :
    Basis (Module.Free.ChooseBasisIndex (kN N) (cyclotomicHolomorphicFrickeAlgebra N).toSubmodule) ℂ
      (Submodule.span ℂ (holomorphicCyclotomicFrickeFractions N)) :=
  (exists_complex_basis_of_cyclotomic_fricke_basis
    (Module.Free.chooseBasis (kN N) (cyclotomicHolomorphicFrickeAlgebra N).toSubmodule)).choose

theorem cyclotomicFrickeComplexBasis_apply (N : ℕ) [NeZero N]
    (i : Module.Free.ChooseBasisIndex (kN N) (cyclotomicHolomorphicFrickeAlgebra N).toSubmodule) :
    (cyclotomicFrickeComplexBasis N i : ℍ → ℂ) =
      (Module.Free.chooseBasis (kN N) (cyclotomicHolomorphicFrickeAlgebra N).toSubmodule i : ℍ → ℂ) :=
  (exists_complex_basis_of_cyclotomic_fricke_basis
    (Module.Free.chooseBasis (kN N) (cyclotomicHolomorphicFrickeAlgebra N).toSubmodule)).choose_spec i

end
end Dubon2026.SourceFricke