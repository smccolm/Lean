import Dubon2026.SourceOriginalFinitePeriodGeneration
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-! DUB-17/18 -> original torsion cardinality -> discrete original periods.
Any 2g actual loops generating all regular periods give a real basis of the
period coordinate space. The already proved full real span and native basis
lattice theorem prove discreteness directly. Constructing the generating
loops remains required; no intersection-matrix normal form is assumed.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Set KaehlerDifferential
variable (N : ℕ) [NeZero N]
attribute [local instance] placeTopology
local notation "F" => modularFunctionFieldOver N ℂ

theorem original_period_basis_of_generating_loops {n : ℕ}
    (b : Module.Basis (Fin n) ℂ (regularDifferentials ℂ F))
    (Pz : Fin n ⊕ Fin n → Place ℂ F) (Z : ∀ k, Path (Pz k) (Pz k))
    (hgen : ∀ (P : Place ℂ F) (γ : Path P P), ∃ κ : Fin n ⊕ Fin n → ℤ,
      ∀ i, pathIntegral N (b i : Ω[F⁄ℂ]) γ =
        ∑ k, (κ k : ℂ) * pathIntegral N (b i : Ω[F⁄ℂ]) (Z k)) :
    ∃ B : Module.Basis (Fin n ⊕ Fin n) ℝ (Fin n → ℂ),
      (∀ k i, B k i = pathIntegral N (b i : Ω[F⁄ℂ]) (Z k)) ∧
      pathPeriodLattice N (fun i => (b i : Ω[F⁄ℂ])) = Submodule.span ℤ (Set.range B) := by
  let v : (Fin n ⊕ Fin n) → Fin n → ℂ := fun k i =>
    pathIntegral N (b i : Ω[F⁄ℂ]) (Z k)
  have hL := original_period_lattice_eq_span_loops N (fun i => (b i : Ω[F⁄ℂ])) Pz Z hgen
  have hs : Submodule.span ℝ (Set.range v) = ⊤ := by
    rw [← Submodule.span_span_of_tower ℤ ℝ, ← hL]
    exact span_real_pathPeriodLattice_eq_top N b
  have hli : LinearIndependent ℝ v :=
    linearIndependent_of_top_le_span_of_card_le_finrank (by rw [hs]) (by
      simp [finrank_real_of_complex, two_mul])
  let B : Module.Basis (Fin n ⊕ Fin n) ℝ (Fin n → ℂ) := Module.Basis.mk hli (by rw [hs])
  refine ⟨B, ?_, ?_⟩
  · intro k i
    simp only [B, Module.Basis.coe_mk, v]
  · simpa only [B, Module.Basis.coe_mk] using hL

theorem original_discrete_periods_of_generating_loops {n : ℕ}
    (b : Module.Basis (Fin n) ℂ (regularDifferentials ℂ F))
    (Pz : Fin n ⊕ Fin n → Place ℂ F) (Z : ∀ k, Path (Pz k) (Pz k))
    (hgen : ∀ (P : Place ℂ F) (γ : Path P P), ∃ κ : Fin n ⊕ Fin n → ℤ,
      ∀ i, pathIntegral N (b i : Ω[F⁄ℂ]) γ =
        ∑ k, (κ k : ℂ) * pathIntegral N (b i : Ω[F⁄ℂ]) (Z k)) :
    DiscreteTopology (pathPeriodLattice N (fun i => (b i : Ω[F⁄ℂ]))) := by
  obtain ⟨B, _, hB⟩ := original_period_basis_of_generating_loops N b Pz Z hgen
  rw [hB]
  infer_instance

end
end Dubon2026.SourceFunctionField.OriginalChart
