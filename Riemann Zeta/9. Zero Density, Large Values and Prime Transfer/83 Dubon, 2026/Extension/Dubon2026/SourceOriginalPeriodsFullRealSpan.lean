import Dubon2026.SourceOriginalPeriodAnnihilator
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! DUB-17/18 -> original torsion cardinality -> complex Abel-Jacobi.
The integer span of actual loop periods of an original regular-differential
basis spans the full real coordinate space. A hypothetical proper span
has a nonzero annihilator by native finite-dimensional duality; the proved
compact maximum-principle consumer forces it to vanish. No compactness,
primitive, chart compatibility or period-span hypothesis is supplied.
Discreteness and the principal-divisor/Jacobi-inversion comparison remain
required before this yields the exact original torsion cardinality.
Adapted from S_AlgebraicCurve_span_real_pathPeriodLattice_eq_top,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Set KaehlerDifferential
variable (N : ℕ) [NeZero N]

theorem span_real_pathPeriodLattice_eq_top_of_linearIndependent {n : ℕ}
    (b : Fin n → Ω[modularFunctionFieldOver N ℂ⁄ℂ])
    (hb : ∀ i, b i ∈ regularDifferentials ℂ (modularFunctionFieldOver N ℂ))
    (hli : LinearIndependent ℂ b) :
    Submodule.span ℝ (pathPeriodLattice N b : Set (Fin n → ℂ)) = ⊤ := by
  by_contra htop
  obtain ⟨ℓ, hℓ0, hℓbot⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top
    (lt_top_iff_ne_top.mpr htop) inferInstance
  apply hℓ0
  apply eq_zero_of_annihilates_periods N b hb hli ℓ
  intro u hu
  have hm := Submodule.mem_map_of_mem (f := ℓ)
    (Submodule.subset_span (R := ℝ) hu)
  rw [hℓbot, Submodule.mem_bot] at hm
  exact hm

theorem span_real_pathPeriodLattice_eq_top {n : ℕ}
    (b : Module.Basis (Fin n) ℂ (regularDifferentials ℂ (modularFunctionFieldOver N ℂ))) :
    Submodule.span ℝ (pathPeriodLattice N (fun i => (b i : Ω[modularFunctionFieldOver N ℂ⁄ℂ])) :
      Set (Fin n → ℂ)) = ⊤ := by
  apply span_real_pathPeriodLattice_eq_top_of_linearIndependent N _ (fun i => (b i).2)
  exact b.linearIndependent.map' (regularDifferentials ℂ (modularFunctionFieldOver N ℂ)).subtype
    (Submodule.ker_subtype _)

end
end Dubon2026.SourceFunctionField.OriginalChart
