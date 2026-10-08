import Mathlib.RepresentationTheory.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # Genuine finite-dimensional group orbits in an actual eigenvector span -/

namespace Dubon2026

/-- The literal orbit span of an original representation is invariant under every original group element. -/
theorem representationOrbitSpan_invariant {G K V : Type*} [Monoid G] [Field K]
    [AddCommGroup V] [Module K V] (ρ : Representation K G V) (v : V)
    (g : G) (w : V) (hw : w ∈ Submodule.span K (Set.range (fun h => ρ h v))) :
    ρ g w ∈ Submodule.span K (Set.range (fun h => ρ h v)) := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
      obtain ⟨h, rfl⟩ := hw
      apply Submodule.subset_span
      exact ⟨g * h, by
        change ρ (g * h) v = ρ g (ρ h v)
        rw [map_mul, Module.End.mul_apply]⟩
  | zero => simpa only [map_zero] using (Submodule.span K (Set.range (fun h => ρ h v))).zero_mem
  | add x y _ _ hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  | smul a w _ hw => simpa only [map_smul] using Submodule.smul_mem _ a hw

/-- Every vector in the actual span of group eigenvectors has a genuinely finite-dimensional original group orbit. -/
theorem finiteOrbitSpan_of_eigen_span {G K V ι : Type*} [Monoid G] [Field K]
    [AddCommGroup V] [Module K V] (ρ : Representation K G V) (b : ι → V)
    (he : ∀ g i, ∃ a : K, ρ g (b i) = a • b i)
    (v : V) (hv : v ∈ Submodule.span K (Set.range b)) :
    FiniteDimensional K (Submodule.span K (Set.range (fun g => ρ g v))) := by
  classical
  obtain ⟨s, hs, hv⟩ := Submodule.mem_span_finite_of_mem_span hv
  let p := Submodule.span K (s : Set V)
  letI : FiniteDimensional K p := FiniteDimensional.span_of_finite K s.finite_toSet
  have hi (g : G) (w : V) (hw : w ∈ p) : ρ g w ∈ p := by
    induction hw using Submodule.span_induction with
    | mem w hw =>
        obtain ⟨i, rfl⟩ := hs hw
        obtain ⟨a, ha⟩ := he g i
        rw [ha]
        exact p.smul_mem a (Submodule.subset_span hw)
    | zero => simpa only [map_zero] using p.zero_mem
    | add x y _ _ hx hy => simpa only [map_add] using p.add_mem hx hy
    | smul a w _ hw => simpa only [map_smul] using p.smul_mem a hw
  apply Submodule.finiteDimensional_of_le (S₂ := p)
  apply Submodule.span_le.mpr
  rintro _ ⟨g, rfl⟩
  exact hi g v hv

end Dubon2026
