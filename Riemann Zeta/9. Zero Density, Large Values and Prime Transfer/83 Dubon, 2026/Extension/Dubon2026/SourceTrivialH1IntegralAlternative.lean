import Dubon2026.SourceGamma0IntegralSpan

/-! DUB-17/18 -> residual Galois association -> the original weight-two
class either lifts from the integral span or detects a finite-order element.
This consumer uses native H1 returned by the all-prime weight-two theorem,
via Mathlib's proved identification with actual subgroup homomorphisms.
The remaining two branches require characteristic-zero Hecke lifting and
the finite-order Hecke calculation, respectively.
-/

namespace Dubon2026
noncomputable section
open CongruenceSubgroup groupCohomology CategoryTheory

/-- A native original weight-two class vanishing on finite-order elements
belongs to the span of actual reductions of integral homomorphism classes. -/
theorem sourceTrivialH1_mem_integralSpan
    (M : ℕ) [NeZero M] (κ : Type) [CommRing κ]
    (x : H1 (Rep.trivial κ (Gamma0 M) κ))
    (hx : ∀ g : Gamma0 M, IsOfFinOrder g →
      (H1IsoOfIsTrivial (Rep.trivial κ (Gamma0 M) κ)).hom x (Additive.ofMul g) = 0) :
    x ∈ Submodule.span κ (Set.range fun y : Additive (Gamma0 M) →+ ℤ =>
      (H1IsoOfIsTrivial (Rep.trivial κ (Gamma0 M) κ)).inv ((Int.castAddHom κ).comp y)) := by
  let e := H1IsoOfIsTrivial (Rep.trivial κ (Gamma0 M) κ)
  have h := sourceGamma0Hom_mem_integralSpan M κ (e.hom x) hx
  have hm : ∀ y ∈ Submodule.span κ
      (Set.range fun z : Additive (Gamma0 M) →+ ℤ => (Int.castAddHom κ).comp z),
      e.inv y ∈ Submodule.span κ (Set.range fun z : Additive (Gamma0 M) →+ ℤ =>
        e.inv ((Int.castAddHom κ).comp z)) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨z, rfl⟩ := hy
      exact Submodule.subset_span ⟨z, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
    | smul a y _ hy => rw [map_smul]; exact Submodule.smul_mem _ a hy
  simpa using hm (e.hom x) h

/-- The actual native weight-two class has the integral-span or detected
finite-order alternative needed by the two Galois-association branches. -/
theorem sourceTrivialH1_integral_or_torsion
    (M : ℕ) [NeZero M] (κ : Type) [CommRing κ]
    (x : H1 (Rep.trivial κ (Gamma0 M) κ)) :
    x ∈ Submodule.span κ (Set.range fun y : Additive (Gamma0 M) →+ ℤ =>
      (H1IsoOfIsTrivial (Rep.trivial κ (Gamma0 M) κ)).inv ((Int.castAddHom κ).comp y)) ∨
    ∃ g : Gamma0 M, IsOfFinOrder g ∧
      (H1IsoOfIsTrivial (Rep.trivial κ (Gamma0 M) κ)).hom x (Additive.ofMul g) ≠ 0 := by
  by_cases h : ∀ g : Gamma0 M, IsOfFinOrder g →
      (H1IsoOfIsTrivial (Rep.trivial κ (Gamma0 M) κ)).hom x (Additive.ofMul g) = 0
  · exact Or.inl (sourceTrivialH1_mem_integralSpan M κ x h)
  · push Not at h
    exact Or.inr h

end
end Dubon2026
