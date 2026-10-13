import Dubon2026.FiniteCoefficientGaloisDescent

/-! # Exact finite descent of original nontrivial coefficient two-cocycles

The actual coefficient action and original cocycle descend to the same original
finite Galois field. This is the arithmetic finite-stage input needed before
unramified local H2 vanishing can establish support for DUB-17 reciprocity.
-/

namespace Dubon2026
noncomputable section

variable {R K Ω : Type} [CommRing R] [TopologicalSpace R]
  [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (A : Rep.{0} R Gal(Ω/K)) [TopologicalSpace A] [DiscreteTopology A] [ContinuousSMul R A]
  (F : FiniteGaloisIntermediateField K Ω)
  (hker : ∀ u : Gal(Ω/K), AlgEquiv.restrictNormalHom F u = 1 → ∀ a : A, A.ρ u a = a)
  (c : continuousRepresentationCocyclesTwo A)
  (hperiod : ∀ g h u v : Gal(Ω/K), AlgEquiv.restrictNormalHom F u = 1 →
    AlgEquiv.restrictNormalHom F v = 1 → c.val (g * u, h * v) = c.val (g, h))

include hperiod in
/-- Original restriction descends the entire original two-cocycle, with the
proved descended nontrivial coefficient action and exact representative values. -/
theorem finiteCoefficientTwoCocycle_exists_finite_descent :
    ∃ d : continuousRepresentationCocyclesTwo (Rep.of (finiteStageCoefficientRepresentation A F hker)),
      ∀ g h : Gal(Ω/K), d.val (AlgEquiv.restrictNormalHom F g, AlgEquiv.restrictNormalHom F h) =
        c.val (g, h) := by
  let j : Gal(Ω/K) →* Gal(F/K) := AlgEquiv.restrictNormalHom F
  have hj : Function.Surjective j := AlgEquiv.restrictNormalHom_surjective Ω
  let f : Gal(F/K) × Gal(F/K) → A :=
    fun z => c.val (Function.surjInv hj z.1, Function.surjInv hj z.2)
  have hf : ∀ g h : Gal(Ω/K), f (j g, j h) = c.val (g, h) := by
    intro g h
    let g' := Function.surjInv hj (j g)
    let h' := Function.surjInv hj (j h)
    have hg : j g' = j g := Function.surjInv_eq hj (j g)
    have hh : j h' = j h := Function.surjInv_eq hj (j h)
    have hgu : j (g'⁻¹ * g) = 1 := by rw [map_mul, map_inv, hg, inv_mul_cancel]
    have hhv : j (h'⁻¹ * h) = 1 := by rw [map_mul, map_inv, hh, inv_mul_cancel]
    have he := hperiod g' h' (g'⁻¹ * g) (h'⁻¹ * h) hgu hhv
    exact (show c.val (g, h) = f (j g, j h) by
      simpa only [mul_inv_cancel_left] using he).symm
  have hc : f ∈ groupCohomology.cocycles₂ (Rep.of (finiteStageCoefficientRepresentation A F hker)) := by
    apply (groupCohomology.mem_cocycles₂_iff _).mpr
    intro x y z
    obtain ⟨g, rfl⟩ := hj x
    obtain ⟨h, rfl⟩ := hj y
    obtain ⟨u, rfl⟩ := hj z
    change f (j g * j h, j u) + f (j g, j h) =
      finiteStageCoefficientRepresentation A F hker (j g) (f (j h, j u)) + f (j g, j h * j u)
    rw [← map_mul j, ← map_mul j, hf, hf, hf, hf,
      finiteStageCoefficientRepresentation_apply]
    exact (groupCohomology.mem_cocycles₂_iff _).mp c.val.property g h u
  exact ⟨⟨⟨f, hc⟩, continuous_of_discreteTopology⟩, hf⟩

/-- Every actual continuous finite-coefficient two-cocycle descends together
with its full action to a constructed finite Galois stage. Both action and
cocycle comparisons are proved on every original automorphism. -/
theorem continuousFiniteCoefficientTwoCocycle_exists_finite_descent [Finite A]
    (hA : Continuous (fun z : Gal(Ω/K) × A => A.ρ z.1 z.2)) :
    ∃ E : FiniteGaloisIntermediateField K Ω,
      ∃ ρ : Representation R Gal(E/K) A,
        ∃ d : continuousRepresentationCocyclesTwo (Rep.of ρ),
          (∀ g : Gal(Ω/K), ∀ a : A, ρ (AlgEquiv.restrictNormalHom E g) a = A.ρ g a) ∧
          (∀ g h : Gal(Ω/K), d.val (AlgEquiv.restrictNormalHom E g, AlgEquiv.restrictNormalHom E h) =
            c.val (g, h)) := by
  obtain ⟨E, hact, hper⟩ := continuousFiniteCoefficientTwoCocycle_exists_finiteField A hA c
  obtain ⟨d, hd⟩ := finiteCoefficientTwoCocycle_exists_finite_descent A E hact c hper
  exact ⟨E, finiteStageCoefficientRepresentation A E hact, d,
    finiteStageCoefficientRepresentation_apply A E hact, hd⟩

end
end Dubon2026
