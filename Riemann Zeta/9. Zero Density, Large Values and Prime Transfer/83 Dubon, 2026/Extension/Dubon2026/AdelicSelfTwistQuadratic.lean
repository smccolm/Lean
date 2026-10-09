import Dubon2026.AdelicNonCMDirichletTwist

/-! # The actual trivial central action forces every original determinant self-twist to be quadratic -/

namespace Dubon2026

noncomputable section
open NumberField Matrix

private theorem scalarTwist_character_one_of_trivial_action {G V : Type*} [Group G]
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (χ : G →* ℂ)
    (T : Representation.IntertwiningMap ρ (scalarTwistRepresentation ρ χ))
    (g : G) (hg : ∀ x, ρ g x = x) (x : V) (hx : T x ≠ 0) : χ g = 1 := by
  have he := scalarTwist_intertwining_apply ρ ρ χ T g x
  rw [hg, hg] at he
  exact (smul_left_injective ℂ hx) (he.symm.trans (one_smul ℂ (T x)).symm)

/-- An actual injective self-twist of the original primitive adelic representation automatically has square-one idele values, because every original scalar acts trivially and its determinant is the square of that idele. -/
theorem adelicSelfTwist_quadratic {N : ℕ} [NeZero N] {k : ℤ}
    (F : PrimitiveCuspForm N k) (ψ : (AdeleRing ℤ ℚ)ˣ →* ℂ)
    (T : Representation.IntertwiningMap (adelicCyclicHilbertRepresentation F.toCuspForm)
      (scalarTwistRepresentation (adelicCyclicHilbertRepresentation F.toCuspForm)
        (ψ.comp GeneralLinearGroup.det))) (hT : Function.Injective T) :
    ∀ a, ψ a ^ 2 = 1 := by
  have hn : T (adelicCyclicHilbertGenerator F.toCuspForm) ≠ 0 := by
    intro hz
    apply adelicCyclicHilbertGenerator_ne_zero F.toCuspForm (primitiveCuspForm_ne_zero F)
    apply hT
    exact hz.trans (map_zero T).symm
  intro a
  have he := scalarTwist_character_one_of_trivial_action
    (adelicCyclicHilbertRepresentation F.toCuspForm) (ψ.comp GeneralLinearGroup.det) T
    (GeneralLinearGroup.scalar (Fin 2) a) (adelicCyclicHilbert_scalar_action F.toCuspForm a)
    (adelicCyclicHilbertGenerator F.toCuspForm) hn
  simpa only [MonoidHom.comp_apply, GeneralLinearGroup.det_scalar, Fintype.card_fin, map_pow] using he

end
end Dubon2026
