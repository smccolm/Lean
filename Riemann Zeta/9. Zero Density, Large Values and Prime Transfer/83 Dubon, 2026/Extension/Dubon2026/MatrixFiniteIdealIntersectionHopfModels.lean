import Dubon2026.MatrixIdealIntersectionHopfModels
import Mathlib.Order.CompleteLattice.Finset

/-! # Actual finite nonempty intersections preserve original quotient models -/

namespace Dubon2026
noncomputable section
open Matrix
universe u

variable {R F K A ι η : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [PerfectField F] [Field K] [Algebra R F] [IsFractionRing R F]
  [Algebra R K] [Algebra F K] [IsScalarTower R F K] [Normal F K] [IsAlgClosed K]
  [CommRing A] [Fintype ι] [DecidableEq ι]

/-- Genuine models of a finite nonempty family of original quotient representations construct a model modulo the actual intersection of those original ideals. Each induction step uses the real equivariant product embedding and its integral subgroup model. -/
theorem matrixFiniteIdealIntersectionHopfModel_exists
    (I : η → Ideal A) (s : Finset η) (hs : s.Nonempty)
    (ρ : (K ≃ₐ[F] K) →* GeneralLinearGroup ι A)
    (hmodels : ∀ i ∈ s,
      Nonempty (FiniteFreeHopfPointModel.{u,u,u,u,u} R F K (Multiplicative (ι → A ⧸ I i))
        (matrixUnderlyingGroupAction (matrixIdealQuotientRepresentation (I i) ρ)))) :
    Nonempty (FiniteFreeHopfPointModel.{u,u,u,u,u} R F K
      (Multiplicative (ι → A ⧸ (⨅ i ∈ s, I i)))
      (matrixUnderlyingGroupAction (matrixIdealQuotientRepresentation (⨅ i ∈ s, I i) ρ))) := by
  classical
  revert hs hmodels
  induction s using Finset.induction_on with
  | empty =>
    intro hs
    exact False.elim (Finset.not_nonempty_empty hs)
  | @insert a s _ha ih =>
    intro _hs hmodels
    have hma := hmodels a (Finset.mem_insert_self _ _)
    by_cases hs : s.Nonempty
    · obtain ⟨ma⟩ := hma
      obtain ⟨ms⟩ := ih hs (fun i hi => hmodels i (Finset.mem_insert_of_mem hi))
      rw [Finset.iInf_insert]
      exact matrixIdealIntersectionHopfModel_exists (I a) (⨅ i ∈ s, I i) ρ ma ms
    · have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      subst s
      rw [Finset.insert_empty, Finset.iInf_singleton]
      exact hma

end
end Dubon2026
