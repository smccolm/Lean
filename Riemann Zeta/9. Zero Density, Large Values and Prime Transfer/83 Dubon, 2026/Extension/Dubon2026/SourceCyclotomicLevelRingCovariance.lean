import Dubon2026.SourceFrickeCyclotomicConjugateRelation
import Dubon2026.SourceCyclotomicModularLift

/-! DUB-17/18 -> actual Gamma1 differential realization -> rational Fourier
structure -> modular covariance of analytic cyclotomic conjugation. Adjoin
induction uses the literal generator permutation and actual modular action.
It constructs original-ring conjugates together with the required covariance;
no field automorphism is assumed to preserve analytic modularity. -/
namespace Dubon2026.SourceFricke
noncomputable section
open UpperHalfPlane SourceFunctionField
open scoped MatrixGroups Manifold ModularForm

theorem exists_cyclotomic_levelRing_modular_conjugate {N : ℕ} [NeZero N]
    (σ : kN N ≃ₐ[ℚ] kN N) (s : ℕ) (hs : s.Coprime N)
    (hσ : σ (zetaK N) = zetaK N ^ s) (A A' : SL(2, ℤ))
    (hconj : ∀ v : Fin 2 → ZMod N,
      vecMulSL N (cyclotomicTorsionVector s v) A =
        cyclotomicTorsionVector s (vecMulSL N v A'))
    {P : ℍ → ℂ} (hP : P ∈ cyclotomicLevelRing N) :
    ∃ P' ∈ cyclotomicLevelRing N, CyclotomicConjugates σ P P' ∧
      CyclotomicConjugates σ (P ∘ (A' • ·)) (P' ∘ (A • ·)) := by
  induction hP using Algebra.adjoin_induction with
  | mem P hP =>
    rcases hP with rfl | ⟨i, rfl⟩
    · refine ⟨JMultiplicity.jf, Algebra.subset_adjoin (Set.mem_insert _ _),
        CyclotomicConjugates.j σ, ?_⟩
      simpa only [Function.comp_def, JMultiplicity.jf_smul] using CyclotomicConjugates.j σ
    · refine ⟨frickeF N (cyclotomicFrickeIndex s hs i).1,
        Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨_, rfl⟩),
        CyclotomicConjugates.fricke σ s hs hσ i, ?_⟩
      have he1 : frickeF N i.1 ∘ (A' • ·) = frickeF N (frickeIdxPerm N A' i).1 := by
        funext τ
        exact frickeF_slash i.1 A' τ
      have he2 : frickeF N (cyclotomicFrickeIndex s hs i).1 ∘ (A • ·) =
          frickeF N (cyclotomicFrickeIndex s hs (frickeIdxPerm N A' i)).1 := by
        funext τ
        rw [Function.comp_apply, frickeF_slash]
        exact congrArg (fun v => frickeF N v τ) (hconj i.1)
      rw [he1, he2]
      exact CyclotomicConjugates.fricke σ s hs hσ _
  | algebraMap c =>
    exact ⟨algebraMap (kN N) (ℍ → ℂ) (σ c), Subalgebra.algebraMap_mem _ (σ c),
      CyclotomicConjugates.const σ c, CyclotomicConjugates.const σ c⟩
  | add P Q _ _ hP hQ =>
    obtain ⟨P', hP', hPP', hPA⟩ := hP
    obtain ⟨Q', hQ', hQQ', hQA⟩ := hQ
    exact ⟨P' + Q', Subalgebra.add_mem _ hP' hQ', hPP'.add hQQ', hPA.add hQA⟩
  | mul P Q _ _ hP hQ =>
    obtain ⟨P', hP', hPP', hPA⟩ := hP
    obtain ⟨Q', hQ', hQQ', hQA⟩ := hQ
    exact ⟨P' * Q', Subalgebra.mul_mem _ hP' hQ', hPP'.mul hQQ', hPA.mul hQA⟩

end
end Dubon2026.SourceFricke
