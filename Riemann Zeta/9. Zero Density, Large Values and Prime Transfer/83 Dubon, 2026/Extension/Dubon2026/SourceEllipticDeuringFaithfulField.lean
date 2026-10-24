import Dubon2026.SourceEllipticDeuringGaloisModel
import Dubon2026.SourceEllipticDivisionFieldRestriction
import Dubon2026.SourceEllipticFullTorsionFieldExtension
import Dubon2026.SourceEllipticTrivialInertiaTorsion
import Dubon2026.IntermediateFieldSupEmbeddings

/-! DUB-17/18 -> characteristic-two modular genus/Picard -> actual faithful inertia.
The already proved division-field compositum and injective torsion reduction
assemble the explicit Deuring generator field. Identity reduced cocycle
implies identity inertia, without assuming a torsion-fixing certificate. -/
namespace Dubon2026.SourceEllipticDivisionField
open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing
open SourceEllipticReduction SourceEllipticDeuring
noncomputable section

theorem exists_faithful_deuring_good_model_field
    {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] [IsAlgClosed Ω]
    [Algebra.IsAlgebraic F Ω] [DecidableEq Ω]
    (E : WeierstrassCurve F) [E.IsElliptic] (h3 : (3 : F) ≠ 0)
    {N : ℕ} (hN : (N : F) ≠ 0) :
    ∃ M : IntermediateField F Ω, FiniteDimensional F M ∧ IsGalois F M ∧
      Nat.card {P : (E.baseChange M).toAffine.Point // N • P = 0} = N ^ 2 ∧
      ∀ (A : ValuationSubring M), IsUnit (3 : A) → IsUnit (N : A) →
        algebraMap F M E.j ∈ A →
      ∃ (W : WeierstrassCurve A) (κ : VariableChange M),
        κ • E.baseChange M = W.map A.subtype ∧ IsUnit W.Δ ∧
        ∀ (σ : M ≃ₐ[F] M) (hσ : σ ∈ A.decompositionSubgroup F),
          (⟨σ, hσ⟩ : A.decompositionSubgroup F) ∈ A.inertiaSubgroup F →
          (∃ g : VariableChange A,
            g.map A.subtype = κ * (κ.map (σ : M →+* M))⁻¹ ∧
            g.map (residue A) = 1) → σ = 1 := by
  obtain ⟨L, hLfd, hLgal, hLcard, hLfaith⟩ := exists_divisionField (Ω := Ω) E hN
  obtain ⟨S, hSfd, hSgal, hS⟩ := exists_deuring_galois_model_faithful (Ω := Ω) E h3
  haveI := hLfd
  haveI := hLgal
  haveI := hSfd
  haveI := hSgal
  let M := L ⊔ S
  have hLM : L ≤ M := le_sup_left
  have hSM : S ≤ M := le_sup_right
  refine ⟨M, inferInstance, inferInstance,
    card_torsion_of_containing_full_field E hN L M hLM hLcard, ?_⟩
  intro A h3A hNA hjA
  obtain ⟨W, κ, hκ, hW, hfaith⟩ := hS M hSM A h3A hjA
  refine ⟨W, κ, hκ, hW, ?_⟩
  intro σ hσ hI hg
  obtain ⟨g, hg, hg1⟩ := hg
  letI : DecidableEq (ResidueField A) := Classical.decEq _
  have hΔ : (W.map (residue A)).Δ ≠ 0 := (map_residue_Δ_ne_zero_iff W).mpr hW
  have hfixT (n : ℕ) (hn : IsUnit (n : A))
      (P : (E.baseChange M).toAffine.Point) (hP : n • P = 0) :
      Point.map (σ : M →ₐ[F] M) P = P :=
    galois_fixes_torsion_of_residue_cocycle_one E W κ hκ hΔ hn g σ hσ hI hg hg1 P hP
  have hfixS : ∀ x : M, (x : Ω) ∈ S → σ x = x :=
    hfaith σ hσ hI (hfixT 3 h3A) ⟨g, hg, hg1⟩
  have hfixL : ∀ x : M, (x : Ω) ∈ L → σ x = x :=
    fixes_division_field_of_fixes_torsion E L M hLM N hLfaith σ (hfixT N hNA)
  have htop : (⊤ : Subfield M) ≤ σ.toRingHom.eqLocusField (RingHom.id M) := by
    rw [← intermediateField_sup_inclusion_ranges L S]
    refine sup_le ?_ ?_
    · rintro _ ⟨x, rfl⟩
      exact hfixL _ x.property
    · rintro _ ⟨x, rfl⟩
      exact hfixS _ x.property
  apply AlgEquiv.ext
  intro x
  exact htop (Subfield.mem_top x)

end
end Dubon2026.SourceEllipticDivisionField
