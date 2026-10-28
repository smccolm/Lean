import Dubon2026.SourceH1TraceBaseChangeCoefficient

/-! DUB-17/18 -> original Gamma1 arithmetic realization -> diamond
transfer invariance. Identify the literal conjugation preimage with the
proved equal original cover subgroup, retaining the native trace rather
than introducing a replacement transfer.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
variable {R G : Type} [CommRing R] [Group G] (A : Rep R G)

/-- Identity coefficients on the actual equality-induced subgroup map. -/
def sourceSubgroupEqualityCoefficient {S T : Subgroup G} (h : S = T) :
    Rep.res (MulEquiv.subgroupCongr h).toMonoidHom (Rep.res T.subtype A) ⟶
      Rep.res S.subtype A := by
  subst T
  exact 𝟙 (Rep.res S.subtype A)

theorem sourceSubgroupH1Trace_equality {S T : Subgroup G} (h : S = T)
    [fS : Fintype (G ⧸ S)] [fT : Fintype (G ⧸ T)] :
    groupCohomology.map (MulEquiv.subgroupCongr h).toMonoidHom
        (sourceSubgroupEqualityCoefficient A h) 1 ≫ subgroupCohomologyTrace A S 1 =
      subgroupCohomologyTrace A T 1 := by
  subst T
  have hf : fT = fS := Subsingleton.elim _ _
  subst fT
  change groupCohomology.map (MonoidHom.id S) (𝟙 (Rep.res S.subtype A)) 1 ≫
    subgroupCohomologyTrace A S 1 = subgroupCohomologyTrace A S 1
  rw [groupCohomology.map_id, Category.id_comp]

end
end Dubon2026
