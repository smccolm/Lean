import Dubon2026.FiniteSymmetricAbsoluteIrreducible

/-! DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> higher symmetric-power
continuation -> automorphy -> absolute residual symmetric-power irreducibility.
The projective classification gives SL₂ over a possibly proper finite subfield.
Reuse the native three-operator proof without identifying that subfield with the
original residue field. Small-image arithmetic exclusions remain separate. -/
namespace Dubon2026
noncomputable section
open Module Matrix
open scoped MatrixGroups

/-- Embedded finite-subfield symmetric matrices force irreducibility over the
actual ambient field. Only the original finite subfield controls the bound. -/
theorem finiteSubfield_matrixRepresentation_irreducible_of_symmetricSL2_image
    {G K L : Type} [Group G] [Field K] [Finite K] [Field L] (q n : ℕ)
    [Fact q.Prime] [CharP K q] (φ : K →+* L)
    (hn : 2 * n < Nat.card K - 1) (hchar : n < q)
    (ρ : G →* GeneralLinearGroup (Fin (n + 1)) L)
    (himage : ((GeneralLinearGroup.map φ).comp ((homogeneousSymmetricGL (R := K) n).comp
      Matrix.SpecialLinearGroup.toGL)).range ≤ ρ.range) :
    Representation.IsIrreducible (matrixStandardRepresentation ρ) := by
  letI : CharP L q := charP_of_injective_ringHom φ.injective q
  obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  rw [Nat.card_units] at hu
  let uL := Units.map φ.toMonoidHom u
  have huL : 2 * n < orderOf uL := by
    have ho := orderOf_injective (Units.map φ.toMonoidHom) (Units.map_injective φ.injective) u
    change orderOf uL = orderOf u at ho
    rwa [ho, hu]
  have htb : (⊤ : Subrepresentation (matrixStandardRepresentation ρ)) ≠ ⊥ := by
    intro h
    exact top_ne_bot (α := Submodule L (Fin (n + 1) → L)) (congrArg Subrepresentation.toSubmodule h)
  letI : Nontrivial (Subrepresentation (matrixStandardRepresentation ρ)) := ⟨⟨⊤, ⊥, htb⟩⟩
  refine { eq_bot_or_eq_top := ?_ }
  intro W
  by_cases hW : W.toSubmodule = ⊥
  · exact Or.inl (Subrepresentation.toSubmodule_injective hW)
  · right
    apply Subrepresentation.toSubmodule_injective
    have hstable (g : SL(2, K)) (w : Fin (n + 1) → L) (hw : w ∈ W.toSubmodule) :
        Matrix.toLin' (GeneralLinearGroup.map φ
          (homogeneousSymmetricGL n (Matrix.SpecialLinearGroup.toGL g))).val w ∈ W.toSubmodule := by
      obtain ⟨γ, hγ⟩ := himage (show ((GeneralLinearGroup.map φ).comp ((homogeneousSymmetricGL n).comp
        Matrix.SpecialLinearGroup.toGL)) g ∈ _ from ⟨g, rfl⟩)
      have hm := W.apply_mem_toSubmodule γ hw
      change Matrix.toLin' (ρ γ).val w ∈ W.toSubmodule at hm
      rw [hγ] at hm
      exact hm
    apply symmetricMatrixThreeOperators_submodule_eq_top n uL huL
      (factorial_cast_ne_zero_of_lt_char q n hchar) W.toSubmodule hW
    · intro w hw
      have hm := hstable (ringSL2UnitDiagonal u) w hw
      rwa [homogeneousSymmetricGL_map, map_ringSL2UnitDiagonal] at hm
    · intro w hw
      have hm := hstable (ringLowerUnipotent 1) w hw
      rwa [homogeneousSymmetricGL_map, map_ringLowerUnipotent_one] at hm
    · intro w hw
      have hm := hstable (ringUpperUnipotent 1) w hw
      rwa [homogeneousSymmetricGL_map, map_ringUpperUnipotent_one] at hm

end
end Dubon2026
