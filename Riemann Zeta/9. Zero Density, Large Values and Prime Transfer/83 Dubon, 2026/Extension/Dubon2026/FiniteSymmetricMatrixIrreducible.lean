import Dubon2026.FiniteSymmetricIrreducible
import Dubon2026.MatrixAdjointSchur

/-! Irreducibility of the literal matrix representation used by the
arithmetic modules, consumed from the proved native homogeneous action.
The residual image of the modular representation remains to be constructed. -/

namespace Dubon2026
noncomputable section
open MvPolynomial Module Matrix
open scoped MatrixGroups

/-- The original monomial coordinates intertwine the actual polynomial
action and the actual symmetric general-linear matrices. -/
theorem homogeneousSymmetricGL_equivFun_action
    {K : Type*} [Field K] (n : ℕ) (g : GeneralLinearGroup (Fin 2) K)
    (w : homogeneousSubmodule (Fin 2) K n) :
    (binaryHomogeneousMonomialBasis n).equivFun (homogeneousGLRepresentation n g w) =
      Matrix.toLin' (homogeneousSymmetricGL n g).val
        ((binaryHomogeneousMonomialBasis n).equivFun w) := by
  rw [Matrix.toLin'_apply, homogeneousSymmetricGL_val]
  exact (LinearMap.toMatrix_mulVec_repr (binaryHomogeneousMonomialBasis n)
    (binaryHomogeneousMonomialBasis n) (homogeneousGLRepresentation n g) w).symm

/-- No proper nonzero original column-vector subspace is stable under the
literal symmetric SL2 matrices in the stated degree and field range. -/
theorem finiteSymmetricMatrix_submodule_eq_top
    {K : Type*} [Field K] (n : ℕ) (u : Kˣ)
    (hu : 2 * n < orderOf u) (hn : (n.factorial : K) ≠ 0)
    (p : Submodule K (Fin (n + 1) → K)) (hpne : p ≠ ⊥)
    (hp : ∀ g : SL(2, K), ∀ w ∈ p,
      Matrix.toLin' (homogeneousSymmetricGL n (Matrix.SpecialLinearGroup.toGL g)).val w ∈ p) :
    p = ⊤ := by
  let e := (binaryHomogeneousMonomialBasis (R := K) n).equivFun
  let P := p.comap e.toLinearMap
  have hPne : P ≠ ⊥ := by
    intro hz
    apply hpne
    apply bot_unique
    intro w hw
    have hmem : e.symm w ∈ P := by
      change e (e.symm w) ∈ p
      simpa only [e.apply_symm_apply] using hw
    rw [hz, Submodule.mem_bot] at hmem
    have he := congrArg e hmem
    simpa only [e.apply_symm_apply, map_zero, Submodule.mem_bot] using he
  have hP : P = ⊤ := by
    apply finiteSymmetricSL2_submodule_eq_top n u hu hn P hPne
    intro g w hw
    change e (homogeneousGLRepresentation n (Matrix.SpecialLinearGroup.toGL g) w) ∈ p
    rw [homogeneousSymmetricGL_equivFun_action]
    exact hp g (e w) hw
  apply top_unique
  intro w _
  have hmem : e.symm w ∈ P := by rw [hP]; exact Submodule.mem_top
  change e (e.symm w) ∈ p at hmem
  simpa only [e.apply_symm_apply] using hmem

/-- Any original matrix representation containing the literal symmetric
SL2 image is irreducible in the proved degree and field range. -/
theorem matrixRepresentation_irreducible_of_symmetricSL2_image
    {G K : Type} [Group G] [Field K] (n : ℕ) (u : Kˣ)
    (hu : 2 * n < orderOf u) (hn : (n.factorial : K) ≠ 0)
    (ρ : G →* GeneralLinearGroup (Fin (n + 1)) K)
    (himage : ((homogeneousSymmetricGL (R := K) n).comp
      Matrix.SpecialLinearGroup.toGL).range ≤ ρ.range) :
    Representation.IsIrreducible (matrixStandardRepresentation ρ) := by
  have htb : (⊤ : Subrepresentation (matrixStandardRepresentation ρ)) ≠ ⊥ := by
    intro h
    have he := congrArg Subrepresentation.toSubmodule h
    exact top_ne_bot (α := Submodule K (Fin (n + 1) → K)) he
  letI : Nontrivial (Subrepresentation (matrixStandardRepresentation ρ)) := ⟨⟨⊤, ⊥, htb⟩⟩
  refine { eq_bot_or_eq_top := ?_ }
  intro W
  by_cases hW : W.toSubmodule = ⊥
  · exact Or.inl (Subrepresentation.toSubmodule_injective hW)
  · right
    apply Subrepresentation.toSubmodule_injective
    apply finiteSymmetricMatrix_submodule_eq_top n u hu hn W.toSubmodule hW
    intro g w hw
    obtain ⟨γ, hγ⟩ := himage (show ((homogeneousSymmetricGL n).comp
      Matrix.SpecialLinearGroup.toGL) g ∈ ((homogeneousSymmetricGL n).comp
        Matrix.SpecialLinearGroup.toGL).range from ⟨g, rfl⟩)
    have hm := W.apply_mem_toSubmodule γ hw
    change Matrix.toLin' (ρ γ).val w ∈ W.toSubmodule at hm
    rw [hγ] at hm
    exact hm

/-- For the actual prime field, the size bound constructs the torus
element and proves factorial nonvanishing in the original representation. -/
theorem primeField_matrixRepresentation_irreducible_of_symmetricSL2_image
    {G : Type} [Group G] (q n : ℕ) [Fact q.Prime] (hn : 2 * n < q - 1)
    (ρ : G →* GeneralLinearGroup (Fin (n + 1)) (ZMod q))
    (himage : ((homogeneousSymmetricGL (R := ZMod q) n).comp
      Matrix.SpecialLinearGroup.toGL).range ≤ ρ.range) :
    Representation.IsIrreducible (matrixStandardRepresentation ρ) := by
  obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod q)ˣ)
  rw [Nat.card_units, Nat.card_zmod] at hu
  apply matrixRepresentation_irreducible_of_symmetricSL2_image n u _
    (factorial_cast_ne_zero_of_lt_char q n (by omega)) ρ himage
  rwa [hu]

end
end Dubon2026
