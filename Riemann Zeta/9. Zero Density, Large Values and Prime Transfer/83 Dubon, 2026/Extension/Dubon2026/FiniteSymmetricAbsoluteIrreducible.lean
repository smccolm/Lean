import Dubon2026.FiniteSymmetricMatrixIrreducible
import Dubon2026.HomogeneousSymmetricBaseChange
import Dubon2026.MatrixAdjointScalarDescent
import Mathlib.Algebra.CharP.Algebra

/-! Absolute irreducibility retains the original finite group and extends
only coefficients. The three explicit symmetric operators are already
defined over the original finite field; their native invariant-subspace proof works
over every coefficient extension. This serves the original residual
deformation and dual-Selmer inputs of DUB-17. -/

namespace Dubon2026
noncomputable section
open MvPolynomial Module Matrix
open scoped MatrixGroups

/-- The native three-operator argument transfers to the original column
coordinates through the proved monomial basis intertwining. -/
theorem symmetricMatrixThreeOperators_submodule_eq_top
    {K : Type*} [Field K] (n : ℕ) (u : Kˣ)
    (hu : 2 * n < orderOf u) (hn : (n.factorial : K) ≠ 0)
    (p : Submodule K (Fin (n + 1) → K)) (hpne : p ≠ ⊥)
    (hpDiagonal : ∀ w ∈ p, Matrix.toLin'
      (homogeneousSymmetricGL n (Matrix.SpecialLinearGroup.toGL (ringSL2UnitDiagonal u))).val w ∈ p)
    (hpLower : ∀ w ∈ p, Matrix.toLin'
      (homogeneousSymmetricGL n (Matrix.SpecialLinearGroup.toGL (ringLowerUnipotent (1 : K)))).val w ∈ p)
    (hpUpper : ∀ w ∈ p, Matrix.toLin'
      (homogeneousSymmetricGL n (Matrix.SpecialLinearGroup.toGL (ringUpperUnipotent (1 : K)))).val w ∈ p) :
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
  have htransfer (g : SL(2, K))
      (hg : ∀ w ∈ p, Matrix.toLin' (homogeneousSymmetricGL n (Matrix.SpecialLinearGroup.toGL g)).val w ∈ p) :
      ∀ w ∈ P, homogeneousMatrixAction n g.val w ∈ P := by
    intro w hw
    change e (homogeneousGLRepresentation n (Matrix.SpecialLinearGroup.toGL g) w) ∈ p
    rw [homogeneousSymmetricGL_equivFun_action]
    exact hg (e w) hw
  have hP := symmetricThreeOperators_submodule_eq_top n u hu hn P hPne
    (htransfer _ hpDiagonal) (htransfer _ hpLower) (htransfer _ hpUpper)
  apply top_unique
  intro w _
  have hmem : e.symm w ∈ P := by rw [hP]; exact Submodule.mem_top
  change e (e.symm w) ∈ p at hmem
  simpa only [e.apply_symm_apply] using hmem

/-- Coefficient extension preserves the literal native determinant-one diagonal. -/
theorem map_ringSL2UnitDiagonal {K L : Type*} [Field K] [Field L]
    (φ : K →+* L) (u : Kˣ) :
    GeneralLinearGroup.map φ (Matrix.SpecialLinearGroup.toGL (ringSL2UnitDiagonal u)) =
      Matrix.SpecialLinearGroup.toGL (ringSL2UnitDiagonal (Units.map φ.toMonoidHom u)) := by
  apply Units.ext
  ext i j
  change φ ((ringSL2UnitDiagonal u).val i j) =
    (ringSL2UnitDiagonal (Units.map φ.toMonoidHom u)).val i j
  fin_cases i <;> fin_cases j <;> simp [ringSL2UnitDiagonal]

/-- Coefficient extension preserves the literal lower unipotent of entry one. -/
theorem map_ringLowerUnipotent_one {K L : Type*} [Field K] [Field L]
    (φ : K →+* L) :
    GeneralLinearGroup.map φ (Matrix.SpecialLinearGroup.toGL (ringLowerUnipotent (1 : K))) =
      Matrix.SpecialLinearGroup.toGL (ringLowerUnipotent (1 : L)) := by
  apply Units.ext
  ext i j
  change φ ((ringLowerUnipotent (1 : K)).val i j) = (ringLowerUnipotent (1 : L)).val i j
  fin_cases i <;> fin_cases j <;> simp [ringLowerUnipotent]

/-- Coefficient extension preserves the literal upper unipotent of entry one. -/
theorem map_ringUpperUnipotent_one {K L : Type*} [Field K] [Field L]
    (φ : K →+* L) :
    GeneralLinearGroup.map φ (Matrix.SpecialLinearGroup.toGL (ringUpperUnipotent (1 : K))) =
      Matrix.SpecialLinearGroup.toGL (ringUpperUnipotent (1 : L)) := by
  apply Units.ext
  ext i j
  change φ ((ringUpperUnipotent (1 : K)).val i j) = (ringUpperUnipotent (1 : L)).val i j
  fin_cases i <;> fin_cases j <;> simp [ringUpperUnipotent]

/-- The genuine original residual representation remains irreducible over
every coefficient-field extension, while its original group is unchanged.
The actual symmetric finite-field image and numerical bounds discharge the
irreducibility premise consumed by the native deformation theory. -/
theorem finiteField_matrixRepresentation_absoluteIrreducible_of_symmetricSL2_image
    {G K L : Type} [Group G] [Field K] [Finite K] [Field L] (q n : ℕ)
    [Fact q.Prime] [CharP K q] [Algebra K L]
    (hn : 2 * n < Nat.card K - 1) (hchar : n < q)
    (ρ : G →* GeneralLinearGroup (Fin (n + 1)) K)
    (himage : ((homogeneousSymmetricGL (R := K) n).comp
      Matrix.SpecialLinearGroup.toGL).range ≤ ρ.range) :
    Representation.IsIrreducible (matrixStandardRepresentation (matrixCoefficientExtension (L := L) ρ)) := by
  let φ := algebraMap K L
  let ρL := matrixCoefficientExtension (L := L) ρ
  letI : CharP L q := charP_of_injective_algebraMap φ.injective q
  obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  rw [Nat.card_units] at hu
  let uL := Units.map φ.toMonoidHom u
  have huL : 2 * n < orderOf uL := by
    have ho := orderOf_injective (Units.map φ.toMonoidHom) (Units.map_injective φ.injective) u
    change orderOf uL = orderOf u at ho
    rwa [ho, hu]
  have htb : (⊤ : Subrepresentation (matrixStandardRepresentation ρL)) ≠ ⊥ := by
    intro h
    exact top_ne_bot (α := Submodule L (Fin (n + 1) → L)) (congrArg Subrepresentation.toSubmodule h)
  letI : Nontrivial (Subrepresentation (matrixStandardRepresentation ρL)) := ⟨⟨⊤, ⊥, htb⟩⟩
  refine { eq_bot_or_eq_top := ?_ }
  intro W
  by_cases hW : W.toSubmodule = ⊥
  · exact Or.inl (Subrepresentation.toSubmodule_injective hW)
  · right
    apply Subrepresentation.toSubmodule_injective
    have hstable (g : SL(2, K)) (w : Fin (n + 1) → L) (hw : w ∈ W.toSubmodule) :
        Matrix.toLin' (GeneralLinearGroup.map φ
          (homogeneousSymmetricGL n (Matrix.SpecialLinearGroup.toGL g))).val w ∈ W.toSubmodule := by
      obtain ⟨γ, hγ⟩ := himage (show ((homogeneousSymmetricGL n).comp
        Matrix.SpecialLinearGroup.toGL) g ∈ ((homogeneousSymmetricGL n).comp
          Matrix.SpecialLinearGroup.toGL).range from ⟨g, rfl⟩)
      have hm := W.apply_mem_toSubmodule γ hw
      change Matrix.toLin' (GeneralLinearGroup.map φ (ρ γ)).val w ∈ W.toSubmodule at hm
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

/-- The prime-field case derives both numerical requirements from the
single original degree bound, for every coefficient-field extension. -/
theorem primeField_matrixRepresentation_absoluteIrreducible_of_symmetricSL2_image
    {G L : Type} [Group G] [Field L] (q n : ℕ) [Fact q.Prime]
    [Algebra (ZMod q) L] (hn : 2 * n < q - 1)
    (ρ : G →* GeneralLinearGroup (Fin (n + 1)) (ZMod q))
    (himage : ((homogeneousSymmetricGL (R := ZMod q) n).comp
      Matrix.SpecialLinearGroup.toGL).range ≤ ρ.range) :
    Representation.IsIrreducible (matrixStandardRepresentation (matrixCoefficientExtension (L := L) ρ)) :=
  finiteField_matrixRepresentation_absoluteIrreducible_of_symmetricSL2_image q n
    (by simpa only [Nat.card_zmod] using hn) (by omega) ρ himage

end
end Dubon2026
