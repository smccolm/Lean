import Dubon2026.FiniteAdeleResidueUnits
import Mathlib.NumberTheory.DirichletCharacter.Basic

/-! # The original finite-adelic residue maps commute with actual changes of modulus -/

namespace Dubon2026

noncomputable section

/-- Divisibility of the original modulus gives actual inclusion of the corresponding finite-adelic integer ideals. -/
theorem finiteAdeleLevelMultiple_of_dvd (M D : ℕ) (h : M ∣ D)
    {x : IsDedekindDomain.FiniteAdeleRing ℤ ℚ} (hx : finiteAdeleLevelMultiple D x) :
    finiteAdeleLevelMultiple M x := by
  obtain ⟨k, rfl⟩ := h
  obtain ⟨y, hy, he⟩ := hx
  refine ⟨(k : IsDedekindDomain.FiniteAdeleRing ℤ ℚ) * y,
    finiteAdeleIntegerSubring.mul_mem (by simp) hy, ?_⟩
  simpa only [Nat.cast_mul, mul_assoc] using he

/-- The actual original residue homomorphisms agree under the genuine ordinary residue-ring reduction. -/
theorem finiteAdeleResidue_changeLevel (M D : ℕ) [NeZero M] [NeZero D] (h : M ∣ D)
    (x : finiteAdeleIntegerSubring) :
    ZMod.castHom h (ZMod M) (finiteAdeleResidue D x) = finiteAdeleResidue M x := by
  have he := (finiteAdeleResidue_eq_intCast_iff M x (finiteAdeleResidueInteger D x)).mpr
    (finiteAdeleLevelMultiple_of_dvd M D h (finiteAdeleResidueInteger_spec D x))
  rw [he]
  change ZMod.castHom h (ZMod M) ((finiteAdeleResidueInteger D x : ℤ) : ZMod D) = _
  exact map_intCast _ _

/-- Changing a Dirichlet level preserves exactly its values on the original integral-idele residues. -/
theorem dirichlet_changeLevel_integral_residue {M D : ℕ} [NeZero M] [NeZero D]
    (χ : DirichletCharacter ℂ M) (h : M ∣ D) (u : finiteAdeleIntegerSubringˣ) :
    DirichletCharacter.changeLevel h χ (finiteAdeleResidue D u.val) = χ (finiteAdeleResidue M u.val) := by
  have he := DirichletCharacter.changeLevel_eq_cast_of_dvd χ h
    (Units.map (finiteAdeleResidue D).toMonoidHom u)
  have hc : ZMod.cast (finiteAdeleResidue D u.val) = finiteAdeleResidue M u.val :=
    finiteAdeleResidue_changeLevel M D h u.val
  exact he.trans (congrArg χ hc)

end
end Dubon2026
