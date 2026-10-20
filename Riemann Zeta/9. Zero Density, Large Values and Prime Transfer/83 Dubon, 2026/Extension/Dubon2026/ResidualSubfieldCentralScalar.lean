import Dubon2026.ResidualGL2CentralScalar

/-! The scalar witness for the exact coefficient-subfield image bounds
in BLGG Lemma 6.1.2. The already proved perfection of SL2 and character-kernel
lifting are reused; the ambient coefficient field need not equal the image field. -/

namespace Dubon2026
noncomputable section
open Matrix
open scoped MatrixGroups

/-- Scalar general-linear matrices commute with the original change of coefficient ring. -/
theorem generalLinear_map_scalar {ι R S : Type} [Fintype ι] [DecidableEq ι]
    [CommRing R] [CommRing S] (f : R →+* S) (u : Rˣ) :
    GeneralLinearGroup.map f (GeneralLinearGroup.scalar ι u) =
      GeneralLinearGroup.scalar ι (Units.map f.toMonoidHom u) := by
  apply Units.ext
  ext i j
  by_cases hij : i = j <;>
    simp [GeneralLinearGroup.map, GeneralLinearGroup.scalar, Matrix.scalar_apply,
      hij]

/-- The source SL2-subfield lower bound and scalar-GL2-subfield upper bound yield a central scalar with the square of any original character value. -/
theorem residualSubfieldGL2_exists_scalar_character_square
    {G B k k' : Type} [Group G] [CommGroup B] [Field k] [Field k']
    [NeZero (2 : k')] [NeZero (3 : k')]
    (f : k' →+* k) (ρ : G →* GeneralLinearGroup (Fin 2) k) (χ : G →* B)
    (himage : ((GeneralLinearGroup.map f).comp
      (SpecialLinearGroup.toGL (n := Fin 2) (R := k'))).range ≤ ρ.range)
    (g : G) (u : kˣ) (a : GeneralLinearGroup (Fin 2) k')
    (hg : ρ g = GeneralLinearGroup.scalar (Fin 2) u * GeneralLinearGroup.map f a) :
    ∃ σ : G, ∃ v : kˣ, χ σ = χ g ^ 2 ∧ ρ σ = GeneralLinearGroup.scalar (Fin 2) v := by
  let b := GeneralLinearGroup.scalar (Fin 2) (GeneralLinearGroup.det a) * (a ^ 2)⁻¹
  have hb : GeneralLinearGroup.det b = 1 := by
    simp [b, map_mul, map_inv, map_pow, GeneralLinearGroup.det_scalar]
  let s : SL(2, k') := ⟨b.val, congrArg Units.val hb⟩
  have hs : SpecialLinearGroup.toGL s = b := Units.ext rfl
  let ψ := (GeneralLinearGroup.map f).comp (SpecialLinearGroup.toGL (n := Fin 2) (R := k'))
  letI : Group.IsPerfect SL(2, k') := fieldSL2_isPerfect
  letI : Group.IsPerfect ψ.range := Group.IsPerfect.range ψ
  have hk := perfect_subgroup_le_map_character_kernel ρ χ ψ.range himage
  obtain ⟨τ, hτ, heτ⟩ := Subgroup.mem_map.mp (hk (show ψ s ∈ ψ.range from ⟨s, rfl⟩))
  let d := Units.map f.toMonoidHom (GeneralLinearGroup.det a)
  have hc : ψ s * (GeneralLinearGroup.map f a) ^ 2 = GeneralLinearGroup.scalar (Fin 2) d := by
    change GeneralLinearGroup.map f (SpecialLinearGroup.toGL s) * _ = _
    rw [hs]
    dsimp only [b]
    rw [map_mul, map_inv, map_pow, generalLinear_map_scalar, inv_mul_cancel_right]
  refine ⟨τ * g ^ 2, u ^ 2 * d, ?_, ?_⟩
  · change χ τ = 1 at hτ
    rw [map_mul, hτ, one_mul, map_pow]
  · rw [map_mul, map_pow, heτ, hg,
      (generalLinear_scalar_commute u (GeneralLinearGroup.map f a)).mul_pow,
      ← map_pow (GeneralLinearGroup.scalar (Fin 2)), ← mul_assoc,
      (generalLinear_scalar_commute (u ^ 2) (ψ s)).eq.symm, mul_assoc, hc, ← map_mul]

end
end Dubon2026
