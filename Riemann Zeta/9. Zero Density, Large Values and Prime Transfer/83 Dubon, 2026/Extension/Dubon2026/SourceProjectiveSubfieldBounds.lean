import Dubon2026.SourceProjectiveSL2Lift

/-! DUB-17/18 -> residual large image -> exact linear coefficient-subfield bounds.
Projective PSL₂/PGL₂ bounds lift to a linear SL₂ lower bound and a scalar-GL₂
upper bound. The required arithmetic exclusion of the other cases stays open. -/
namespace Dubon2026.SourceDickson
noncomputable section
open Matrix
open scoped MatrixGroups

/-- Membership in the projective subfield image supplies an actual scalar-times-subfield matrix. -/
theorem scalar_subfield_matrix_of_projective_mem {F L : Type*} [Field F] [Field L]
    (j : F →+* L) (x : GL (Fin 2) L)
    (hx : QuotientGroup.mk' (Subgroup.center (GL (Fin 2) L)) x ∈ (pglMap j).range) :
    ∃ (u : Lˣ) (a : GL (Fin 2) F),
      x = GeneralLinearGroup.scalar (Fin 2) u * GeneralLinearGroup.map j a := by
  obtain ⟨y, hy⟩ := hx
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective y
  have hc : x / GeneralLinearGroup.map j a ∈ Subgroup.center (GL (Fin 2) L) :=
    QuotientGroup.eq_iff_div_mem.mp hy.symm
  rw [GeneralLinearGroup.center_eq_range_scalar] at hc
  obtain ⟨u, hu⟩ := hc
  refine ⟨u, a, ?_⟩
  rw [hu, div_mul_cancel]

/-- A change of basis commutes with projectivizing a matrix subgroup. -/
theorem projective_image_conjugate {L : Type*} [Field L]
    (H : Subgroup (GL (Fin 2) L)) (A : GL (Fin 2) L) :
    (H.map (MulEquiv.toMonoidHom (MulAut.conj A))).map
      (QuotientGroup.mk' (Subgroup.center (GL (Fin 2) L))) =
    (H.map (QuotientGroup.mk' (Subgroup.center (GL (Fin 2) L)))).map
      (MulEquiv.toMonoidHom (MulAut.conj
        (QuotientGroup.mk' (Subgroup.center (GL (Fin 2) L)) A))) := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

/-- Projective subfield bounds after conjugacy give the literal linear bounds after a matrix change of basis. -/
theorem exists_linear_subfield_bounds_of_projective_conjugacy
    {F L : Type*} [Field F] [Field L] [NeZero (2 : F)] [NeZero (3 : F)]
    (j : F →+* L) (H : Subgroup (GL (Fin 2) L))
    (g : PGLOf L)
    (hlo : (PSLImageInPGL F).map (pglMap j) ≤
      (H.map (QuotientGroup.mk' (Subgroup.center (GL (Fin 2) L)))).map
        (MulEquiv.toMonoidHom (MulAut.conj g)))
    (hhi : (H.map (QuotientGroup.mk' (Subgroup.center (GL (Fin 2) L)))).map
        (MulEquiv.toMonoidHom (MulAut.conj g)) ≤ (pglMap j).range) :
    ∃ A : GL (Fin 2) L,
      ((GeneralLinearGroup.map j).comp
        (SpecialLinearGroup.toGL (n := Fin 2) (R := F))).range ≤
          H.map (MulEquiv.toMonoidHom (MulAut.conj A)) ∧
      ∀ x ∈ H.map (MulEquiv.toMonoidHom (MulAut.conj A)),
        ∃ (u : Lˣ) (a : GL (Fin 2) F),
          x = GeneralLinearGroup.scalar (Fin 2) u * GeneralLinearGroup.map j a := by
  obtain ⟨A, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center (GL (Fin 2) L)) g
  rw [← projective_image_conjugate H A] at hlo hhi
  refine ⟨A, subfieldSL2_le_of_projective_image j _ hlo, ?_⟩
  intro x hx
  exact scalar_subfield_matrix_of_projective_mem j x
    (hhi (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩))

end
end Dubon2026.SourceDickson
