import Dubon2026.FiniteIdeleDirichletCharacter
import Mathlib.Topology.Algebra.Group.Basic

/-! # Continuity of the genuine finite-idele Dirichlet character -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Filter
open scoped Topology

variable {D : ℕ} [NeZero D] (χ : DirichletCharacter ℂ D)

/-- On the actual principal integral-unit congruence neighborhood the constructed finite character equals one. -/
theorem finiteIdeleDirichletCharacter_congruence_one (a : (FiniteAdeleRing ℤ ℚ)ˣ)
    (ha : a.val ∈ finiteAdeleIntegerSubring) (hai : a.inv ∈ finiteAdeleIntegerSubring)
    (hD : finiteAdeleLevelMultiple D (a.val - 1)) : finiteIdeleDirichletCharacter χ a = 1 := by
  let u : finiteAdeleIntegerSubringˣ :=
    { val := ⟨a.val, ha⟩
      inv := ⟨a.inv, hai⟩
      val_inv := Subtype.ext a.val_inv
      inv_val := Subtype.ext a.inv_val }
  have hu : Units.map finiteAdeleIntegerSubring.subtype.toMonoidHom u = a := Units.ext rfl
  have hr : finiteAdeleResidue D u.val = 1 := by
    have h := finiteAdeleResidue_eq_intCast_iff D u.val 1
    simp only [Int.cast_one] at h
    exact h.mpr hD
  rw [← hu, finiteIdeleDirichletCharacter_integral, hr, map_one, inv_one]

/-- The genuine finite-idele Dirichlet character is continuous in the original idèle topology. -/
theorem finiteIdeleDirichletCharacter_continuous : Continuous (finiteIdeleDirichletCharacter χ) := by
  apply continuous_of_continuousAt_one
  change Tendsto (finiteIdeleDirichletCharacter χ) (𝓝 1) (𝓝 (finiteIdeleDirichletCharacter χ 1))
  rw [map_one]
  apply tendsto_nhds_of_eventually_eq
  let U : Set (FiniteAdeleRing ℤ ℚ)ˣ := {a | a.val ∈ finiteAdeleIntegerSubring ∧
    a.inv ∈ finiteAdeleIntegerSubring ∧ finiteAdeleLevelMultiple D (a.val - 1)}
  have hU : IsOpen U :=
    (finiteAdeleIntegerSubring_isOpen.preimage Units.continuous_val).inter
      ((finiteAdeleIntegerSubring_isOpen.preimage (Units.continuous_val.comp continuous_inv)).inter
        ((finiteAdeleLevelMultiple_isOpen D).preimage (Units.continuous_val.sub continuous_const)))
  have h1 : (1 : (FiniteAdeleRing ℤ ℚ)ˣ) ∈ U :=
    ⟨finiteAdeleIntegerSubring.one_mem, finiteAdeleIntegerSubring.one_mem,
      ⟨0, finiteAdeleIntegerSubring.zero_mem, by simp⟩⟩
  filter_upwards [hU.mem_nhds h1] with a ha
  exact finiteIdeleDirichletCharacter_congruence_one χ a ha.1 ha.2.1 ha.2.2

end
end Dubon2026
