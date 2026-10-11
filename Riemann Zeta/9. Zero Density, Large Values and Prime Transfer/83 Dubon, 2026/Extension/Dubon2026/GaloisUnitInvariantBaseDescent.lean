import Dubon2026.FiniteGaloisUnitNormRange

/-! # Original invariant Galois unit coefficients are precisely actual base units -/

namespace Dubon2026
noncomputable section

variable {K L : Type} [Field K] [Field L] [Algebra K L]

/-- The original base-unit coefficient inclusion is injective because the
actual extension-field algebra map is injective. -/
theorem galoisUnitsBaseCoefficient_injective :
    Function.Injective (galoisUnitsBaseCoefficient (K := K) (L := L)) := by
  intro u v huv
  apply Units.ext
  apply (algebraMap K L).injective
  exact congrArg (fun x : Rep.ofAlgebraAutOnUnits K L =>
    ((Additive.toMul (Rep.toAdditive x) : Lˣ) : L)) huv

variable [FiniteDimensional K L] [IsGalois K L]

/-- Actual fixed-field descent recovers an original base-field unit from
each original invariant coefficient. No finiteness of either field as a set
or surjectivity of a field norm is assumed. -/
theorem galoisUnitInvariant_exists_base
    (x : Rep.ofAlgebraAutOnUnits K L)
    (hx : x ∈ (Rep.ofAlgebraAutOnUnits K L).ρ.invariants) :
    ∃ u : Kˣ, galoisUnitsBaseCoefficient (L := L) u = x := by
  let uL : Lˣ := Additive.toMul (Rep.toAdditive x)
  have hfixed : ∀ g : Gal(L/K), g (uL : L) = (uL : L) := by
    intro g
    exact congrArg (fun y : Rep.ofAlgebraAutOnUnits K L =>
      ((Additive.toMul (Rep.toAdditive y) : Lˣ) : L)) (hx g)
  obtain ⟨a, ha⟩ :=
    (IsGalois.mem_range_algebraMap_iff_fixed (F := K) (E := L) (uL : L)).mpr hfixed
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, map_zero] at ha
    exact Units.ne_zero uL ha.symm
  refine ⟨Units.mk0 a ha0, ?_⟩
  change Units.map (algebraMap K L).toMonoidHom (Units.mk0 a ha0) = uL
  apply Units.ext
  exact ha

/-- The original coefficient norm range contains a base coefficient exactly
when that same base-field unit is an actual extension-field norm. -/
theorem galoisUnitsBaseCoefficient_mem_normRange_iff (u : Kˣ) :
    galoisUnitsBaseCoefficient (L := L) u ∈
        LinearMap.range (Rep.ofAlgebraAutOnUnits K L).norm.hom.toLinearMap ↔
      ∃ v : Lˣ, Units.map (Algebra.norm K (S := L)) v = u := by
  constructor
  · rintro ⟨x, hx⟩
    let v : Lˣ := Additive.toMul (Rep.toAdditive x)
    refine ⟨v, ?_⟩
    apply galoisUnitsBaseCoefficient_injective (L := L)
    rw [← galoisUnitsNorm_baseCoefficient]
    exact hx
  · rintro ⟨v, rfl⟩
    exact ⟨Rep.toAdditive.symm (Additive.ofMul v), galoisUnitsNorm_baseCoefficient v⟩

end
end Dubon2026
