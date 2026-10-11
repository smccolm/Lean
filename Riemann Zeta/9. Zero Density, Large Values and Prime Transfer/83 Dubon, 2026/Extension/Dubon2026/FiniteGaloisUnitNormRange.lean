import Dubon2026.FiniteGaloisCharacterRadicals
import Mathlib.FieldTheory.Finite.GaloisField

/-! # The original finite-field Galois unit representation and its actual norm range -/

namespace Dubon2026
noncomputable section

variable {K L : Type} [Field K] [Field L] [Algebra K L]

/-- The original base-field unit as a coefficient in the pinned Galois unit
representation, through the actual algebra map and original additive tag. -/
def galoisUnitsBaseCoefficient (u : Kˣ) : Rep.ofAlgebraAutOnUnits K L :=
  Rep.toAdditive.symm (Additive.ofMul (Units.map (algebraMap K L).toMonoidHom u))

/-- Every original base-field unit coefficient is fixed by the actual Galois action. -/
theorem galoisUnitsBaseCoefficient_fixed (u : Kˣ) (g : Gal(L/K)) :
    (Rep.ofAlgebraAutOnUnits K L).ρ g (galoisUnitsBaseCoefficient u) =
      galoisUnitsBaseCoefficient u := by
  change g • Units.map (algebraMap K L).toMonoidHom u =
    Units.map (algebraMap K L).toMonoidHom u
  exact galois_base_unit_fixed g u

variable [FiniteDimensional K L] [IsGalois K L]

/-- The norm in the pinned original Galois unit representation is exactly the
base coefficient of the actual extension-field unit norm. -/
theorem galoisUnitsNorm_baseCoefficient (u : Lˣ) :
    (Rep.ofAlgebraAutOnUnits K L).norm.hom (Rep.toAdditive.symm (Additive.ofMul u)) =
      galoisUnitsBaseCoefficient (Units.map (Algebra.norm K (S := L)) u) := by
  change (Additive.toMul (Rep.toAdditive
    ((Rep.ofAlgebraAutOnUnits K L).norm.hom (Rep.toAdditive.symm (Additive.ofMul u))))) =
      Units.map (algebraMap K L).toMonoidHom (Units.map (Algebra.norm K (S := L)) u)
  apply Units.ext
  exact groupCohomology.norm_ofAlgebraAutOnUnits_eq u

/-- Surjectivity of the actual finite-field unit norm places every original
base unit coefficient in the range of the original representation norm. -/
theorem galoisUnitsBaseCoefficient_mem_normRange [Finite L] (u : Kˣ) :
    galoisUnitsBaseCoefficient (L := L) u ∈
      LinearMap.range (Rep.ofAlgebraAutOnUnits K L).norm.hom.toLinearMap := by
  obtain ⟨v, hv⟩ := FiniteField.unitsMap_norm_surjective K L u
  refine ⟨Rep.toAdditive.symm (Additive.ofMul v), ?_⟩
  change (Rep.ofAlgebraAutOnUnits K L).norm.hom _ = _
  rw [galoisUnitsNorm_baseCoefficient, hv]

/-- For the genuine finite-field Galois unit representation, every invariant
coefficient is an actual norm: fixed-field descent gives its original base unit,
and the pinned finite-field norm theorem supplies an original extension unit. -/
theorem finiteFieldGaloisUnit_invariant_mem_normRange [Finite L]
    (x : Rep.ofAlgebraAutOnUnits K L)
    (hx : x ∈ (Rep.ofAlgebraAutOnUnits K L).ρ.invariants) :
    x ∈ LinearMap.range (Rep.ofAlgebraAutOnUnits K L).norm.hom.toLinearMap := by
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
  let uK : Kˣ := Units.mk0 a ha0
  have he : galoisUnitsBaseCoefficient (L := L) uK = x := by
    change Units.map (algebraMap K L).toMonoidHom uK = uL
    apply Units.ext
    exact ha
  rw [← he]
  exact galoisUnitsBaseCoefficient_mem_normRange uK

end
end Dubon2026
