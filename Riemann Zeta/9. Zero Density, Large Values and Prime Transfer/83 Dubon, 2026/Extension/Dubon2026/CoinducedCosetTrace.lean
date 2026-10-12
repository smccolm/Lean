import Dubon2026.CoinducedCosetValues
import Mathlib.GroupTheory.Coset.Card

/-! # The actual finite coset trace on original coinduced coefficients -/

namespace Dubon2026
noncomputable section

open CategoryTheory
open scoped BigOperators

variable {k G : Type} [CommRing k] [Group G] (A : Rep k G) (S : Subgroup G)
  [Fintype (G ⧸ S)]

/-- Sum the actual untwisted coefficient values over genuine subgroup cosets. -/
def coinducedCosetTraceLinear : Rep.coind S.subtype (Rep.res S.subtype A) →ₗ[k] A where
  toFun f := ∑ q : G ⧸ S, coinducedCosetValues A S f q
  map_add' f g := by simp only [map_add, Pi.add_apply, Finset.sum_add_distrib]
  map_smul' r f := by simp only [map_smul, Pi.smul_apply, Finset.smul_sum, RingHom.id_apply]

/-- The actual finite coset sum intertwines the original Galois-type
actions. The proof reindexes the literal cosets by their genuine group action. -/
def coinducedCosetTrace : Rep.coind S.subtype (Rep.res S.subtype A) ⟶ A :=
  Rep.ofHom ⟨coinducedCosetTraceLinear A S, by
    intro h
    apply LinearMap.ext
    intro f
    change (∑ q : G ⧸ S,
      coinducedCosetValues A S ((Rep.coind S.subtype (Rep.res S.subtype A)).ρ h f) q) =
        A.ρ h (∑ q : G ⧸ S, coinducedCosetValues A S f q)
    calc
      _ = ∑ q : G ⧸ S, A.ρ h (coinducedCosetValues A S f (h⁻¹ • q)) :=
        Finset.sum_congr rfl (fun q _ => coinducedCosetValues_action A S f h q)
      _ = _ := by
        rw [map_sum]
        exact Equiv.sum_comp (MulAction.toPerm h⁻¹)
          (fun q : G ⧸ S => A.ρ h (coinducedCosetValues A S f q))⟩

/-- The original restriction-coinduction unit followed by the actual trace
is multiplication by the exact number of subgroup cosets. -/
theorem coinducedCosetTrace_unit_apply (x : A) :
    (coinducedCosetTrace A S).hom
      ((Rep.resCoindToHom S.subtype A (Rep.res S.subtype A) (𝟙 _)).hom x) =
        Fintype.card (G ⧸ S) • x := by
  change (∑ q : G ⧸ S, coinducedCosetValues A S
    ((Rep.resCoindToHom S.subtype A (Rep.res S.subtype A) (𝟙 _)).hom x) q) = _
  have hterm : ∀ q : G ⧸ S, coinducedCosetValues A S
      ((Rep.resCoindToHom S.subtype A (Rep.res S.subtype A) (𝟙 _)).hom x) q = x := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H g =>
      change A.ρ g (A.ρ g⁻¹ x) = x
      exact Representation.self_inv_apply A.ρ g x
  simp only [hterm, Finset.sum_const, Finset.card_univ]

/-- The coefficient-map composition is the exact coset-cardinality
multiple of the original identity morphism. -/
theorem coinducedCosetTrace_comp_unit :
    Rep.resCoindToHom S.subtype A (Rep.res S.subtype A) (𝟙 _) ≫
      coinducedCosetTrace A S = Fintype.card (G ⧸ S) • 𝟙 A := by
  apply Rep.hom_ext
  ext x
  exact coinducedCosetTrace_unit_apply A S x

end
end Dubon2026
