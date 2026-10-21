import Dubon2026.SourceCurveOrders
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! DUB-17/18 -> regular differential dimension and local regularity ->
finite residue fields -> restriction to a rational coordinate field.
The restricted place is constructed from the actual valuation-ring preimage.
Pinned cyclic-value-group discreteness supplies its principal ideal ring;
no abstract place or ramification certificate is supplied as a premise.
The integral-closedness argument follows Def_AlgebraicCurve_DivisorPushPull
in anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceCurve.Place
noncomputable section
open IsDedekindDomain WithZero IsLocalRing

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F'] [Algebra F F'] (w : Place K F')

/-- The residue field of the actual discrete valuation ring defining the place. -/
abbrev ResidueField := IsLocalRing.ResidueField w.toValuationSubring

theorem adicValuation_le_one_iff {x : F'} :
    w.adicValuation x ≤ 1 ↔ x ∈ w.toValuationSubring := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rw [w.mem_iff_ord_nonneg, ← WithZero.log_le_log (w.adicValuation_ne_zero hx) one_ne_zero]
  simp [Place.ord]

theorem comap_algebraMap_ne_top [Algebra.IsIntegral F F'] :
    w.toValuationSubring.comap (algebraMap F F') ≠ ⊤ := by
  intro htop
  apply w.ne_top'
  have hF : ∀ f : F, algebraMap F F' f ∈ w.toValuationSubring := fun f =>
    ValuationSubring.mem_comap.mp (htop ▸ ValuationSubring.mem_top f)
  refine SetLike.ext fun x => ⟨fun _ => ValuationSubring.mem_top x, fun _ => ?_⟩
  letI : Algebra F w.toValuationSubring :=
    ((algebraMap F F').codRestrict w.toValuationSubring.toSubring hF).toAlgebra
  letI : IsScalarTower F w.toValuationSubring F' :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hx : IsIntegral w.toValuationSubring x :=
    (Algebra.IsIntegral.isIntegral (R := F) x).tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hx
  exact hy ▸ y.2

theorem isPrincipalIdealRing_comap [Algebra.IsIntegral F F'] :
    IsPrincipalIdealRing (w.toValuationSubring.comap (algebraMap F F')) := by
  let v : Valuation F ℤᵐ⁰ := w.adicValuation.comap (algebraMap F F')
  have he : v.valuationSubring = w.toValuationSubring.comap (algebraMap F F') := by
    ext x
    exact w.adicValuation_le_one_iff
  haveI : v.IsNontrivial := by
    by_contra hn
    apply w.comap_algebraMap_ne_top (F := F)
    rw [← he]
    exact (Valuation.valuationSubring_eq_top_iff (v := v)).mpr hn
  haveI : IsCyclic (MonoidWithZeroHom.valueGroup v) := inferInstance
  rw [← he]
  exact Valuation.valuationSubring_isPrincipalIdealRing v

variable [Algebra K F] [IsScalarTower K F F'] [Algebra.IsIntegral F F']

variable (F) in
/-- Restriction of an actual place along an algebraic field extension. -/
def restrict : Place K F where
  toValuationSubring := w.toValuationSubring.comap (algebraMap F F')
  algebraMap_mem' a := by
    rw [ValuationSubring.mem_comap, ← IsScalarTower.algebraMap_apply]
    exact w.algebraMap_mem' a
  ne_top' := w.comap_algebraMap_ne_top
  isPrincipalIdealRing' := w.isPrincipalIdealRing_comap

@[simp]
theorem restrict_toValuationSubring :
    (w.restrict F).toValuationSubring = w.toValuationSubring.comap (algebraMap F F') := rfl

theorem mem_restrict_iff {f : F} :
    f ∈ (w.restrict F).toValuationSubring ↔ algebraMap F F' f ∈ w.toValuationSubring := Iff.rfl

end
end Dubon2026.SourceCurve.Place
