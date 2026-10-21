import Dubon2026.SourceCurveChartOrders
import Dubon2026.SourceCurveLocalDifferentials

/-! DUB-17/18 -> actual regular differential dimension -> global residue
identity -> finite-extension trace comparison. Galois averaging requires
the action of field automorphisms on the actual places, with their exact
normalized orders. These constructions transport the literal valuation
subrings, and reuse the proved uniqueness of normalized discrete order.
No differential-residue invariance or global trace identity is assumed.
-/
namespace Dubon2026.SourceCurve.Place
noncomputable section
variable {K F E : Type*} [Field K] [Field F] [Field E]
variable [Algebra K F] [Algebra K E]

/-- The literal valuation rings are isomorphic under a field equivalence. -/
def valuationRingComapEquiv (w : Place K E) (e : F ≃ₐ[K] E) :
    w.toValuationSubring.comap e.toRingHom ≃+* w.toValuationSubring where
  toFun x := ⟨e x, x.2⟩
  invFun y := ⟨e.symm y, by
    change e (e.symm y) ∈ w.toValuationSubring
    simpa only [e.apply_symm_apply] using y.2⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv y := Subtype.ext (e.apply_symm_apply y)
  map_mul' x y := Subtype.ext (map_mul e (x : F) (y : F))
  map_add' x y := Subtype.ext (map_add e (x : F) (y : F))

/-- Pullback of a genuine place along an equivalence of constant fields. -/
def comapEquiv (w : Place K E) (e : F ≃ₐ[K] E) : Place K F where
  toValuationSubring := w.toValuationSubring.comap e.toRingHom
  algebraMap_mem' a := by
    change e (algebraMap K F a) ∈ w.toValuationSubring
    rw [e.commutes]
    exact w.algebraMap_mem' a
  ne_top' := by
    intro h
    apply w.ne_top'
    apply SetLike.ext
    intro y
    constructor
    · intro _
      exact ValuationSubring.mem_top y
    · intro _
      have hx : e.symm y ∈ w.toValuationSubring.comap e.toRingHom :=
        h ▸ ValuationSubring.mem_top _
      change e (e.symm y) ∈ w.toValuationSubring at hx
      simpa only [e.apply_symm_apply] using hx
  isPrincipalIdealRing' :=
    IsPrincipalIdealRing.of_surjective (w.valuationRingComapEquiv e).symm
      (w.valuationRingComapEquiv e).symm.surjective

theorem mem_comapEquiv_iff (w : Place K E) (e : F ≃ₐ[K] E) (f : F) :
    f ∈ (w.comapEquiv e).toValuationSubring ↔ e f ∈ w.toValuationSubring := Iff.rfl

theorem ord_comapEquiv (w : Place K E) (e : F ≃ₐ[K] E) (f : F) :
    (w.comapEquiv e).ord f = w.ord (e f) := by
  rcases eq_or_ne f 0 with rfl | hf
  · rw [map_zero, (w.comapEquiv e).ord_zero, w.ord_zero]
  symm
  apply (w.comapEquiv e).eq_ord_of_addHom_of_nonneg_iff (fun x => w.ord (e x))
  · intro x y hx hy
    rw [map_mul, w.ord_mul (by simpa using hx) (by simpa using hy)]
  · refine ⟨e.symm w.uniformizer, ?_, ?_⟩
    · simpa only [map_zero] using e.symm.injective.ne w.uniformizer_ne_zero
    · rw [e.apply_symm_apply, w.ord_uniformizer]
  · intro x _
    exact w.mem_iff_ord_nonneg.symm
  · exact hf

/-- The exact bijection of places induced by a constant-preserving field equivalence. -/
def placeEquiv (e : F ≃ₐ[K] E) : Place K E ≃ Place K F where
  toFun w := w.comapEquiv e
  invFun v := v.comapEquiv e.symm
  left_inv w := by
    apply Place.ext
    ext x
    change e (e.symm x) ∈ w.toValuationSubring ↔ x ∈ w.toValuationSubring
    rw [e.apply_symm_apply]
  right_inv v := by
    apply Place.ext
    ext x
    change e.symm (e x) ∈ v.toValuationSubring ↔ x ∈ v.toValuationSubring
    rw [e.symm_apply_apply]

end
end Dubon2026.SourceCurve.Place
