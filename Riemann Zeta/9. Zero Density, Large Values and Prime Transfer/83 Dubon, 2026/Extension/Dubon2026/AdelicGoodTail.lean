import Dubon2026.AdelicGoodBaseProjection
import Dubon2026.AdelicRestrictedFiniteOrbitCoverage

/-! # Actual good-place tails outside finite tensor stages -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

variable (N : ℕ) {n : ℕ} (v : Fin n → HeightOneSpectrum ℤ) (hv : Function.Injective v)

/-- Remove the selected genuine coordinates from the original matrix's actual good-place component. -/
def adelicGoodTail (a : RationalAdelicGL2) : RationalAdelicGL2 :=
  adelicFinitePlaceRemoval v hv (adelicGoodPartHom N a)

/-- The genuine good-place tail has identity at each selected original place. -/
theorem adelicGoodTail_same (a : RationalAdelicGL2) (i : Fin n) :
    adelicPlaceGL2Hom (v i) (adelicGoodTail N v hv a) = 1 :=
  adelicFinitePlaceRemoval_same v hv i (adelicGoodPartHom N a)

/-- The genuine good-place tail has identity real coordinate. -/
theorem adelicGoodTail_real (a : RationalAdelicGL2) :
    (rationalAdelicGL2RealFiniteEquiv (adelicGoodTail N v hv a)).1 = 1 := by
  rw [adelicGoodTail, adelicFinitePlaceRemoval_real, adelicGoodPartHom_coordinates]

/-- At an unselected good place, the actual tail retains the literal original coordinate. -/
theorem adelicGoodTail_good (a : RationalAdelicGL2) (w : HeightOneSpectrum ℤ)
    (hw : IsGoodAdelicPlace N w) (hout : ∀ i, w ≠ v i) :
    adelicPlaceGL2Hom w (adelicGoodTail N v hv a) = adelicPlaceGL2Hom w a := by
  rw [adelicGoodTail, adelicFinitePlaceRemoval_ne v hv w hout, adelicGoodPartHom_good N a w hw]

/-- The actual tail retains identity at every original bad place. -/
theorem adelicGoodTail_bad (hgood : ∀ i, IsGoodAdelicPlace N (v i)) (a : RationalAdelicGL2)
    (w : HeightOneSpectrum ℤ) (hw : ¬ IsGoodAdelicPlace N w) :
    adelicPlaceGL2Hom w (adelicGoodTail N v hv a) = 1 := by
  have hout : ∀ i, w ≠ v i := by
    intro i he
    apply hw
    exact he.symm ▸ hgood i
  rw [adelicGoodTail, adelicFinitePlaceRemoval_ne v hv w hout, adelicGoodPartHom_bad N a w hw]

/-- The genuine tail commutes with every actual fixed-base matrix. -/
theorem adelicGoodTail_base_commute (hgood : ∀ i, IsGoodAdelicPlace N (v i))
    (a : RationalAdelicGL2) (b : adelicRestrictedBaseGroup N) : Commute (adelicGoodTail N v hv a) b.val :=
  adelicGoodSupported_base_commute N _ (adelicGoodTail_real N v hv a)
    (adelicGoodTail_bad N v hv hgood a) b

/-- Every original matrix factors into its actual finite coordinates, canonical fixed base, and genuine good tail. -/
theorem adelicFiniteProduct_base_tail (hgood : ∀ i, IsGoodAdelicPlace N (v i)) (a : RationalAdelicGL2) :
    (adelicFinitePlaceProduct v hv (fun i => adelicPlaceGL2Hom (v i) a) * (adelicBaseProjection N a).val) *
      adelicGoodTail N v hv a = a := by
  have hcoords : (fun i => adelicPlaceGL2Hom (v i) (adelicGoodPartHom N a)) =
      fun i => adelicPlaceGL2Hom (v i) a := by
    funext i
    exact adelicGoodPartHom_good N a (v i) (hgood i)
  have hfactor := adelicFinitePlaceProduct_mul_removal v hv (adelicGoodPartHom N a)
  rw [hcoords] at hfactor
  change adelicFinitePlaceProduct v hv (fun i => adelicPlaceGL2Hom (v i) a) * adelicGoodTail N v hv a =
    adelicGoodPartHom N a at hfactor
  rw [mul_assoc, ← (adelicGoodTail_base_commute N v hv hgood a (adelicBaseProjection N a)).eq,
    ← mul_assoc, hfactor]
  exact adelicGoodPart_mul_base N a

/-- If all unselected good coordinates lie in original local level, the actual tail lies in genuine finite adelic level. -/
theorem adelicGoodTail_finite_level [NeZero N] (hgood : ∀ i, IsGoodAdelicPlace N (v i))
    (a : RationalAdelicGL2)
    (ha : ∀ w, IsGoodAdelicPlace N w → (∀ i, w ≠ v i) → adelicPlaceGL2Hom w a ∈ finitePlaceGL2Gamma0 N w) :
    (rationalAdelicGL2RealFiniteEquiv (adelicGoodTail N v hv a)).2 ∈ finiteAdeleGL2Gamma0 N := by
  classical
  apply (finiteAdeleGL2Gamma0_iff_places N _).mpr
  intro w
  change adelicPlaceGL2Hom w (adelicGoodTail N v hv a) ∈ _
  by_cases hin : ∃ i, v i = w
  · obtain ⟨i, rfl⟩ := hin
    rw [adelicGoodTail_same]
    exact (finitePlaceGL2Gamma0 N _).one_mem
  · have hout : ∀ i, w ≠ v i := fun i he => hin ⟨i, he.symm⟩
    by_cases hw : IsGoodAdelicPlace N w
    · rw [adelicGoodTail_good N v hv a w hw hout]
      exact ha w hw hout
    · rw [adelicGoodTail_bad N v hv hgood a w hw]
      exact (finitePlaceGL2Gamma0 N _).one_mem

/-- A genuine original good tail with local-level coordinates fixes the actual normalized cusp reference. -/
theorem adelicGoodTail_unitReference [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (hgood : ∀ i, IsGoodAdelicPlace N (v i))
    (a : RationalAdelicGL2)
    (ha : ∀ w, IsGoodAdelicPlace N w → (∀ i, w ≠ v i) → adelicPlaceGL2Hom w a ∈ finitePlaceGL2Gamma0 N w) :
    adelicCyclicHilbertRepresentation f (adelicGoodTail N v hv a) (adelicCyclicUnitReference f) =
      adelicCyclicUnitReference f := by
  let u : finiteAdeleGL2Gamma0 N := ⟨(rationalAdelicGL2RealFiniteEquiv (adelicGoodTail N v hv a)).2,
    adelicGoodTail_finite_level N v hv hgood a ha⟩
  have he : adelicGoodTail N v hv a = rationalAdelicFiniteGL2Embedding u.val := by
    apply rationalAdelicGL2RealFiniteEquiv.injective
    rw [rationalAdelicFiniteGL2Embedding_coordinates]
    exact Prod.ext (adelicGoodTail_real N v hv a) rfl
  rw [he]
  exact adelicCyclicUnitReference_finite_level f u

end
end Dubon2026
