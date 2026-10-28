import Dubon2026.SourceGammaOneHeckeValuationExtension
import Dubon2026.SourceConstantFieldExtensionOrders
import Dubon2026.SourceCurveFiniteCoordinateValuations
import Dubon2026.SourceGammaOneResidues

/-! DUB17/18 -> actual arithmetic Gamma1 Tate/Hecke comparison ->
conorm naturality on the Hecke intersection curve. The same native
valuation-domination and exact-order theorems give unique complex
extensions of its arithmetic places. Functions from the arithmetic
intersection field have order zero outside the lifted-place image.
No Picard or torsion theory of the intersection curve is introduced. -/
namespace Dubon2026.SourceFunctionField.GammaOne.HeckeConstantField
noncomputable section
open SourceCurve CongruenceSubgroup
local notation "Qbar" => AlgebraicClosure ℚ
variable (M d : ℕ) [NeZero M] [NeZero d]
local notation "FQ" => functionFieldOver (Gamma1 M ⊓ Gamma0 (d * M)) Qbar
local notation "FC" => functionFieldOver (Gamma1 M ⊓ Gamma0 (d * M)) ℂ
attribute [local instance] complexAlgebra fieldAlgebra complexFieldAlgebra
  complexScalarTower arithmeticFieldScalarTower

theorem exists_extended_place (P : Place Qbar FQ) :
    ∃ Q : Place ℂ FC,
      Q.toValuationSubring.comap (fieldMap M d) = P.toValuationSubring ∧
      (∀ f : FQ, Q.ord (fieldMap M d f) = P.ord f) ∧
      ∀ Q' : Place ℂ FC,
        Q'.toValuationSubring.comap (fieldMap M d) = P.toValuationSubring → Q' = Q := by
  obtain ⟨V, hV, hC, hP⟩ := exists_extending_valuation M d P
  letI := finiteDimensional_jCoordinateOver (Γ := Gamma1 M ⊓ Gamma0 (d * M))
    (by constructor <;> simp [Gamma1_mem, Gamma0_mem, ModularGroup.T]) ℂ
  obtain ⟨Q, hQ⟩ := SourceCurve.ConstantField.exists_place_of_finite_coordinate
    (jCoordinateOver (Gamma1 M ⊓ Gamma0 (d * M)) ℂ) (transcendental_jCoordinateOver (Gamma1 M ⊓ Gamma0 (d * M)) ℂ) V hC hV
  have hover : Q.toValuationSubring.comap (fieldMap M d) = P.toValuationSubring := by
    rw [hQ]
    exact hP
  letI : Module.Finite Qbar P.ResidueField :=
    Module.Finite.of_surjective (Algebra.linearMap Qbar P.ResidueField)
      (gamma1_hecke_place_residue_bijective Qbar M (d * M) P).surjective
  obtain ⟨hord, huniq⟩ := SourceCurve.ConstantField.extension_order_and_unique FC P
    (adjoin_range_fieldMap M d)
  exact ⟨Q, hover, hord Q hover, fun Q' hQ' => huniq Q' Q hQ' hover⟩


/-- The unique original complex place above the specified arithmetic place. -/
def liftPlace (v : Place Qbar FQ) : Place ℂ FC := (exists_extended_place M d v).choose

theorem liftPlace_comap (v : Place Qbar FQ) :
    (liftPlace M d v).toValuationSubring.comap (fieldMap M d) = v.toValuationSubring :=
  (exists_extended_place M d v).choose_spec.1

theorem ord_liftPlace (v : Place Qbar FQ) (f : FQ) :
    (liftPlace M d v).ord (fieldMap M d f) = v.ord f :=
  (exists_extended_place M d v).choose_spec.2.1 f

theorem liftPlace_unique {v : Place Qbar FQ} {Q' : Place ℂ FC}
    (h : Q'.toValuationSubring.comap (fieldMap M d) = v.toValuationSubring) : Q' = liftPlace M d v :=
  (exists_extended_place M d v).choose_spec.2.2 Q' h

theorem liftPlace_injective : Function.Injective (liftPlace M d) := fun v w h =>
  Place.ext (by rw [← liftPlace_comap M d v, ← liftPlace_comap M d w, h])

theorem exists_eq_liftPlace {w' : Place ℂ FC}
    (hwx : ∃ y : FQ, fieldMap M d y ∉ w'.toValuationSubring) : ∃ v, w' = liftPlace M d v := by
  letI := finiteDimensional_jCoordinateOver (Γ := Gamma1 M ⊓ Gamma0 (d * M))
    (by constructor <;> simp [Gamma1_mem, Gamma0_mem, ModularGroup.T]) Qbar
  have hV : w'.toValuationSubring.comap (fieldMap M d) ≠ ⊤ := by
    intro h
    obtain ⟨y, hy⟩ := hwx
    exact hy (show y ∈ w'.toValuationSubring.comap (fieldMap M d) from
      h ▸ ValuationSubring.mem_top y)
  obtain ⟨v, hv⟩ := SourceCurve.ConstantField.exists_place_of_finite_coordinate
    (jCoordinateOver (Gamma1 M ⊓ Gamma0 (d * M)) Qbar) (transcendental_jCoordinateOver (Gamma1 M ⊓ Gamma0 (d * M)) Qbar) (w'.toValuationSubring.comap (fieldMap M d))
    (fun a => by
      change fieldMap M d (algebraMap Qbar FQ a) ∈ w'.toValuationSubring
      rw [fieldMap_constants]
      exact w'.algebraMap_mem' _) hV
  exact ⟨v, liftPlace_unique M d hv.symm⟩

theorem ord_phi_of_forall_ne {w' : Place ℂ FC} (hoff : ∀ v, w' ≠ liftPlace M d v)
    (f : FQ) : w'.ord (fieldMap M d f) = 0 := by
  have hall : ∀ y : FQ, fieldMap M d y ∈ w'.toValuationSubring := by
    by_contra h
    push Not at h
    obtain ⟨v, hv⟩ := exists_eq_liftPlace M d h
    exact hoff v hv
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  exact SourceCurve.ConstantField.ord_eq_zero_of_mem_of_inv_mem w' (hall f) (by rw [← map_inv₀]; exact hall f⁻¹)

end
end Dubon2026.SourceFunctionField.GammaOne.HeckeConstantField
