import Dubon2026.SourceGammaOneExtendedPlaceMap
import Dubon2026.SourceCurvePicardGroup
import Dubon2026.SourceCurveDivisorDegree

/-! DUB17/18 -> original all-weight arithmetic realization -> actual Gamma1
arithmetic/complex Picard torsion comparison -> actual
divisor conorm. The unique original place extension pushes forward finite
divisors injectively on their supports. Proved residue-field identifications
preserve degree, and exact orders both on and off the image preserve actual
principal divisors. Descent and injectivity on Picard groups remain separate.
Adapted from S_ModularCurve_exists_injective_heckeEquivariant_addMonoidHom_jZero_pic0_complex,
anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2, divisor-conorm section.
-/
namespace Dubon2026.SourceFunctionField.GammaOne.ConstantField
noncomputable section
open SourceCurve CongruenceSubgroup
local notation "Qbar" => AlgebraicClosure ℚ
variable (N : ℕ) [NeZero N]
local notation "FQ" => functionFieldOver (Gamma1 N) Qbar
local notation "FC" => functionFieldOver (Gamma1 N) ℂ

/-- Pushforward along the actual extension of arithmetic places to complex places. -/
def conorm : Divisor Qbar FQ →+ Divisor ℂ FC :=
  Finsupp.mapDomain.addMonoidHom (liftPlace N)

theorem conorm_apply_liftPlace (D : Divisor Qbar FQ) (v : Place Qbar FQ) :
    conorm N D (liftPlace N v) = D v :=
  Finsupp.mapDomain_apply (liftPlace_injective N) D v

theorem conorm_apply_of_forall_ne (D : Divisor Qbar FQ) {w : Place ℂ FC}
    (h : ∀ v, w ≠ liftPlace N v) : conorm N D w = 0 :=
  Finsupp.mapDomain_notin_range D w (by rintro ⟨v, rfl⟩; exact h v rfl)

theorem conorm_single (v : Place Qbar FQ) (n : ℤ) :
    conorm N (Finsupp.single v n) = Finsupp.single (liftPlace N v) n :=
  Finsupp.mapDomain_single

theorem degree_conorm (D : Divisor Qbar FQ) :
    Divisor.degree (conorm N D) = Divisor.degree D := by
  have hQ (v : Place Qbar FQ) : Module.finrank Qbar v.ResidueField = 1 :=
    Module.finrank_of_bijective_algebraMap (gamma1_place_residue_bijective Qbar N v)
  have hC (v : Place ℂ FC) : Module.finrank ℂ v.ResidueField = 1 :=
    Module.finrank_of_bijective_algebraMap (gamma1_place_residue_bijective ℂ N v)
  induction D using Finsupp.induction with
  | zero => rw [map_zero, map_zero, map_zero]
  | single_add v n D _ _ ih =>
    rw [map_add, map_add, map_add, ih, conorm_single,
      Divisor.degree_single, Divisor.degree_single, hC, hQ]

theorem isPrincipal_conorm {D : Divisor Qbar FQ} (hD : Divisor.IsPrincipal D) :
    Divisor.IsPrincipal (conorm N D) := by
  classical
  obtain ⟨f, hf, hDf⟩ := hD
  refine ⟨fieldMap N f, (map_ne_zero _).mpr hf, fun w => ?_⟩
  by_cases h : ∃ v, w = liftPlace N v
  · obtain ⟨v, rfl⟩ := h
    rw [conorm_apply_liftPlace, ord_liftPlace, hDf]
  · push Not at h
    rw [conorm_apply_of_forall_ne N D h, ord_phi_of_forall_ne N h]

end
end Dubon2026.SourceFunctionField.GammaOne.ConstantField
