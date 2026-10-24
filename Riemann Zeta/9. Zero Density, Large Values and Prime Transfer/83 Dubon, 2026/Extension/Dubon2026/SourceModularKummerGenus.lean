import Dubon2026.SourceModularKummerCanonicalDegree
import Dubon2026.SourceModularKummerUnramified
import Dubon2026.SourceCurveUnramifiedCanonicalDegree

/-! DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> all-weight continuation
-> residual association -> original Frobenius/inertia -> Picard torsion
injectivity -> Kummer power lifting. The actual prime Kummer cover of an
arithmetic modular function with prime-divisible divisor has genus
g(E)-1 = q*(g(F)-1). Its degree, unramified local orders, canonical divisors,
residue duality and source H1 genus identification are all proved upstream.
The genus comparison for extending reductions remains necessary. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve Polynomial IntermediateField KaehlerDifferential
local notation "Qbar" => AlgebraicClosure ℚ
variable (N : ℕ) [NeZero N]
local notation "FF" => modularFunctionFieldCoeff N Qbar

theorem modular_kummer_genus_sub_one
    {q : ℕ} [Fact q.Prime] {f : FF} (hf : ∀ g : FF, g ^ q ≠ f)
    (hdvd : ∀ P : Place Qbar FF, (q : ℤ) ∣ P.ord f)
    (E : Type*) [Field E] [Algebra FF E] [Algebra Qbar E] [IsScalarTower Qbar FF E]
    [IsSplittingField FF E (X ^ q - C f)] :
    (genusFF Qbar E : ℤ) - 1 = (q : ℤ) * ((genusFF Qbar FF : ℤ) - 1) := by
  letI : CharZero FF := charZero_of_injective_algebraMap (algebraMap Qbar FF).injective
  letI : FiniteDimensional FF E := IsSplittingField.finiteDimensional E (X ^ q - C f)
  letI hdim : FiniteDimensional Qbar⟮jCoeff N Qbar⟯ FF := finiteDimensional_coeff_field N Qbar
  letI hdimE : FiniteDimensional Qbar⟮algebraMap FF E (jCoeff N Qbar)⟯ E :=
    modular_extension_finite_coordinate N E
  have hDF := D_jCoeff_ne_zero N Qbar
  have hDE := modular_extension_D_j_ne_zero N E
  letI : Nontrivial Ω[FF⁄Qbar] := nontrivial_of_ne _ _ hDF
  letI : Nontrivial Ω[E⁄Qbar] := nontrivial_of_ne _ _ hDE
  letI : HasCanonicalDivisor (K := Qbar) (F := FF) :=
    hasCanonicalDivisor_finite_coordinate (jCoeff N Qbar) (transcendental_jCoeff N Qbar) hDF
  letI : HasCanonicalDivisor (K := Qbar) (F := E) := (modular_extension_curve_and_canonical N E).2
  letI : ∀ v : Place Qbar FF, v.DCoordGenerates := finite_coordinate_place_dCoordGenerates (jCoeff N Qbar)
  letI : ∀ w : Place Qbar E, w.DCoordGenerates :=
    finite_coordinate_place_dCoordGenerates (algebraMap FF E (jCoeff N Qbar))
  letI : ∀ w : Place Qbar E, Module.Finite w.toValuationSubring Ω[w.toValuationSubring⁄Qbar] :=
    finite_coordinate_place_differentials (algebraMap FF E (jCoeff N Qbar))
  letI : ∀ w : Place Qbar E, Module.Finite Qbar w.ResidueField :=
    finite_coordinate_place_residue (algebraMap FF E (jCoeff N Qbar))
  letI : ∀ w : Place Qbar E, Algebra.IsSeparable Qbar w.ResidueField := fun _ => inferInstance
  have hmap : KaehlerDifferential.map Qbar Qbar FF E (D Qbar FF (jCoeff N Qbar)) ≠ 0 := by
    rw [KaehlerDifferential.map_D]
    exact hDE
  obtain ⟨hdegree, he⟩ := modular_kummer_degree_and_unramified N hf hdvd E
  have hcan := canonical_degree_map_of_unramified
    (place_residue_bijective_of_finite_coordinate (jCoeff N Qbar))
    (place_residue_bijective_of_finite_coordinate (algebraMap FF E (jCoeff N Qbar))) he hDF hmap
  have hbase := finite_coordinate_canonical_degree_eq_genusFF (jCoeff N Qbar)
    (transcendental_jCoeff N Qbar) hDF hDF
  have htop := modular_extension_canonical_degree_eq_genusFF N E hmap
  rw [hbase, htop, hdegree] at hcan
  nlinarith

end
end Dubon2026.SourceFunctionField
