import Dubon2026.SourceResidueConjugateEmbedding
import Dubon2026.SourceResiduePrimeRelationCompatibility

/-! DUB-17/18 -> original Frobenius/inertia -> good reduction -> all-level
residue degree -> coprime nonmembership -> lower-level conjugate induction.
The actual full degree-p+1 prime relation is identified with the relative
minimal polynomial under the explicit induction degree. Its literal twisted
branches supply the required roots. The compatible polynomial's adjacent
identities and root list are proved together. Adapted from local SourcePrimeConjugateMinpolyStep;
no rational coefficient field or conditional modular-polynomial input is used. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial IntermediateField PrimeDegreeAux
variable {K : Type*} [Field K]

theorem residue_prime_twisted_minpoly_root_of_full_step_degree
    (p : ℕ) [Fact p.Prime] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) p)
    (F : IntermediateField K (LaurentSeries K)) (σ : F →+* LaurentSeries K)
    (d : ℕ) [NeZero d] (hd : qExpand K d (jqModC K) ∈ F)
    (e : ℕ) [NeZero e] (u : Kˣ)
    (hσd : σ ⟨qExpand K d (jqModC K), hd⟩ = TS K (e * p) (u ^ p))
    (hdeg : (minpoly F (qExpand K (d * p) (jqModC K))).natDegree = p + 1)
    (c : ℕ) (hc : c < p) :
    ((minpoly F (qExpand K (d * p) (jqModC K))).map σ).eval (TS K e (u * ζ ^ c)) = 0 := by
  obtain ⟨R, hRm, hRdeg, hrel, hR⟩ := exists_residue_prime_compatible_relations K p ζ hζ
  let Q := relationAtSeed R (⟨qExpand K d (jqModC K), hd⟩ : F)
  have hQm : Q.Monic := hRm.map _
  have hQdeg : Q.natDegree = p + 1 := (hRm.natDegree_map _).trans hRdeg
  have hQroot : Polynomial.aeval (qExpand K (d * p) (jqModC K)) Q = 0 := by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, relationAtSeed_map]
    exact (hrel d).1
  have hint : IsIntegral F (qExpand K (d * p) (jqModC K)) := ⟨Q, hQm, hQroot⟩
  have he : Q = minpoly F (qExpand K (d * p) (jqModC K)) :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hQm
      (minpoly.dvd F _ hQroot) (by rw [hQdeg, hdeg])
  rw [← he]
  change ((relationAtSeed R (⟨qExpand K d (jqModC K), hd⟩ : F)).map σ).eval _ = 0
  rw [relationAtSeed_map, hσd]
  exact (residue_prime_root_iff_of_root_list p e ζ u R hRm (hR e u).1 _).mpr (Or.inr ⟨c, hc, rfl⟩)

end
end Dubon2026.SourceFunctionField
