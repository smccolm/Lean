import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.Valuation.Integral

/-! # Actual monic residue-extension polynomials and their integral lifts -/

namespace Dubon2026
noncomputable section

open Polynomial
open scoped ValuativeRel

/-- An actual primitive element in the genuine finite-field extension gives a
monic, irreducible, separable polynomial of every prescribed positive degree. -/
theorem finiteField_exists_monic_irreducible_separable_polynomial
    (k : Type) [Field k] [Finite k] (n : ℕ) [NeZero n] :
    ∃ f : k[X], f.Monic ∧ Irreducible f ∧ f.Separable ∧ f.natDegree = n := by
  haveI : Fact (ringChar k).Prime := ⟨CharP.char_is_prime k _⟩
  let l := FiniteField.Extension k (ringChar k) n
  let b : PowerBasis k l := Field.powerBasisOfFiniteOfSeparable k l
  refine ⟨minpoly k b.gen, minpoly.monic b.isIntegral_gen,
    minpoly.irreducible b.isIntegral_gen, Algebra.IsSeparable.isSeparable k b.gen, ?_⟩
  exact b.natDegree_minpoly.trans
    (b.finrank.symm.trans (FiniteField.finrank_extension k (ringChar k) n))

/-- The actual integer ring of the original local field has a monic polynomial
whose original residue polynomial is irreducible and separable of degree `n`.
Its image in the original fraction field is also irreducible. This constructs
the polynomial data, not yet an unramified local-field extension. -/
theorem localField_exists_integral_residue_extension_polynomial
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ) [NeZero n] :
    ∃ F : 𝒪[K][X], F.Monic ∧ F.natDegree = n ∧
      (F.map (IsLocalRing.residue 𝒪[K])).natDegree = n ∧
      Irreducible (F.map (IsLocalRing.residue 𝒪[K])) ∧
      (F.map (IsLocalRing.residue 𝒪[K])).Separable ∧
      Irreducible (F.map (algebraMap 𝒪[K] K)) := by
  obtain ⟨f, hfm, hfi, hfs, hfn⟩ :=
    finiteField_exists_monic_irreducible_separable_polynomial 𝓀[K] n
  obtain ⟨F, hFf, hFd, hFm⟩ := Polynomial.lifts_and_degree_eq_and_monic
    (Polynomial.mem_lifts_of_surjective (IsLocalRing.residue_surjective) f) hfm
  have hFi : Irreducible F := Polynomial.Monic.irreducible_of_irreducible_map
    (IsLocalRing.residue 𝒪[K]) F hFm (hFf.symm ▸ hfi)
  refine ⟨F, hFm, (Polynomial.natDegree_eq_natDegree hFd).trans hfn,
    hFf.symm ▸ hfn, hFf.symm ▸ hfi, hFf.symm ▸ hfs, ?_⟩
  exact (hFm.irreducible_iff_irreducible_map_fraction_map (K := K)).mp hFi

end
end Dubon2026
