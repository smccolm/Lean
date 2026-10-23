import Dubon2026.SourceResidueEmbeddedConjugate

/-! DUB-17/18 -> original Frobenius/inertia -> good reduction -> all-level
residue degree -> coprime nonmembership -> lower-level conjugate induction.
Adapt local SourceOriginalReducedConjugateRoot to the actual coefficient-field j series and divisor field.
The same native minimal-polynomial, tower and primitive-slot arguments are used.
Every lower-level generation, degree and product hypothesis remains explicit;
the all-level consumer must derive them by induction. No new characteristic-zero
structure is imposed on the residue coefficient field. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial IntermediateField ConjugateSlots PrimeDegreeAux
open scoped IntermediateField
variable {K : Type*} [Field K]

theorem residue_reduced_prime_root_of_lower_identity
    (m p a b : ℕ) [NeZero m] [hp : Fact p.Prime] [NeZero a]
    (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) (m * p * p))
    (hs : (⟨a, b⟩ : Σ _ : ℕ, ℕ) ∈ indices (m * p * p))
    (hpa : p ∣ (m * p * p) / a)
    (σ : modularFunctionFieldCoeff (m * p) K →+* LaurentSeries K)
    (hbase : ∀ (z : K⟮(jqModC K)⟯) (hz : (z : LaurentSeries K) ∈ modularFunctionFieldCoeff (m * p) K),
      σ ⟨z, hz⟩ = (qExpand K (m * p * p) (z : LaurentSeries K)))
    (η : Kˣ) (hη : IsPrimitiveRoot (η : K) p) (u : Kˣ) (c : ℕ) (hc : c < p)
    (hseed : σ ⟨qExpand K (m * p) (jqModC K), jqd_mem_coeff_field (m * p) K dvd_rfl⟩ =
      TS K (a * a * p) (u ^ p))
    (hbranch : TS K (a * a) (u * η ^ c) = slotValue ζ a b)
    (hdeg : (minpoly (modularFunctionFieldCoeff (m * p) K)
      (qExpand K (m * p * p) (jqModC K))).natDegree = p)
    (hprev : residueExpandedJMinpoly K m m = slotProduct m (ζ ^ (p * p))) :
    (residueExpandedJMinpoly K (m * p * p) (m * p * p)).IsRoot (slotValue ζ a b) := by
  have hmem := jqd_mem_coeff_field (m * p) K (dvd_mul_right m p)
  have hr := residue_expanded_minpoly_root_of_member (modularFunctionFieldCoeff (m * p) K)
    (jq_mem_coeff_field _ K) σ (m * p * p) m hbase hmem
  have he : m * p * p = (p * p) * m := by ring
  have hr' : (residueExpandedJMinpoly K ((p * p) * m) m).IsRoot
      (σ ⟨qExpand K m (jqModC K), hmem⟩) := by simpa only [he] using hr
  obtain ⟨s, hs', hshape⟩ := residue_expanded_minpoly_root_shape_of_identity
    (p * p) m (ζ ^ (p * p)) hprev _ hr'
  have hne : TS K (a * a) (u * η ^ c) ≠ σ ⟨qExpand K m (jqModC K), hmem⟩ := by
    rw [hbranch, hshape]
    exact slotValue_ne_prime_square_expansion hp.out he ζ hζ hs hs' hpa
  have hroot := residue_prime_twisted_minpoly_root_of_reduced_step_degree p η hη
    (modularFunctionFieldCoeff (m * p) K) σ m hmem (jqd_mem_coeff_field (m * p) K dvd_rfl)
    (a * a) u hseed hdeg c hc hne
  rw [hbranch] at hroot
  exact residue_expanded_minpoly_root_of_relative_root (modularFunctionFieldCoeff (m * p) K)
    (jq_mem_coeff_field _ K) σ (m * p * p) (m * p * p) hbase _ hroot

end
end Dubon2026.SourceFunctionField
