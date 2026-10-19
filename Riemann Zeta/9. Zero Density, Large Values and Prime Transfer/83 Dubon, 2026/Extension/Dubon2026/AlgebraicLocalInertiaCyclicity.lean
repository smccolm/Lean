import Dubon2026.AlgebraicLocalResidueGaloisContinuity
import Dubon2026.FiniteFieldFrobeniusClosedSubgroup

/-! The same original arithmetic Frobenius generates every finite quotient
by original local inertia. Compactness of the original residue action and
pinned finite-field Frobenius replace a separate finite local field model.
This discharges the cyclicity input to DUB-17's unramified H1 dimension. -/

namespace Dubon2026
noncomputable section

variable (K L : Type) [NontriviallyNormedField K] [NormedField L]
  [NormedAlgebra K L] [IsUltrametricDist K] [IsUltrametricDist L] [CompleteSpace K]
  [IsGalois K L] [Finite (IsLocalRing.ResidueField (algebraicLocalIntegerRing K))]

attribute [local instance] algebraicLocalIntegerAction algebraicLocalIntegerBaseAlgebra
  algebraicLocalIntegerBaseIsLocalHom

/-- The original Frobenius lift generates each original finite inertia quotient. -/
theorem algebraicLocal_frobenius_generates_inertia_quotient
    (φ : Gal(L/K))
    (hφ : ∀ x : algebraicLocalIntegerRing L,
      IsLocalRing.residue _ (φ • x) = (IsLocalRing.residue _ x) ^
        Nat.card (IsLocalRing.ResidueField (algebraicLocalIntegerRing K)))
    (U : OpenNormalSubgroup Gal(L/K))
    (x : Gal(L/K) ⧸ (algebraicLocalInertia K L ⊔ U.toSubgroup)) :
    x ∈ Subgroup.zpowers (QuotientGroup.mk φ) := by
  classical
  let k := IsLocalRing.ResidueField (algebraicLocalIntegerRing K)
  let κ := IsLocalRing.ResidueField (algebraicLocalIntegerRing L)
  letI : Fintype k := Fintype.ofFinite k
  letI : Algebra.IsAlgebraic k κ := algebraicLocalResidue_isAlgebraic K L
  let ψ := algebraicLocalResidueGalois K L
  have hψφ : ψ φ = FiniteField.frobeniusAlgEquivOfAlgebraic k κ := by
    ext y
    obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective y
    change IsLocalRing.residue _ (φ • y) = (IsLocalRing.residue _ y) ^ Fintype.card k
    simpa only [Nat.card_eq_fintype_card] using hφ y
  let N := algebraicLocalInertia K L ⊔ U.toSubgroup
  let π := QuotientGroup.mk' N
  let H := (Subgroup.zpowers (π φ)).comap π
  have hNH : N ≤ H := by
    intro g hg
    change π g ∈ Subgroup.zpowers (π φ)
    have he : π g = 1 := (QuotientGroup.eq_one_iff _).mpr hg
    rw [he]
    exact Subgroup.one_mem _
  have hHopen : IsOpen (H : Set Gal(L/K)) :=
    Subgroup.isOpen_mono (le_sup_right.trans hNH) U.isOpen
  have hHclosed : IsClosed (H : Set Gal(L/K)) := (⟨H, hHopen⟩ : OpenSubgroup Gal(L/K)).isClosed
  have hDclosed : IsClosed (H.map ψ : Set Gal(κ/k)) :=
    (hHclosed.isCompact.image (algebraicLocalResidueGalois_continuous K L)).isClosed
  have hDφ : FiniteField.frobeniusAlgEquivOfAlgebraic k κ ∈ H.map ψ := by
    refine ⟨φ, ?_, hψφ⟩
    exact Subgroup.mem_zpowers (π φ)
  have hDtop := finiteField_closedSubgroup_eq_top_of_frobenius_mem k κ
    (H.map ψ) hDclosed hDφ
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  change g ∈ H
  have hgD : ψ g ∈ H.map ψ := by rw [hDtop]; exact Subgroup.mem_top _
  obtain ⟨h, hh, he⟩ := hgD
  have hhg : h⁻¹ * g ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, he, inv_mul_cancel]
  have hIH : ψ.ker ≤ H := by
    rw [show ψ.ker = algebraicLocalInertia K L from algebraicLocalResidueGalois_ker K L]
    exact le_sup_left.trans hNH
  simpa only [← mul_assoc, mul_inv_cancel, one_mul] using H.mul_mem hh (hIH hhg)

end
end Dubon2026
