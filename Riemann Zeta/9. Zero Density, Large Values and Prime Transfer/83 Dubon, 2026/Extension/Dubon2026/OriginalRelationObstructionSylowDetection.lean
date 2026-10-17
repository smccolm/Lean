import Dubon2026.OriginalRelationPrimeInvariantPairing
import Dubon2026.SubgroupCohomologyCoprimeDetection
import Dubon2026.OriginalCohomologyRestrictionTrace

/-! # Detect the actual prime-annihilated relation obstruction on one Sylow group

DUB-17's scalar criterion only uses obstructions killed by its coefficient
prime. The existing coprime-index trace therefore reduces zero detection to
that prime's Sylow subgroup, even when the full finite stage has mixed degree.
This avoids requiring a normalized class system at every mixed-degree stage.
The comparison with the actual local invariant sum remains to be proved.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
variable {G : Type} [Group G] (B C : Rep ℤ G)

/-- The literal relation obstruction inherits the prime annihilator of
its original H1 coefficient. -/
theorem originalRelationExtensionObstruction_nsmul_zero
    (p : ℕ) (hB : ∀ b : B, p • b = 0)
    (φ : originalRelationModule B ⟶ C) (y : groupCohomology B 1) :
    p • (originalRelationExtensionObstruction B C φ).hom y = 0 := by
  rw [← map_nsmul, originalH1_nsmul_zero B p hB y, map_zero]

/-- The same original obstruction vanishes exactly when its literal
restriction to the coefficient prime's Sylow subgroup vanishes. -/
theorem originalRelationExtensionObstruction_eq_zero_iff_sylow [Finite G]
    (p : ℕ) [Fact p.Prime] (hB : ∀ b : B, p • b = 0) (S : Sylow p G)
    (φ : originalRelationModule B ⟶ C) (y : groupCohomology B 1) :
    (originalRelationExtensionObstruction B C φ).hom y = 0 ↔
      (groupCohomology.map (S : Subgroup G).subtype
        (𝟙 (Rep.res (S : Subgroup G).subtype C)) 2).hom
          ((originalRelationExtensionObstruction B C φ).hom y) = 0 := by
  constructor
  · intro h
    rw [h, map_zero]
  · intro h
    letI : Fintype (G ⧸ (S : Subgroup G)) := Fintype.ofFinite _
    have hp : p.Coprime (Fintype.card (G ⧸ (S : Subgroup G))) := by
      simpa only [Subgroup.index, Nat.card_eq_fintype_card] using
        (Fact.out : p.Prime).coprime_iff_not_dvd.mpr S.not_dvd_index
    apply subgroupCohomologyComparison_coprime_zero C (S : Subgroup G) 2 p hp
      ((originalRelationExtensionObstruction B C φ).hom y)
      (originalRelationExtensionObstruction_nsmul_zero B C p hB φ y)
    rw [subgroupCohomologyComparison_eq_restriction]
    exact h

/-- The constructed scalar pairing's zero locus is already detected
on one actual prime-power subgroup of the original finite stage. -/
theorem originalRelationPrimePairingData_readout_eq_zero_iff_sylow [Finite G]
    (p : ℕ) [Fact p.Prime] (hB : ∀ b : B, p • b = 0) (S : Sylow p G)
    (d : OriginalRelationPrimePairingData B C p)
    (φ : originalRelationModule B ⟶ C) (y : groupCohomology B 1) :
    d.readout φ y = 0 ↔
      (groupCohomology.map (S : Subgroup G).subtype
        (𝟙 (Rep.res (S : Subgroup G).subtype C)) 2).hom
          ((originalRelationExtensionObstruction B C φ).hom y) = 0 :=
  (d.zero_iff φ y).trans
    (originalRelationExtensionObstruction_eq_zero_iff_sylow B C p hB S φ y)

end
end Dubon2026
