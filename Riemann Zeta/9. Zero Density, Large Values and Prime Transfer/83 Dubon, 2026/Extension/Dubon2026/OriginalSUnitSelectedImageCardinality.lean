import Dubon2026.OriginalSUnitSelectedKernel
import Dubon2026.OriginalAdicIntegerPowerIndexAway

/-! # Surjectivity of the original selected S-unit local-power map

The proved exact kernel comparison identifies its image cardinality with
the original Kummer subgroup's character group. Existing finite character
duality evaluates that order. The original local integer-unit indices give
the same order for the selected target, so the actual S-unit map is
surjective. This discharges the local-unit correction input to DUB-17's
remaining principal S-union-T localization and norm-index upper bound.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical
variable (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [IsGalois K Ω]
  (S : Finset (HeightOneSpectrum (𝓞 K))) (p : ℕ) (hp : 0 < p)
  (hroot : (primitiveRoots p K).Nonempty)

local notation "N" => OriginalSUnitKummerField K Ω S p

include hp hroot in
/-- The selected original local-unit map has image order equal to the
actual Kummer subgroup order, with its kernel comparison proved. -/
theorem originalSUnitSelectedPowerMap_range_card
    (H : Subgroup Gal(N/K)) (r : ℕ)
    (e : H ≃* (Fin r → Multiplicative (ZMod p)))
    (w : Fin r → HeightOneSpectrum (𝓞 N))
    (T : Finset (HeightOneSpectrum (𝓞 K)))
    (hT : T = Finset.univ.image (fun i => originalFinitePrimeBelow K N (w i)))
    (hST : Disjoint S T)
    (hD : ∀ i, OriginalFiniteDecompositionGroup K N (w i) =
      Subgroup.zpowers (primeCoordinateGenerator e i).val) :
    Nat.card (Set.range (originalSUnitLocalPowerMap K p S T hST)) = Nat.card H := by
  letI : FiniteDimensional K N :=
    numberField_sUnit_kummerField_finiteDimensional K Ω S S.finite_toSet p hp hroot
  letI : NeZero p := ⟨hp.ne'⟩
  letI : CommGroup H := MonoidHom.commGroupOfInjective e.toMonoidHom e.injective
  letI : HasEnoughRootsOfUnity N p := {
    prim := ⟨algebraMap K N hroot.choose,
      (isPrimitiveRoot_of_mem_primitiveRoots hroot.choose_spec).map_of_injective
        (algebraMap K N).injective⟩
    cyc := rootsOfUnity.isCyclic N p }
  letI : HasEnoughRootsOfUnity N (Monoid.exponent H) :=
    HasEnoughRootsOfUnity.of_dvd N (Monoid.exponent_dvd_of_forall_pow_eq_one (by
      intro σ
      apply Subtype.ext
      exact originalKummerRadicalField_galois_pow_eq_one p hroot _ σ.val))
  let Q (v : T) := (v.val.adicCompletionIntegers K)ˣ ⧸ (powMonoidHom p).range
  letI (v : T) : CommGroup (Q v) := inferInstance
  let f : (S : Set (HeightOneSpectrum (𝓞 K))).unit K →* (∀ v : T, Q v) :=
    originalSUnitLocalPowerMap K p S T hST
  let g := originalSUnitKummerCharacterMap K Ω S p hp hroot H
  have hKer : f.ker = g.ker :=
    originalSUnitSelectedPowerMap_ker_eq K Ω S p hp hroot H r e w T hT hST hD
  change Nat.card f.range = _
  calc
    Nat.card f.range = f.ker.index := (Subgroup.index_ker f).symm
    _ = Nat.card (H →* Nˣ) := Nat.card_congr
      ((QuotientGroup.quotientMulEquivOfEq hKer).trans
        (QuotientGroup.quotientKerEquivOfSurjective g
          (originalSUnitKummerCharacterMap_surjective K Ω S p hp hroot H))).toEquiv
    _ = Nat.card H := CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity H N

include hp hroot in
/-- The constructed original coordinate conditions and away-from-exponent
prime count make the actual S-unit local-unit power map surjective. -/
theorem originalSUnitSelectedPowerMap_surjective
    (H : Subgroup Gal(N/K)) (r : ℕ)
    (e : H ≃* (Fin r → Multiplicative (ZMod p)))
    (w : Fin r → HeightOneSpectrum (𝓞 N))
    (T : Finset (HeightOneSpectrum (𝓞 K)))
    (hT : T = Finset.univ.image (fun i => originalFinitePrimeBelow K N (w i)))
    (hST : Disjoint S T) (hCount : T.card = r)
    (hAway : ∀ v : T, (p : 𝓞 K) ∉ v.val.asIdeal)
    (hD : ∀ i, OriginalFiniteDecompositionGroup K N (w i) =
      Subgroup.zpowers (primeCoordinateGenerator e i).val) :
    Function.Surjective (originalSUnitLocalPowerMap K p S T hST) := by
  letI : NeZero p := ⟨hp.ne'⟩
  let Q (v : T) := (v.val.adicCompletionIntegers K)ˣ ⧸ (powMonoidHom p).range
  letI (v : T) : CommGroup (Q v) := inferInstance
  have hLocal (v : T) : Nat.card (Q v) = p :=
    originalAdicIntegerPowerQuotient_card_away K v.val p hp hroot.choose
      (isPrimitiveRoot_of_mem_primitiveRoots hroot.choose_spec) (hAway v)
  letI (v : T) : Finite (Q v) := Nat.finite_of_card_ne_zero ((hLocal v).symm ▸ hp.ne')
  have hTarget : Nat.card (∀ v : T, Q v) = p ^ r := by
    rw [Nat.card_pi]
    simp only [hLocal, Finset.prod_const, Finset.card_univ, Fintype.card_coe, hCount]
  have hH : Nat.card H = p ^ r := by
    rw [Nat.card_congr e.toEquiv]
    simp [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  have hImage : Nat.card (Set.range (originalSUnitLocalPowerMap K p S T hST)) =
      Nat.card (∀ v : T, Q v) := by
    rw [originalSUnitSelectedPowerMap_range_card K Ω S p hp hroot H r e w T hT hST hD,
      hH, hTarget]
  let f : (S : Set (HeightOneSpectrum (𝓞 K))).unit K →* (∀ v : T, Q v) :=
    originalSUnitLocalPowerMap K p S T hST
  exact (MonoidHom.range_eq_top (f := f)).mp (Subgroup.eq_top_of_card_eq f.range hImage)

end
end Dubon2026
