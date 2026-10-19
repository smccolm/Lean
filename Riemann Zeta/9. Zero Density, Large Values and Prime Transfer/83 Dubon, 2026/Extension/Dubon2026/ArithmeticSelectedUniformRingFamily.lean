import Dubon2026.ArithmeticSupportUniformRank
import Dubon2026.ArithmeticExactSelectedSupportFamily

/-! Construct the entire genuine auxiliary ring family and discharge
the exact uniform-rank class of the reused patching algebra. The same
families retain their original local dimensions and zero dual-Selmer
restriction kernel at every positive level. Arithmetic Hecke modules,
freeness and higher-weight local deformation conditions remain required. -/

namespace Dubon2026
noncomputable section
open Matrix IsLocalRing
open scoped NumberField MatrixGroups BigOperators
attribute [local instance] exceptionalTraceRootTopology exceptionalTraceRootDiscrete
  exceptionalTraceUnitTopology exceptionalTraceUnitDiscrete

/-- Exact arithmetic selection constructs a family of the original
enlarged-support rings satisfying the patching uniform-rank condition,
with no auxiliary family or finite-quotient bound supplied. -/
theorem arithmeticSymmetric_exists_selectedUniformlyBoundedRingFamily
    {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O]
    [Finite (ResidueField O)] [TopologicalSpace (ResidueField O)] [DiscreteTopology (ResidueField O)]
    (a : 𝓞 ℚ) (ha : a ≠ 0) (q degree : ℕ) [Fact q.Prime]
    [NeZero (2 : ZMod q)] [NeZero (3 : ZMod q)]
    (hqa : (q : 𝓞 ℚ) ∣ a) (hsize : 2 * degree < q - 1)
    (eO : ResidueField O ≃+* ZMod q)
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup (Fin 2) (ZMod q))
    (hρ : Continuous ρ)
    (himage : (SpecialLinearGroup.toGL (n := Fin 2) (R := ZMod q)).range ≤ ρ.range)
    (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det
      (GeneralLinearGroup.map eO.symm.toRingHom (((homogeneousSymmetricGL degree).comp ρ) g)) =
      Units.map (algebraMap O (ResidueField O)) (δ g))
    (C : ∀ p : rationalArithmeticExceptionalPrimes a ha,
      Submodule (ZMod q) (rationalArithmeticPrimeTraceH1Module a q
        ((homogeneousSymmetricGL degree).comp ρ)
        ((homogeneousSymmetricGL_continuous degree).comp hρ) p.val))
    (S : Finset ℕ) :
    let R := (homogeneousSymmetricGL degree).comp ρ
    let hR := (homogeneousSymmetricGL_continuous degree).comp hρ
    let σ := (GeneralLinearGroup.map eO.symm.toRingHom).comp R
    let hσ : Continuous σ :=
      (show Continuous (GeneralLinearGroup.map (n := Fin (degree + 1)) eO.symm.toRingHom)
        from continuous_of_discreteTopology).comp hR
    let P := rationalArithmeticTraceDualSelmer a q hqa ha R hR
      (rationalArithmeticTraceLocalConditionProduct a q ha R hR C)
    ∃ Q : ℕ → Finset Nat.Primes,
      (∀ i, ArithmeticSymmetricSelectedFamilyProperty a ha q degree (i + 1) hqa ρ hρ C S (Q i) ∧
        (Q i).card = Module.finrank (ZMod q) P) ∧
      (letI : ∀ i, IsLocalRing (ArithmeticSupportFamilyRing a ha q degree hqa σ hσ δ Q i) :=
         fun i => arithmeticSupportFamilyRing_isLocal a ha q degree hqa σ hσ δ Q hδ i
       Algebra.UniformlyBoundedRank (ArithmeticSupportFamilyRing a ha q degree hqa σ hσ δ Q)) := by
  classical
  let R := (homogeneousSymmetricGL degree).comp ρ
  let hR := (homogeneousSymmetricGL_continuous degree).comp hρ
  let σ := (GeneralLinearGroup.map eO.symm.toRingHom).comp R
  have hmap : Continuous (GeneralLinearGroup.map (n := Fin (degree + 1)) eO.symm.toRingHom) :=
    continuous_of_discreteTopology
  have hσ : Continuous σ := hmap.comp hR
  let P := rationalArithmeticTraceDualSelmer a q hqa ha R hR
    (rationalArithmeticTraceLocalConditionProduct a q ha R hR C)
  have hselect : ∀ i : ℕ, ∃ Q : Finset Nat.Primes,
      ArithmeticSymmetricSelectedFamilyProperty a ha q degree (i + 1) hqa ρ hρ C S Q ∧
      Q.card = Module.finrank (ZMod q) P :=
    fun i => arithmeticSymmetric_exists_exactSelectedFamilyProperty
      a ha q degree (i + 1) hqa hsize ρ hρ himage C S
  choose Q hQ hcard using hselect
  refine ⟨Q, fun i => ⟨hQ i, hcard i⟩, ?_⟩
  have he : (GeneralLinearGroup.map eO.toRingHom).comp σ = R := by
    apply MonoidHom.ext
    intro x
    change GeneralLinearGroup.map eO.toRingHom
      (GeneralLinearGroup.map eO.symm.toRingHom (R x)) = R x
    apply Units.ext
    apply Matrix.ext
    intro j k
    exact eO.apply_symm_apply ((R x).val j k)
  have hgood : ∀ i, ∀ p : Q i, RationalArithmeticTorusAuxiliaryPrime a q degree (i + 1)
      ((GeneralLinearGroup.map eO.toRingHom).comp σ) p.val := by
    rw [he]
    intro i
    exact ArithmeticSymmetricSelectedFamilyProperty.good a ha q degree (i + 1) hqa ρ hρ C S (Q i) (hQ i)
  exact arithmeticSupportFamily_uniformlyBoundedRank
    a ha q degree (Module.finrank (ZMod q) P) hqa eO σ hσ δ hδ Q hgood hcard

end
end Dubon2026
