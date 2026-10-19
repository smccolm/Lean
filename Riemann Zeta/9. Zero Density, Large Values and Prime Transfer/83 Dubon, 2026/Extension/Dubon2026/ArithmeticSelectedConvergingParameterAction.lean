import Dubon2026.ArithmeticConvergingParameterAction
import Dubon2026.ArithmeticExactSelectedSupportFamily

/-! Exact native auxiliary-prime selection constructs the actual
continuous group-algebra parameter action, its quantitative kernel
convergence and its factorization to the original deformation ring.
The same family retains finite avoidance, its original local dimensions
and the zero common dual-Selmer kernel. DUB-17 still requires genuine
modular realization, crystalline conditions and Hecke-module freeness. -/

namespace Dubon2026
noncomputable section
open Matrix IsLocalRing
open scoped NumberField MatrixGroups BigOperators
attribute [local instance] exceptionalTraceRootTopology exceptionalTraceRootDiscrete
  exceptionalTraceUnitTopology exceptionalTraceUnitDiscrete

/-- The exact codomain of the already proved arithmetic comparison.
The lambda only extracts the existing constructor's result type; it does
not assume a good-prime family or an inhabitant of that result type. -/
@[irreducible]
def ArithmeticSupportConvergingParameterData
    {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O]
    [Finite (ResidueField O)] [TopologicalSpace (ResidueField O)] [DiscreteTopology (ResidueField O)]
    (a : 𝓞 ℚ) (ha : a ≠ 0) (b : 𝓞 ℚ) (hb : b ≠ 0) (hab : a ∣ b)
    (q degree level : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a)
    (hlevel : 0 < level) (eO : ResidueField O ≃+* ZMod q)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup (Fin (degree + 1)) (ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) = Units.map (algebraMap O (ResidueField O)) (δ g))
    (Q : Finset Nat.Primes) (hba : b = a * ∏ p ∈ Q, (p.val : 𝓞 ℚ)) (g : ℕ) : Type _ :=
  (fun {T : Type _} (_ : (∀ p : Q, RationalArithmeticTorusAuxiliaryPrime a q degree level
      ((GeneralLinearGroup.map eO.toRingHom).comp σ) p.val) → Q.card = g → T) => T)
    (fun hgood hcard => arithmeticUniversalOriginalSupportConvergingParameterAction
      a ha b hb hab q degree level hqa hlevel eO σ hσ δ hδ Q hba hgood g hcard)

/-- The proved original arithmetic comparison inhabits its exact
output type. The named type keeps arithmetic selection separate from
normalization of the two concrete coefficient rings. -/
def arithmeticSupportConvergingParameterDataOfGood
    {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O]
    [Finite (ResidueField O)] [TopologicalSpace (ResidueField O)] [DiscreteTopology (ResidueField O)]
    (a : 𝓞 ℚ) (ha : a ≠ 0) (b : 𝓞 ℚ) (hb : b ≠ 0) (hab : a ∣ b)
    (q degree level : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a)
    (hlevel : 0 < level) (eO : ResidueField O ≃+* ZMod q)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup (Fin (degree + 1)) (ResidueField O))
    (hσ : Continuous σ) (δ : rationalArithmeticGaloisGroup a →* Oˣ)
    (hδ : ∀ g, GeneralLinearGroup.det (σ g) = Units.map (algebraMap O (ResidueField O)) (δ g))
    (Q : Finset Nat.Primes) (hba : b = a * ∏ p ∈ Q, (p.val : 𝓞 ℚ))
    (hgood : ∀ p : Q, RationalArithmeticTorusAuxiliaryPrime a q degree level
      ((GeneralLinearGroup.map eO.toRingHom).comp σ) p.val)
    (g : ℕ) (hcard : Q.card = g) :
    ArithmeticSupportConvergingParameterData a ha b hb hab q degree level hqa hlevel eO σ hσ δ hδ Q hba g := by
  unfold ArithmeticSupportConvergingParameterData
  exact arithmeticUniversalOriginalSupportConvergingParameterAction
    a ha b hb hab q degree level hqa hlevel eO σ hσ δ hδ Q hba hgood g hcard

/-- One actual selected family simultaneously has the original local
dimensions, zero common dual-Selmer restriction kernel and an actual power-series
action on its original auxiliary group algebra, all kernel bounds up to its level and
its factorization to the original deformation-ring parameter map. The
family and enlarged-support hypotheses are constructed from selection. -/
theorem arithmeticSymmetric_exists_exactSelectedConvergingParameterAction
    {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O]
    [Finite (ResidueField O)] [TopologicalSpace (ResidueField O)] [DiscreteTopology (ResidueField O)]
    (a : 𝓞 ℚ) (ha : a ≠ 0) (q degree level : ℕ) [Fact q.Prime]
    [NeZero (2 : ZMod q)] [NeZero (3 : ZMod q)]
    (hqa : (q : 𝓞 ℚ) ∣ a) (hsize : 2 * degree < q - 1) (hlevel : 0 < level)
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
    ∃ Q : Finset Nat.Primes,
      ArithmeticSymmetricSelectedFamilyProperty a ha q degree level hqa ρ hρ C S Q ∧
      Q.card = Module.finrank (ZMod q) P ∧
      (let b : 𝓞 ℚ := a * ∏ p ∈ Q, (p.val : 𝓞 ℚ)
       let hb : b ≠ 0 := mul_ne_zero ha (Finset.prod_ne_zero_iff.mpr
         (fun p _ => Nat.cast_ne_zero.mpr p.property.ne_zero))
       let hab : a ∣ b := dvd_mul_right a _
       Nonempty (ArithmeticSupportConvergingParameterData
         a ha b hb hab q degree level hqa hlevel eO σ hσ δ hδ Q rfl (Module.finrank (ZMod q) P))) := by
  classical
  let R := (homogeneousSymmetricGL degree).comp ρ
  let hR := (homogeneousSymmetricGL_continuous degree).comp hρ
  let σ := (GeneralLinearGroup.map eO.symm.toRingHom).comp R
  have hmap : Continuous (GeneralLinearGroup.map (n := Fin (degree + 1)) eO.symm.toRingHom) :=
    continuous_of_discreteTopology
  have hσ : Continuous σ := hmap.comp hR
  obtain ⟨Q, hQ, hcard⟩ := arithmeticSymmetric_exists_exactSelectedFamilyProperty
    a ha q degree level hqa hsize ρ hρ himage C S
  refine ⟨Q, hQ, hcard, ?_⟩
  let b : 𝓞 ℚ := a * ∏ p ∈ Q, (p.val : 𝓞 ℚ)
  have hb : b ≠ 0 := mul_ne_zero ha (Finset.prod_ne_zero_iff.mpr
    (fun p _ => Nat.cast_ne_zero.mpr p.property.ne_zero))
  have hab : a ∣ b := dvd_mul_right a _
  have he : (GeneralLinearGroup.map eO.toRingHom).comp σ = R := by
    apply MonoidHom.ext
    intro g
    change GeneralLinearGroup.map eO.toRingHom
      (GeneralLinearGroup.map eO.symm.toRingHom (R g)) = R g
    apply Units.ext
    apply Matrix.ext
    intro i j
    exact eO.apply_symm_apply ((R g).val i j)
  have hgood : ∀ p : Q, RationalArithmeticTorusAuxiliaryPrime a q degree level
      ((GeneralLinearGroup.map eO.toRingHom).comp σ) p.val := by
    rw [he]
    exact ArithmeticSymmetricSelectedFamilyProperty.good a ha q degree level hqa ρ hρ C S Q hQ
  exact ⟨arithmeticSupportConvergingParameterDataOfGood
    a ha b hb hab q degree level hqa hlevel eO σ hσ δ hδ Q rfl hgood _ hcard⟩

end
end Dubon2026
