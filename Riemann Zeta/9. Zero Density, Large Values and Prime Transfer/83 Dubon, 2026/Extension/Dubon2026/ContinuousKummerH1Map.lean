import Dubon2026.ContinuousRootRadicalCocycle

/-! # The actual Kummer map to original continuous H1

The radical, original root cocycle, surjectivity and power kernel are constructed.
This is the degree-one input for the local cup/norm comparison, not local duality.
-/

namespace Dubon2026
noncomputable section

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
  [IsGalois K Ω] [IsAlgClosed Ω] (n : ℕ) [NeZero n]
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- The original continuous H1 of the actual root representation and action. -/
abbrev GaloisRootContinuousH1 :=
  ContinuousRepresentationH1 (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)
    (discreteGaloisRootAction_continuous (K := K) (Ω := Ω) n)

/-- Choose an actual radical of the original base unit in the actual algebraic closure. -/
def galoisKummerRadical (a : Kˣ) : Ωˣ :=
  (algebraicallyClosedUnitPower_surjective n (NeZero.pos n)
    (Units.map (algebraMap K Ω).toMonoidHom a)).choose

omit [IsGalois K Ω]
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)] in
/-- The chosen original radical has exactly the required nth power. -/
theorem galoisKummerRadical_pow (a : Kˣ) :
    galoisKummerRadical (Ω := Ω) n a ^ n = Units.map (algebraMap K Ω).toMonoidHom a :=
  (algebraicallyClosedUnitPower_surjective n (NeZero.pos n)
    (Units.map (algebraMap K Ω).toMonoidHom a)).choose_spec

/-- The actual Kummer class of an original base-field unit. -/
def galoisKummerH1Class (a : Kˣ) : GaloisRootContinuousH1 (K := K) (Ω := Ω) n :=
  Submodule.Quotient.mk (galoisRootRadicalOneCocycle n a
    (galoisKummerRadical (Ω := Ω) n a) (galoisKummerRadical_pow n a))

/-- Every actual radical realization represents the same original Kummer class;
the class does not depend on the chosen root or continuous representative. -/
theorem galoisKummerH1Class_eq_of_radical
    (a : Kˣ) (β : Ωˣ) (hβ : β ^ n = Units.map (algebraMap K Ω).toMonoidHom a)
    (c : continuousRepresentationCocyclesOne
      (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n))
    (hc : ∀ g : Gal(Ω/K), g • β / β =
      ((Additive.toMul (Rep.toAdditive (c.val g)) : rootsOfUnity n Ω) : Ωˣ)) :
    galoisKummerH1Class n a = Submodule.Quotient.mk c := by
  exact (continuousRootOneCocycle_class_eq_iff_power_class n
    (galoisRootRadicalOneCocycle n a (galoisKummerRadical (Ω := Ω) n a)
      (galoisKummerRadical_pow n a)) c a a (galoisKummerRadical n a) β
    (galoisKummerRadical_pow n a) hβ
    (fun g => (galoisRootRadicalOneCocycle_ratio n a (galoisKummerRadical n a)
      (galoisKummerRadical_pow n a) g).symm) hc).mpr rfl

/-- Every original root-valued continuous H1 class is the Kummer class of an
actual base-field unit, by the proved continuous Hilbert-90 radical construction. -/
theorem galoisKummerH1Class_surjective :
    Function.Surjective (galoisKummerH1Class (K := K) (Ω := Ω) n) := by
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ c =>
    obtain ⟨a, β, hβ, hc⟩ := continuousRootOneCocycle_exists_radical n c
    exact ⟨a, galoisKummerH1Class_eq_of_radical n a β hβ c hc⟩

/-- The kernel of the actual Kummer class map consists exactly of the original
base-field nth powers, with no assumed cohomological comparison. -/
theorem galoisKummerH1Class_eq_zero_iff (a : Kˣ) :
    galoisKummerH1Class (Ω := Ω) n a = 0 ↔
      a ∈ (powMonoidHom n : Kˣ →* Kˣ).range :=
  galoisRootRadicalOneCocycle_class_zero_iff n a
    (galoisKummerRadical (Ω := Ω) n a) (galoisKummerRadical_pow n a)

/-- Multiplication of original base units becomes addition of their actual
continuous Kummer classes, as proved on the original radical cocycles. -/
theorem galoisKummerH1Class_mul (a b : Kˣ) :
    galoisKummerH1Class (Ω := Ω) n (a * b) =
      galoisKummerH1Class n a + galoisKummerH1Class n b := by
  let β := galoisKummerRadical (Ω := Ω) n a
  let γ := galoisKummerRadical (Ω := Ω) n b
  let c := galoisRootRadicalOneCocycle n a β (galoisKummerRadical_pow n a)
  let d := galoisRootRadicalOneCocycle n b γ (galoisKummerRadical_pow n b)
  change galoisKummerH1Class n (a * b) = Submodule.Quotient.mk c + Submodule.Quotient.mk d
  rw [← Submodule.Quotient.mk_add]
  have hβγ : (β * γ) ^ n = Units.map (algebraMap K Ω).toMonoidHom (a * b) := by
    rw [mul_pow, galoisKummerRadical_pow, galoisKummerRadical_pow, map_mul]
  apply galoisKummerH1Class_eq_of_radical n (a * b) (β * γ) hβγ (c + d)
  intro g
  change g • (β * γ) / (β * γ) =
    ((Additive.toMul (Rep.toAdditive (c.val g)) : rootsOfUnity n Ω) : Ωˣ) *
      ((Additive.toMul (Rep.toAdditive (d.val g)) : rootsOfUnity n Ω) : Ωˣ)
  rw [galoisRootRadicalOneCocycle_ratio, galoisRootRadicalOneCocycle_ratio,
    smul_mul', mul_div_mul_comm]

/-- The original Kummer class map as an actual group homomorphism. -/
def galoisKummerH1Hom : Kˣ →* Multiplicative (GaloisRootContinuousH1 (K := K) (Ω := Ω) n) where
  toFun a := Multiplicative.ofAdd (galoisKummerH1Class n a)
  map_one' := (galoisKummerH1Class_eq_zero_iff n 1).mpr ⟨1, one_pow n⟩
  map_mul' a b := galoisKummerH1Class_mul n a b

/-- The actual homomorphism has exactly the original nth-power subgroup as kernel. -/
theorem galoisKummerH1Hom_ker :
    (galoisKummerH1Hom (K := K) (Ω := Ω) n).ker =
      (powMonoidHom n : Kˣ →* Kˣ).range := by
  ext a
  exact galoisKummerH1Class_eq_zero_iff n a

/-- The genuine Kummer homomorphism is onto the original root H1. -/
theorem galoisKummerH1Hom_surjective :
    Function.Surjective (galoisKummerH1Hom (K := K) (Ω := Ω) n) := by
  intro x
  obtain ⟨a, ha⟩ := galoisKummerH1Class_surjective n (Multiplicative.toAdd x)
  exact ⟨a, ha⟩

/-- The original base units modulo actual nth powers are additively equivalent
to the actual continuous root-of-unity H1. Both directions and the kernel are proved. -/
def galoisKummerH1Equiv :
    Additive (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) ≃+
      GaloisRootContinuousH1 (K := K) (Ω := Ω) n := by
  let f : Kˣ →* Multiplicative (GaloisRootContinuousH1 (K := K) (Ω := Ω) n) :=
    galoisKummerH1Hom n
  let e₁ : Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range ≃* Kˣ ⧸ f.ker :=
    QuotientGroup.quotientMulEquivOfEq (galoisKummerH1Hom_ker (K := K) (Ω := Ω) n).symm
  let e₂ : Kˣ ⧸ f.ker ≃* Multiplicative (GaloisRootContinuousH1 (K := K) (Ω := Ω) n) :=
    QuotientGroup.quotientKerEquivOfSurjective f
      (galoisKummerH1Hom_surjective (K := K) (Ω := Ω) n)
  exact (MulEquiv.toAdditive (e₁.trans e₂)).trans
    (AddEquiv.additiveMultiplicative (GaloisRootContinuousH1 (K := K) (Ω := Ω) n))

/-- The quotient equivalence maps an original base unit to its literal original
radical cocycle class, retaining the concrete comparison used by the cup pairing. -/
theorem galoisKummerH1Equiv_apply (a : Kˣ) :
    galoisKummerH1Equiv (Ω := Ω) n
      (Additive.ofMul (QuotientGroup.mk' (powMonoidHom n : Kˣ →* Kˣ).range a)) =
        galoisKummerH1Class n a := by
  rfl

end
end Dubon2026
