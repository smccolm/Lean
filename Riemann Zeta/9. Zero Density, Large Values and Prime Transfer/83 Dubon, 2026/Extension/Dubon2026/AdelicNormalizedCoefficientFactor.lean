import Dubon2026.AdelicPlaceComplementCriterion
import Dubon2026.AdelicLocalFullMixedCoefficient

/-! # Normalized original cusp coefficients and exact factorization at a genuine good place -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

/-- The actual normalized matrix coefficient of an original representation vector. -/
def representationNormalizedCoefficient {G V : Type*} [Group G]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] (ρ : Representation ℂ G V) (y : V) (g : G) : ℂ :=
  inner ℂ y (ρ g y) / inner ℂ y y

/-- The normalized original coefficient is exactly one at the identity for every nonzero original vector. -/
theorem representationNormalizedCoefficient_one {G V : Type*} [Group G]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] (ρ : Representation ℂ G V) (y : V) (hy : y ≠ 0) :
    representationNormalizedCoefficient ρ y 1 = 1 := by
  rw [representationNormalizedCoefficient, map_one, Module.End.one_apply]
  exact div_self ((inner_self_ne_zero (𝕜 := ℂ)).mpr hy)

/-- Exact normalization identifies the original product-coefficient equation with its literal cross-multiplied inner-product identity. -/
theorem representationNormalizedCoefficient_mul_iff {G V : Type*} [Group G]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] (ρ : Representation ℂ G V) (y : V) (hy : y ≠ 0)
    (g a : G) :
    representationNormalizedCoefficient ρ y (g * a) =
      representationNormalizedCoefficient ρ y g * representationNormalizedCoefficient ρ y a ↔
    inner ℂ y (ρ g (ρ a y)) * inner ℂ y y = inner ℂ y (ρ g y) * inner ℂ y (ρ a y) := by
  have hn : inner ℂ y y ≠ 0 := (inner_self_ne_zero (𝕜 := ℂ)).mpr hy
  simp only [representationNormalizedCoefficient, map_mul, Module.End.mul_apply]
  rw [div_mul_div_comm, div_eq_div_iff hn (mul_ne_zero hn hn), ← mul_assoc]
  exact ⟨fun h => mul_right_cancel₀ hn h, fun h => congrArg (fun z : ℂ => z * inner ℂ y y) h⟩

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- The normalized coefficient of the literal original adelic cusp generator in its actual Hilbert representation. -/
def adelicNormalizedCuspCoefficient (a : RationalAdelicGL2) : ℂ :=
  representationNormalizedCoefficient (adelicCyclicHilbertRepresentation f) (adelicCyclicHilbertGenerator f) a

/-- The genuine normalized cusp coefficient is one at the original adelic identity. -/
theorem adelicNormalizedCuspCoefficient_one (hf : f ≠ 0) : adelicNormalizedCuspCoefficient f 1 = 1 :=
  @representationNormalizedCoefficient_one RationalAdelicGL2 (AdelicCyclicHilbert f)
    inferInstance inferInstance inferInstance (adelicCyclicHilbertRepresentation f)
    (adelicCyclicHilbertGenerator f) (adelicCyclicHilbertGenerator_ne_zero f hf)

/-- Actual good-prime local and full-complement original cusp coefficients multiply with the exact original normalization. -/
theorem adelicNormalizedCuspCoefficient_local_fullAway {p : ℕ} [NeZero p] [Fact p.Prime]
    (F : PrimitiveCuspForm N k) (hpN : p.Coprime N)
    (g : GeneralLinearGroup (Fin 2) ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ))
    (a : AdelicFullAwayGroup (rationalPrimePlace p (Fact.out : p.Prime))) :
    adelicNormalizedCuspCoefficient F.toCuspForm
      (rationalAdelicFiniteGL2Embedding (finiteAdelicLocalGL2 (rationalPrimePlace p (Fact.out : p.Prime)) g) *
        adelicFullAwayEmbedding (rationalPrimePlace p (Fact.out : p.Prime)) a) =
      adelicNormalizedCuspCoefficient F.toCuspForm
        (rationalAdelicFiniteGL2Embedding (finiteAdelicLocalGL2 (rationalPrimePlace p (Fact.out : p.Prime)) g)) *
      adelicNormalizedCuspCoefficient F.toCuspForm (adelicFullAwayEmbedding (rationalPrimePlace p (Fact.out : p.Prime)) a) :=
  (@representationNormalizedCoefficient_mul_iff RationalAdelicGL2 (AdelicCyclicHilbert F.toCuspForm)
    inferInstance inferInstance inferInstance (adelicCyclicHilbertRepresentation F.toCuspForm)
    (adelicCyclicHilbertGenerator F.toCuspForm)
    (adelicCyclicHilbertGenerator_ne_zero F.toCuspForm (primitiveCuspForm_ne_zero F))
    _ _).mpr (adelicCyclicLocal_fullAway_coefficient_factor F hpN g a)

/-- Every original full adelic matrix with identity at a good place factors in the normalized original coefficient against that place. -/
theorem adelicNormalizedCuspCoefficient_local_mul {p : ℕ} [NeZero p] [Fact p.Prime]
    (F : PrimitiveCuspForm N k) (hpN : p.Coprime N)
    (g : GeneralLinearGroup (Fin 2) ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ))
    (a : RationalAdelicGL2) (ha : adelicPlaceGL2Hom (rationalPrimePlace p (Fact.out : p.Prime)) a = 1) :
    adelicNormalizedCuspCoefficient F.toCuspForm
      (rationalAdelicFiniteGL2Embedding (finiteAdelicLocalGL2 (rationalPrimePlace p (Fact.out : p.Prime)) g) * a) =
      adelicNormalizedCuspCoefficient F.toCuspForm
        (rationalAdelicFiniteGL2Embedding (finiteAdelicLocalGL2 (rationalPrimePlace p (Fact.out : p.Prime)) g)) *
      adelicNormalizedCuspCoefficient F.toCuspForm a := by
  obtain ⟨b, rfl⟩ := adelicFullAwayEmbedding_of_place_one _ a ha
  exact adelicNormalizedCuspCoefficient_local_fullAway F hpN g b

end
end Dubon2026
