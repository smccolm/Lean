import RiemannZeta.GuthMaynard.KloostermanEulerProduct

open Polynomial Classical

namespace RiemannZeta.GuthMaynard

def HarcosMonicDegree (p d : ℕ) [Fact p.Prime] :=
  {k : (ZMod p)[X] // k.Monic ∧ k.natDegree = d}

noncomputable def harcosMonicDegreeEquiv
    (p d : ℕ) [Fact p.Prime] :
    (Fin d → ZMod p) ≃ HarcosMonicDegree p d where
  toFun v := ⟨monicPolynomialOfCoeffs p d v, by
    constructor
    · rw [Polynomial.Monic, leadingCoeff,
        natDegree_monicPolynomialOfCoeffs,
        coeff_monicPolynomialOfCoeffs_self]
    · exact natDegree_monicPolynomialOfCoeffs p d v⟩
  invFun k i := k.1.coeff i
  left_inv v := by
    funext i
    exact coeff_monicPolynomialOfCoeffs_of_lt p d i v i.2
  right_inv k := by
    apply Subtype.ext
    ext i
    by_cases hi : i < d
    · exact coeff_monicPolynomialOfCoeffs_of_lt p d i _ hi
    by_cases hid : i = d
    · subst i
      rw [coeff_monicPolynomialOfCoeffs_self]
      symm
      simpa [k.2.2] using k.2.1.coeff_natDegree
    · have hdi : d < i := by omega
      calc
        (monicPolynomialOfCoeffs p d fun i ↦ k.1.coeff i).coeff i = 0 :=
          Polynomial.coeff_eq_zero_of_natDegree_lt (by
            rw [natDegree_monicPolynomialOfCoeffs]
            exact hdi)
        _ = k.1.coeff i := (Polynomial.coeff_eq_zero_of_natDegree_lt (by
          rw [k.2.2]
          exact hdi)).symm

def HarcosIrreducibleMonic (p : ℕ) [Fact p.Prime] :=
  {q : (ZMod p)[X] // Irreducible q ∧ q.Monic}

def HarcosFactorization (p d : ℕ) [Fact p.Prime] :=
  {s : Multiset (HarcosIrreducibleMonic p) //
    (s.map (fun q ↦ q.1.natDegree)).sum = d}

noncomputable def harcosFactorizationOfMonicDegree
    (p d : ℕ) [Fact p.Prime] (k : HarcosMonicDegree p d) :
    HarcosFactorization p d := by
  let s := UniqueFactorizationMonoid.normalizedFactors k.1
  have hs : ∀ q ∈ s, Irreducible q ∧ q.Monic := by
    intro q hq
    have h := (Polynomial.mem_normalizedFactors_iff k.2.1.ne_zero).mp hq
    exact ⟨h.1, h.2.1⟩
  let t : Multiset (HarcosIrreducibleMonic p) :=
    Multiset.pmap (fun q h ↦ ⟨q, h⟩) s hs
  refine ⟨t, ?_⟩
  have hval : t.map (fun q ↦ q.1) = s := by
    dsimp [t]
    rw [Multiset.map_pmap]
    exact Multiset.pmap_eq_map _ id s hs |>.trans (Multiset.map_id s)
  have hdeg := harcosNormalizedFactors_degree_sum p k.1 k.2.1
  calc
    (t.map (fun q ↦ q.1.natDegree)).sum =
        (s.map Polynomial.natDegree).sum := by
      simpa [Function.comp_def] using
        congrArg (fun u : Multiset ((ZMod p)[X]) ↦
          (u.map Polynomial.natDegree).sum) hval
    _ = k.1.natDegree := hdeg
    _ = d := k.2.2

noncomputable def harcosMonicDegreeOfFactorization
    (p d : ℕ) [Fact p.Prime] (s : HarcosFactorization p d) :
    HarcosMonicDegree p d := by
  let k : (ZMod p)[X] := (s.1.map (fun q ↦ q.1)).prod
  have hkmonic : k.Monic := by
    dsimp [k]
    exact monic_multiset_prod_of_monic s.1 (fun q ↦ q.1)
      (fun (q : HarcosIrreducibleMonic p) _hq ↦ q.2.2)
  refine ⟨k, hkmonic, ?_⟩
  dsimp [k]
  have hmonoVals : ∀ q ∈ s.1.map (fun q ↦ q.1), q.Monic := by
    intro q hq
    obtain ⟨r, _hr, rfl⟩ := Multiset.mem_map.mp hq
    exact r.2.2
  rw [natDegree_multiset_prod_of_monic _ hmonoVals, Multiset.map_map]
  exact s.2

theorem harcosFactorizationOfMonicDegree_map_val
    (p d : ℕ) [Fact p.Prime] (k : HarcosMonicDegree p d) :
    (harcosFactorizationOfMonicDegree p d k).1.map (fun q ↦ q.1) =
      UniqueFactorizationMonoid.normalizedFactors k.1 := by
  simp only [harcosFactorizationOfMonicDegree]
  rw [Multiset.map_pmap, Multiset.pmap_eq_map]
  simp

theorem harcosMonicDegree_factorization_left
    (p d : ℕ) [Fact p.Prime] (k : HarcosMonicDegree p d) :
    harcosMonicDegreeOfFactorization p d
      (harcosFactorizationOfMonicDegree p d k) = k := by
  apply Subtype.ext
  change ((harcosFactorizationOfMonicDegree p d k).1.map
      (fun q ↦ q.1)).prod = k.1
  have hmap : (harcosFactorizationOfMonicDegree p d k).1.map
      (fun q ↦ q.1) =
      UniqueFactorizationMonoid.normalizedFactors k.1 := by
    exact harcosFactorizationOfMonicDegree_map_val p d k
  rw [hmap, UniqueFactorizationMonoid.prod_normalizedFactors_eq
    k.2.1.ne_zero, k.2.1.normalize_eq_self]

theorem harcosMonicDegree_factorization_right
    (p d : ℕ) [Fact p.Prime] (s : HarcosFactorization p d) :
    harcosFactorizationOfMonicDegree p d
      (harcosMonicDegreeOfFactorization p d s) = s := by
  apply Subtype.ext
  apply Multiset.map_injective Subtype.val_injective
  change (harcosFactorizationOfMonicDegree p d
      (harcosMonicDegreeOfFactorization p d s)).1.map
        (fun q ↦ q.1) = s.1.map (fun q ↦ q.1)
  have hnorm : UniqueFactorizationMonoid.normalizedFactors
      ((s.1.map (fun q ↦ q.1)).prod) = s.1.map (fun q ↦ q.1) := by
    rw [UniqueFactorizationMonoid.normalizedFactors_prod_eq]
    · rw [Multiset.map_map]
      apply Multiset.map_congr rfl
      intro q hq
      exact q.2.2.normalize_eq_self
    · intro q hq
      obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hq
      exact r.2.1
  simp only [harcosFactorizationOfMonicDegree]
  rw [Multiset.map_pmap, Multiset.pmap_eq_map]
  simpa [harcosMonicDegreeOfFactorization] using hnorm

noncomputable def harcosMonicFactorizationEquiv
    (p d : ℕ) [Fact p.Prime] :
    HarcosMonicDegree p d ≃ HarcosFactorization p d where
  toFun := harcosFactorizationOfMonicDegree p d
  invFun := harcosMonicDegreeOfFactorization p d
  left_inv := harcosMonicDegree_factorization_left p d
  right_inv := harcosMonicDegree_factorization_right p d

noncomputable def harcosCoeffsFactorizationEquiv
    (p d : ℕ) [Fact p.Prime] :
    (Fin d → ZMod p) ≃ HarcosFactorization p d :=
  (harcosMonicDegreeEquiv p d).trans (harcosMonicFactorizationEquiv p d)

noncomputable instance harcosFactorizationFintype
    (p d : ℕ) [Fact p.Prime] : Fintype (HarcosFactorization p d) :=
  Fintype.ofEquiv (Fin d → ZMod p) (harcosCoeffsFactorizationEquiv p d)

noncomputable def harcosFactorizationWeight
    (p d : ℕ) [NeZero p] [Fact p.Prime] (a b : ZMod p)
    (s : HarcosFactorization p d) : ℂ :=
  (s.1.map (fun q ↦ harcosEtaPolynomial p a b q.1)).prod

theorem harcosEtaDegreeSum_eq_factorizationSum
    (p d : ℕ) [NeZero p] [Fact p.Prime] (a b : ZMod p) :
    harcosEtaDegreeSum p d a b =
      ∑ s : HarcosFactorization p d,
        harcosFactorizationWeight p d a b s := by
  unfold harcosEtaDegreeSum
  apply Fintype.sum_equiv (harcosCoeffsFactorizationEquiv p d)
  intro v
  change harcosEtaPolynomial p a b (monicPolynomialOfCoeffs p d v) = _
  rw [harcosEtaPolynomial_eq_normalizedFactors_product]
  · unfold harcosFactorizationWeight harcosCoeffsFactorizationEquiv
    simp only [Equiv.trans_apply]
    congr 1
    have hval :
        ((harcosMonicFactorizationEquiv p d
          (harcosMonicDegreeEquiv p d v)).1.map (fun q ↦ q.1)) =
          UniqueFactorizationMonoid.normalizedFactors
            (monicPolynomialOfCoeffs p d v) := by
      change (harcosFactorizationOfMonicDegree p d
        ⟨monicPolynomialOfCoeffs p d v, _⟩).1.map (fun q ↦ q.1) = _
      exact harcosFactorizationOfMonicDegree_map_val p d _
    rw [← hval, Multiset.map_map]
    simp
  · rw [Polynomial.Monic, leadingCoeff,
      natDegree_monicPolynomialOfCoeffs,
      coeff_monicPolynomialOfCoeffs_self]

end RiemannZeta.GuthMaynard
