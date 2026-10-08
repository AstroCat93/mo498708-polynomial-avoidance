import Formal.MO498708.MonicSum
import Formal.MO498708.PowerSum

/-!
# MO 498708, Lemma 2.3 step (c): `s_n` as a sum over `F_{p^n}`

For `L = GaloisField p n` (`n ≥ 1`) we show

  `s_n = ∑_{π monic irreducible, deg π ∣ n} deg π · χ(π)^{n/deg π} = ∑_{β ∈ L} Ψ_n(β)`,

with `Ψ_n(β) = (β^{p-1} - 1)^{d ρ}`, `ρ = ∑_{σ<n} p^σ`.  Each `β` is grouped by its minimal
polynomial `π` (which has exactly `deg π` roots in `L`), and `Ψ_n(β) = χ(π)^{n / deg π}` is
computed with the field norm `N_{L/F_p}(x) = x^ρ`.
-/

open Finset Polynomial IntermediateField

namespace MO498708

open scoped Classical

variable {p : ℕ} [hp : Fact p.Prime]

/-- `∏_{b ∈ F_p^*} (X - b) = X^{p-1} - 1`. -/
theorem prod_X_sub_C_units :
    ∏ b ∈ (univ : Finset (ZMod p)).erase 0, (X - C b) = (X ^ (p - 1) - 1 : (ZMod p)[X]) := by
  have hp1 : 1 < p := hp.out.one_lt
  have hq : Fintype.card (ZMod p) = p := ZMod.card p
  have h1 : (X ^ p - X : (ZMod p)[X]) = ∏ a : ZMod p, (X - C a) := by
    have hm : (X ^ p - X : (ZMod p)[X]).Monic := by
      apply monic_X_pow_sub
      rw [degree_X]
      exact_mod_cast hp1
    have hroots := FiniteField.roots_X_pow_card_sub_X (ZMod p)
    rw [hq] at hroots
    have hcard : Multiset.card (X ^ p - X : (ZMod p)[X]).roots =
        (X ^ p - X : (ZMod p)[X]).natDegree := by
      rw [hroots, FiniteField.X_pow_card_sub_X_natDegree_eq _ hp1]
      simp [hq]
    have := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hm hcard
    rw [← this, hroots]
    rfl
  have h2 : (X ^ p - X : (ZMod p)[X]) = X * (X ^ (p - 1) - 1) := by
    rw [mul_sub, ← pow_succ', Nat.sub_add_cancel hp1.le, mul_one]
  have h3 : ∏ a : ZMod p, (X - C a) = X * ∏ b ∈ (univ : Finset (ZMod p)).erase 0, (X - C b) := by
    rw [← mul_prod_erase univ _ (mem_univ 0)]
    simp
  rw [h2, h3] at h1
  exact (mul_left_cancel₀ X_ne_zero h1).symm

theorem prod_sub_units {L : Type*} [Field L] [Algebra (ZMod p) L] (y : L) :
    ∏ b ∈ (univ : Finset (ZMod p)).erase 0, (y - algebraMap (ZMod p) L b) = y ^ (p - 1) - 1 := by
  have := congrArg (aeval y) (prod_X_sub_C_units (p := p))
  simpa [map_prod] using this

section GF

variable {n : ℕ}

theorem natDegree_minpoly_dvd (hn : n ≠ 0) (β : GaloisField p n) :
    (minpoly (ZMod p) β).natDegree ∣ n := by
  have hint : IsIntegral (ZMod p) β := Algebra.IsIntegral.isIntegral β
  have h := Module.finrank_mul_finrank (ZMod p) (ZMod p)⟮β⟯ (GaloisField p n)
  rw [IntermediateField.adjoin.finrank hint, GaloisField.finrank p hn] at h
  exact Dvd.intro _ h

/-- `N_{L/F_p}(β - b) = ((-1)^e π(b))^{n/e}` for `π` the minimal polynomial of `β`, `e = deg π`. -/
theorem algebraMap_norm_sub (hn : n ≠ 0) (β : GaloisField p n) (b : ZMod p) :
    algebraMap (ZMod p) (GaloisField p n)
        (Algebra.norm (ZMod p) (β - algebraMap (ZMod p) (GaloisField p n) b)) =
      algebraMap (ZMod p) (GaloisField p n)
        (((-1) ^ (minpoly (ZMod p) β).natDegree * (minpoly (ZMod p) β).eval b) ^
          (n / (minpoly (ZMod p) β).natDegree)) := by
  set π := minpoly (ZMod p) β with hπ
  set x := β - algebraMap (ZMod p) (GaloisField p n) b with hx
  have hint : IsIntegral (ZMod p) x := Algebra.IsIntegral.isIntegral x
  have hintβ : IsIntegral (ZMod p) β := Algebra.IsIntegral.isIntegral β
  have hmin : minpoly (ZMod p) x = π.comp (X + C b) := minpoly.sub_algebraMap β b
  have hsplit : Splits ((minpoly (ZMod p) x).map (algebraMap (ZMod p) (GaloisField p n))) :=
    Normal.splits inferInstance x
  have hdegx : (minpoly (ZMod p) x).natDegree = π.natDegree := by
    rw [hmin, natDegree_comp, natDegree_X_add_C, mul_one]
  rw [Algebra.norm_eq_prod_roots _ hsplit]
  -- the product of the roots
  have hprod : ((minpoly (ZMod p) x).aroots (GaloisField p n)).prod =
      algebraMap (ZMod p) (GaloisField p n) ((-1) ^ π.natDegree * π.eval b) := by
    have hc := hsplit.coeff_zero_eq_prod_roots_of_monic ((minpoly.monic hint).map _)
    rw [natDegree_map, hdegx, coeff_map, hmin, coeff_zero_eq_eval_zero, eval_comp] at hc
    simp only [eval_add, eval_X, eval_C, zero_add] at hc
    rw [aroots_def, hmin, map_mul, map_pow, map_neg, map_one, hc, ← mul_assoc, ← pow_add,
      ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]
  -- the degree `[L : F_p(x)]`
  have hfin : Module.finrank (ZMod p)⟮x⟯ (GaloisField p n) = n / π.natDegree := by
    have h1 := Module.finrank_mul_finrank (ZMod p) (ZMod p)⟮x⟯ (GaloisField p n)
    rw [IntermediateField.adjoin.finrank hint, hdegx, GaloisField.finrank p hn] at h1
    have hpos : 0 < π.natDegree := (minpoly.irreducible hintβ).natDegree_pos
    exact Nat.eq_div_of_mul_eq_right hpos.ne' h1
  rw [hprod, hfin, map_pow]

/-- `Ψ_n(β) = χ(π)^{n / deg π}` (step (c) of Lemma 2.3, for a single `β`). -/
theorem Psi_eq_chi (hn : n ≠ 0) (d : ℕ) (β : GaloisField p n) :
    (β ^ (p - 1) - 1) ^ (d * ∑ σ : Fin n, p ^ (σ : ℕ)) =
      algebraMap (ZMod p) (GaloisField p n)
        (chi d (minpoly (ZMod p) β) ^ (n / (minpoly (ZMod p) β).natDegree)) := by
  set π := minpoly (ZMod p) β with hπ
  set e := π.natDegree with he
  have hp1 : 1 ≤ p := hp.out.one_lt.le
  have hρ : (Nat.card (GaloisField p n) - 1) / (Nat.card (ZMod p) - 1) =
      ∑ σ : Fin n, p ^ (σ : ℕ) := by
    rw [GaloisField.card p n hn, Nat.card_zmod, pow_sub_one_eq p n hp1]
    exact Nat.mul_div_cancel_left _ (by have := hp.out.two_le; omega)
  rw [← prod_sub_units, mul_comm, pow_mul, ← prod_pow, ← prod_pow]
  have h1 : ∀ b ∈ (univ : Finset (ZMod p)).erase 0,
      ((β - algebraMap (ZMod p) (GaloisField p n) b) ^ ∑ σ : Fin n, p ^ (σ : ℕ)) ^ d =
        algebraMap (ZMod p) (GaloisField p n) ((((-1) ^ e * π.eval b) ^ (n / e)) ^ d) := by
    intro b _
    rw [← hρ, ← FiniteField.algebraMap_norm_eq_pow, algebraMap_norm_sub hn]
    simp only [map_pow]
    rfl
  rw [prod_congr rfl h1, ← map_prod]
  congr 1
  -- remove the signs
  simp only [chi, mul_pow, prod_mul_distrib]
  rw [prod_const, card_erase_of_mem (mem_univ _), card_univ, ZMod.card]
  have hsign : ((((-1 : ZMod p) ^ e) ^ (n / e)) ^ d) ^ (p - 1) = 1 := by
    have hm1 : ((-1 : ZMod p)) ^ (p - 1) = 1 :=
      ZMod.pow_card_sub_one_eq_one (neg_ne_zero.mpr (one_ne_zero (α := ZMod p)))
    rw [← pow_mul, ← pow_mul, ← pow_mul,
      show e * (n / e * (d * (p - 1))) = (p - 1) * (e * (n / e) * d) by ring, pow_mul, hm1, one_pow]
  rw [hsign, one_mul, ← prod_pow]
  refine prod_congr rfl fun b _ => ?_
  rw [← pow_mul, ← pow_mul, mul_comm]

theorem minpoly_mem_IrrDiv (hn : n ≠ 0) (β : GaloisField p n) :
    minpoly (ZMod p) β ∈ IrrDiv p n := by
  have hint : IsIntegral (ZMod p) β := Algebra.IsIntegral.isIntegral β
  exact mem_IrrDiv.mpr ⟨minpoly.monic hint, minpoly.irreducible hint,
    natDegree_minpoly_dvd hn β, hn⟩

/-- A monic irreducible `π` with `deg π ∣ n` is the minimal polynomial of exactly `deg π`
elements of `F_{p^n}`. -/
theorem card_filter_minpoly (hn : n ≠ 0) [Fintype (GaloisField p n)] {π : (ZMod p)[X]}
    (hπ : π ∈ IrrDiv p n) :
    ((univ : Finset (GaloisField p n)).filter (fun β => minpoly (ZMod p) β = π)).card =
      π.natDegree := by
  obtain ⟨hm, hirr, hdvd, -⟩ := mem_IrrDiv.mp hπ
  have hdvd' : π ∣ X ^ (p ^ n) - X := by
    have := (hirr.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X (n := n)).mp hdvd
    rwa [Nat.card_zmod] at this
  have hsplit : Splits (π.map (algebraMap (ZMod p) (GaloisField p n))) := by
    refine Splits.of_dvd ?_ ?_ (map_dvd (algebraMap _ (GaloisField p n)) hdvd')
    · exact SplittingField.splits (X ^ p ^ n - X : (ZMod p)[X])
    · exact map_ne_zero (FiniteField.X_pow_card_pow_sub_X_ne_zero _ hn hp.out.one_lt)
  have hsep : π.Separable := PerfectField.separable_of_irreducible hirr
  have hcard := card_rootSet_eq_natDegree (K := GaloisField p n) hsep hsplit
  rw [← hcard, ← Set.toFinset_card]
  congr 1
  ext β
  simp only [mem_filter, mem_univ, true_and, Set.mem_toFinset, mem_rootSet]
  constructor
  · rintro rfl
    exact ⟨hm.ne_zero, minpoly.aeval _ _⟩
  · rintro ⟨-, h⟩
    exact (minpoly.eq_of_irreducible_of_monic hirr h hm).symm

/-- **Step (c) of Lemma 2.3**: `s_n = ∑_{β ∈ F_{p^n}} Ψ_n(β)`. -/
theorem algebraMap_Ssum (hn : n ≠ 0) (d : ℕ) [Fintype (GaloisField p n)] :
    algebraMap (ZMod p) (GaloisField p n) (Ssum p d n) =
      ∑ β : GaloisField p n, (β ^ (p - 1) - 1) ^ (d * ∑ σ : Fin n, p ^ (σ : ℕ)) := by
  simp_rw [Psi_eq_chi hn d]
  rw [Ssum, map_sum]
  rw [← sum_fiberwise_of_maps_to (s := univ) (t := IrrDiv p n) (g := minpoly (ZMod p))
    (fun β _ => minpoly_mem_IrrDiv hn β)]
  refine sum_congr rfl fun π hπ => ?_
  rw [sum_congr rfl (fun β hβ => by rw [(mem_filter.mp hβ).2]), sum_const,
    card_filter_minpoly hn hπ, nsmul_eq_mul, map_mul, map_natCast]

end GF

end MO498708
