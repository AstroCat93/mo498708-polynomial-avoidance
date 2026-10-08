import Formal.MO498708.Reduction
import Formal.MO498708.CinvAd
import Formal.MO498708.Galois
import Formal.MO498708.Newton

/-!
# MO 498708: Theorems 1 and 2

* `MO498708.theorem2_Asum` : `A_d = ∑_{F monic, deg F = d} ∏_{b ≠ 0} F(b)^d
                              = (-1)^{d(d+1)/2} ∏_{k=0}^{d} C(d,k)` in `F_p`, for `d ≤ p - 1`;
* `MO498708.Cinv_ne_zero`  : the Nullstellensatz invariant `Cinv p d` is nonzero;
* `MO498708.theorem1`      : for every prime `p`, every `d ≤ p - 1` and every family
  `A : ZMod p → Finset (ZMod p)` with `#(A i) ≤ d`, some `f` with `natDegree f ≤ d` satisfies
  `f(i) ∉ A i` for all `i`.
-/

open Finset Polynomial

namespace MO498708

open scoped Classical

variable {p : ℕ} [hp : Fact p.Prime]

/-- `s_n = -∑_{t=1}^{d} γ_t^n` for `1 ≤ n` (steps (c)–(d) of Lemma 2.3). -/
theorem Ssum_eq (d : ℕ) (hd : d ≤ p - 1) (n : ℕ) (hn : 1 ≤ n) :
    Ssum p d n = -∑ t ∈ Icc 1 d, (coeffC (ZMod p) d t) ^ n := by
  letI := Fintype.ofFinite (GaloisField p n)
  have hn0 : n ≠ 0 := by omega
  have hcard : Fintype.card (GaloisField p n) = p ^ n := by
    rw [Fintype.card_eq_nat_card, GaloisField.card p n hn0]
  apply (algebraMap (ZMod p) (GaloisField p n)).injective
  rw [algebraMap_Ssum hn0 d, sum_Psi p n hn hcard d hd]
  simp [coeffC, map_sum, map_neg, map_pow, map_mul, map_natCast]

theorem sum_Icc_eq_sum_fin {M : Type*} [AddCommMonoid M] (d : ℕ) (f : ℕ → M) :
    ∑ t ∈ Icc 1 d, f t = ∑ j : Fin d, f (j + 1) := by
  rw [Fin.sum_univ_eq_sum_range (fun j => f (j + 1))]
  refine sum_nbij' (fun t => t - 1) (fun j => j + 1) ?_ ?_ ?_ ?_ ?_
  · intro t ht
    simp only [mem_Icc] at ht
    simp only [mem_range]
    omega
  · intro j hj
    simp only [mem_range] at hj
    simp only [mem_Icc]
    omega
  · intro t ht
    simp only [mem_Icc] at ht
    omega
  · intro j _
    omega
  · intro t ht
    simp only [mem_Icc] at ht
    rw [Nat.sub_add_cancel ht.1]

theorem natCast_ne_zero_of_lt {k : ℕ} (hk1 : 1 ≤ k) (hkp : k < p) : (k : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro h
  exact absurd (Nat.le_of_dvd (by omega) h) (by omega)

/-- **Theorem 2** (form with `γ_t`): `A_d = (-1)^d ∏_{t=1}^d γ_t`, `γ_t = (-1)^{d-t} C(d,t)`. -/
theorem Asum_eq (d : ℕ) (hd : d ≤ p - 1) :
    Asum p d d = (-1) ^ d * ∏ j : Fin d, coeffC (ZMod p) d (j + 1) := by
  have hp1 := hp.out.one_lt
  set γ : Fin d → ZMod p := fun j => coeffC (ZMod p) d (j + 1) with hγ
  have hsumγ : ∀ m, ∑ j, γ j ^ m = ∑ t ∈ Icc 1 d, coeffC (ZMod p) d t ^ m := by
    intro m
    rw [sum_Icc_eq_sum_fin d (fun t => coeffC (ZMod p) d t ^ m)]
  have key := eq_of_newton γ d (fun k hk1 hkd => natCast_ne_zero_of_lt hk1 (by omega))
    (fun k => Asum p d k) (Asum_zero d) (by
      intro k hk1 hkd
      rw [newton_Asum d k]
      refine sum_congr rfl fun i hi => ?_
      have hi' := mem_range.mp hi
      rw [Ssum_eq d hd (k - i) (by omega), hsumγ]) d le_rfl
  rw [key, esymmVal_card]

/-- **Theorem 2, "moreover" part**: for all `0 ≤ k ≤ p - 1`,
`A_k = ∑_{F monic, deg F = k} N(F)^d = (-1)^k e_k(γ_1, …, γ_d) = [u^k] ∏_{t=1}^d (1 - γ_t u)`. -/
theorem Asum_eq_esymm (d : ℕ) (hd : d ≤ p - 1) (k : ℕ) (hk : k ≤ p - 1) :
    Asum p d k = (-1) ^ k * esymmVal (fun j : Fin d => coeffC (ZMod p) d (j + 1)) k := by
  have hp1 := hp.out.one_lt
  set γ : Fin d → ZMod p := fun j => coeffC (ZMod p) d (j + 1) with hγ
  have hsumγ : ∀ m, ∑ j, γ j ^ m = ∑ t ∈ Icc 1 d, coeffC (ZMod p) d t ^ m := by
    intro m
    rw [sum_Icc_eq_sum_fin d (fun t => coeffC (ZMod p) d t ^ m)]
  exact eq_of_newton γ (p - 1) (fun k hk1 hkd => natCast_ne_zero_of_lt hk1 (by omega))
    (fun k => Asum p d k) (Asum_zero d) (by
      intro k hk1 hkd
      rw [newton_Asum d k]
      refine sum_congr rfl fun i hi => ?_
      have hi' := mem_range.mp hi
      rw [Ssum_eq d hd (k - i) (by omega), hsumγ]) k hk

/-- In particular `∑_{F monic, deg F = k} N(F)^d = 0` for `d < k ≤ p - 1`. -/
theorem Asum_eq_zero (d : ℕ) (hd : d ≤ p - 1) (k : ℕ) (hdk : d < k) (hk : k ≤ p - 1) :
    Asum p d k = 0 := by
  rw [Asum_eq_esymm d hd k hk, esymmVal]
  have : powersetCard k (univ : Finset (Fin d)) = ∅ := by
    rw [powersetCard_eq_empty, card_univ, Fintype.card_fin]
    exact hdk
  rw [this, sum_empty, mul_zero]

theorem coeffC_ne_zero (d : ℕ) (hd : d ≤ p - 1) (t : ℕ) (ht : t ≤ d) :
    coeffC (ZMod p) d t ≠ 0 := by
  have hp1 := hp.out.one_lt
  unfold coeffC
  refine mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) ?_
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro h
  have h1 : p ∣ d.factorial := by
    rw [← Nat.choose_mul_factorial_mul_factorial ht]
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_right h _) _
  rw [hp.out.dvd_factorial] at h1
  omega

/-- Sign bookkeeping: `(-1)^d ∏_{t=1}^d γ_t = (-1)^{d(d+1)/2} ∏_{k=0}^d C(d,k)`. -/
theorem sign_prod_coeffC (d : ℕ) :
    (-1) ^ d * ∏ j : Fin d, coeffC (ZMod p) d (j + 1) =
      (-1) ^ (d * (d + 1) / 2) * ∏ k ∈ range (d + 1), (d.choose k : ZMod p) := by
  simp only [coeffC, prod_mul_distrib, prod_pow_eq_pow_sum]
  rw [prod_range_succ', Nat.choose_zero_right, Nat.cast_one, mul_one,
    ← Fin.prod_univ_eq_prod_range (fun k => (d.choose (k + 1) : ZMod p)), ← mul_assoc, ← pow_add]
  congr 2
  -- the exponent: `d + ∑_{j<d} (d - (j+1)) = d(d+1)/2`
  rw [Fin.sum_univ_eq_sum_range (fun j => d - (j + 1)) d]
  have hS : ∑ j ∈ range d, (d - (j + 1)) = ∑ j ∈ range d, j := by
    rw [← sum_range_reflect (fun j => j) d]
    exact sum_congr rfl fun j _ => by omega
  have h2 := sum_range_id_mul_two d
  rw [hS]
  symm
  apply Nat.div_eq_of_eq_mul_left (by norm_num)
  rw [add_mul, h2]
  rcases d with _ | e
  · simp
  · simp only [Nat.add_sub_cancel]
    ring

/-- **Theorem 2** (closed form): for `d ≤ p - 1`,
`∑_{F monic, deg F = d} N(F)^d = (-1)^{d(d+1)/2} ∏_{k=0}^d C(d,k)` in `F_p`. -/
theorem theorem2_Asum (d : ℕ) (hd : d ≤ p - 1) :
    Asum p d d = (-1) ^ (d * (d + 1) / 2) * ∏ k ∈ range (d + 1), (d.choose k : ZMod p) := by
  rw [Asum_eq d hd, sign_prod_coeffC]

/-- The invariant `Cinv p d = ∑_c c_0^{p-1-d} ∏_i f_c(i)^d` in closed form. -/
theorem Cinv_eq (d : ℕ) (hd : d ≤ p - 1) :
    Cinv p d = (-1) ^ (d + 1) *
      ((-1) ^ (d * (d + 1) / 2) * ∏ k ∈ range (d + 1), (d.choose k : ZMod p)) := by
  rw [Cinv_eq_Asum d hd, theorem2_Asum d hd]

/-- **Theorem 2** (non-vanishing). -/
theorem Cinv_ne_zero (d : ℕ) (hd : d ≤ p - 1) : Cinv p d ≠ 0 := by
  rw [Cinv_eq_Asum d hd, Asum_eq d hd]
  refine mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
    (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) ?_)
  rw [prod_ne_zero_iff]
  intro j _
  exact coeffC_ne_zero d hd _ (by have := j.isLt; omega)

end MO498708

/-- **Theorem 1 (MO 498708, question (Q1)).** For every prime `p`, every `0 ≤ d ≤ p - 1` and every
family of sets `A i ⊆ F_p` (`i ∈ F_p`) with `#(A i) ≤ d`, there is a polynomial `f ∈ F_p[x]` with
`natDegree f ≤ d` (this includes `f = 0`) such that `f(i) ∉ A i` for every `i`. -/
theorem MO498708.theorem1 (p : ℕ) [Fact p.Prime] (d : ℕ) (hd : d ≤ p - 1)
    (A : ZMod p → Finset (ZMod p)) (hA : ∀ i, (A i).card ≤ d) :
    ∃ f : Polynomial (ZMod p), f.natDegree ≤ d ∧ ∀ i, f.eval i ∉ A i :=
  MO498708.theorem1_of_Cinv_ne_zero d hd (MO498708.Cinv_ne_zero d hd) A hA

#print axioms MO498708.theorem1
#print axioms MO498708.theorem2_Asum
