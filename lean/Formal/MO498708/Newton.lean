import Mathlib

/-!
# MO 498708, Lemma 2.3 step (e): from Newton's recursion to the closed form

If a sequence `a` with `a 0 = 1` satisfies `k a_k = ∑_{i<k} S_{k-i} a_i` for `1 ≤ k ≤ K`, where
`S_n = -∑_j γ_j^n` and `1, …, K` are invertible, then `a_k = (-1)^k e_k(γ)` for `k ≤ K`.
This replaces the comparison of logarithmic derivatives `uL'/L = uG'/G` in `F_p[[u]]`.
-/

open Finset MvPolynomial

namespace MO498708

variable {R : Type*} [CommRing R]

/-- Elementary symmetric function of the entries of a vector. -/
def esymmVal {m : ℕ} (γ : Fin m → R) (k : ℕ) : R :=
  ∑ t ∈ powersetCard k (univ : Finset (Fin m)), ∏ i ∈ t, γ i

theorem aeval_esymm {m : ℕ} (γ : Fin m → R) (k : ℕ) :
    aeval γ (esymm (Fin m) R k) = esymmVal γ k := by
  simp [esymm, esymmVal, map_sum, map_prod]

theorem aeval_psum {m : ℕ} (γ : Fin m → R) (k : ℕ) :
    aeval γ (psum (Fin m) R k) = ∑ j, γ j ^ k := by
  simp [psum, map_sum]

theorem esymmVal_zero {m : ℕ} (γ : Fin m → R) : esymmVal γ 0 = 1 := by
  simp [esymmVal]

theorem esymmVal_card {m : ℕ} (γ : Fin m → R) : esymmVal γ m = ∏ j, γ j := by
  have : powersetCard m (univ : Finset (Fin m)) = {univ} := by
    have := powersetCard_self (univ : Finset (Fin m))
    simpa using this
  simp [esymmVal, this]

/-- Newton's identities in the form `k b_k = ∑_{i<k} (-P_{k-i}) b_i`, `b_i = (-1)^i e_i`. -/
theorem newton_val {m : ℕ} (γ : Fin m → R) (k : ℕ) :
    (k : R) * ((-1) ^ k * esymmVal γ k) =
      ∑ i ∈ range k, (-(∑ j, γ j ^ (k - i))) * ((-1) ^ i * esymmVal γ i) := by
  have h := congrArg (aeval γ) (mul_esymm_eq_sum (Fin m) R k)
  simp only [map_mul, map_pow, map_neg, map_one, map_natCast, map_sum, aeval_esymm,
    aeval_psum] at h
  rw [sum_filter, Nat.sum_antidiagonal_eq_sum_range_succ_mk, sum_range_succ] at h
  simp only [lt_self_iff_false, ite_false, add_zero] at h
  rw [sum_congr rfl (fun i hi => if_pos (mem_range.mp hi))] at h
  rw [mul_left_comm, h, ← mul_assoc, ← pow_add]
  have hodd : Odd (k + (k + 1)) := ⟨k, by ring⟩
  rw [hodd.neg_one_pow, neg_one_mul, ← sum_neg_distrib]
  refine sum_congr rfl fun i _ => ?_
  ring

/-- Uniqueness of solutions of Newton's recursion as long as `1, …, K` are invertible. -/
theorem newton_rec_unique {F : Type*} [Field F] (K : ℕ)
    (hK : ∀ k, 1 ≤ k → k ≤ K → (k : F) ≠ 0) (S a b : ℕ → F) (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (ha : ∀ k, 1 ≤ k → k ≤ K → (k : F) * a k = ∑ i ∈ range k, S (k - i) * a i)
    (hb : ∀ k, 1 ≤ k → k ≤ K → (k : F) * b k = ∑ i ∈ range k, S (k - i) * b i) :
    ∀ k, k ≤ K → a k = b k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · rw [ha0, hb0]
    · have e1 := ha k hpos hk
      have e2 := hb k hpos hk
      have : ∑ i ∈ range k, S (k - i) * a i = ∑ i ∈ range k, S (k - i) * b i :=
        sum_congr rfl fun i hi => by rw [ih i (mem_range.mp hi) (by have := mem_range.mp hi; omega)]
      rw [this, ← e2] at e1
      exact mul_left_cancel₀ (hK k hpos hk) e1

/-- **Closed form from Newton's recursion.** -/
theorem eq_of_newton {F : Type*} [Field F] {m : ℕ} (γ : Fin m → F) (K : ℕ)
    (hK : ∀ k, 1 ≤ k → k ≤ K → (k : F) ≠ 0) (a : ℕ → F) (ha0 : a 0 = 1)
    (ha : ∀ k, 1 ≤ k → k ≤ K →
      (k : F) * a k = ∑ i ∈ range k, (-(∑ j, γ j ^ (k - i))) * a i) :
    ∀ k, k ≤ K → a k = (-1) ^ k * esymmVal γ k :=
  newton_rec_unique K hK (fun n => -(∑ j, γ j ^ n)) a (fun k => (-1) ^ k * esymmVal γ k) ha0
    (by simp [esymmVal_zero]) ha (fun k _ _ => newton_val γ k)

end MO498708
