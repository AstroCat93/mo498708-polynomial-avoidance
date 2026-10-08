import Mathlib

/-!
# MO 498708, Lemma 2.3 step (d): the power sum `s_n` over `F_{p^n}`

For a finite field `L` of characteristic `p` with `p ^ n` elements (`n ≥ 1`) and `d ≤ p - 1`,

  `∑_{β ∈ L} (β^{p-1} - 1)^{d ρ} = - ∑_{t=1}^{d} ((-1)^{d-t} * C(d,t))^n`,   `ρ = ∑_{σ<n} p^σ`.

(`(β^{p-1}-1)^{dρ} = ∏_{σ<n} (β^{(p-1)p^σ} - 1)^d` is the quantity `Ψ_n(β)` of the write-up.)
-/

open Finset

namespace MO498708

section PowerSums

variable {L : Type*} [Field L] [Fintype L]

/-- Power sums over a finite field (Fact 1.1). -/
theorem sum_pow_eq_ite (m : ℕ) :
    ∑ x : L, x ^ m = if m ≠ 0 ∧ (Fintype.card L - 1) ∣ m then -1 else 0 := by
  classical
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · have h1 : ∑ x : L, x ^ m = ∑ x : Lˣ, ((x : L) ^ m) := by
      have h2 : ∑ x : Lˣ, ((x : L) ^ m) = ∑ x ∈ (univ : Finset L).filter (· ≠ 0), x ^ m := by
        refine Finset.sum_bij' (fun u _ => (u : L)) (fun x hx => Units.mk0 x (by simpa using hx))
          ?_ ?_ ?_ ?_ ?_ <;> simp
      rw [h2, Finset.sum_filter_of_ne]
      intro x _ hx
      rintro rfl
      exact hx (zero_pow hm.ne')
    rw [h1, FiniteField.sum_pow_units]
    simp [hm.ne']

end PowerSums

/-- Uniqueness of base-`p` digits, in the special form needed: if `∑ k_σ p^σ = t ∑ p^σ` with all
digits `< p`, then every `k_σ = t`. -/
theorem digits_eq_const {p : ℕ} (hp : 0 < p) :
    ∀ (n : ℕ) (k : Fin n → ℕ) (t : ℕ), (∀ σ, k σ < p) → t < p →
      ∑ σ : Fin n, k σ * p ^ (σ : ℕ) = t * ∑ σ : Fin n, p ^ (σ : ℕ) → ∀ σ, k σ = t
  | 0, _, _, _, _, _ => fun σ => σ.elim0
  | n + 1, k, t, hk, ht, h => by
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at h
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ] at h
    have h' : k 0 + p * ∑ σ : Fin n, k σ.succ * p ^ (σ : ℕ)
        = t + p * (t * ∑ σ : Fin n, p ^ (σ : ℕ)) := by
      rw [mul_sum, mul_sum, mul_sum]
      rw [mul_add, mul_one, mul_sum] at h
      convert h using 2 <;> refine sum_congr rfl fun σ _ => by ring
    have h0 : k 0 = t := by
      have := congrArg (· % p) h'
      simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hk 0), Nat.mod_eq_of_lt ht] at this
      exact this
    have hrest : ∑ σ : Fin n, k σ.succ * p ^ (σ : ℕ) = t * ∑ σ : Fin n, p ^ (σ : ℕ) := by
      rw [h0] at h'
      exact Nat.eq_of_mul_eq_mul_left hp (Nat.add_left_cancel h')
    intro σ
    refine Fin.cases h0 (fun σ => ?_) σ
    exact digits_eq_const hp n (fun σ => k σ.succ) t (fun σ => hk _) ht hrest σ

/-- `p^n - 1 = (p - 1) * ∑_{σ<n} p^σ`. -/
theorem pow_sub_one_eq (p n : ℕ) (hp : 1 ≤ p) :
    p ^ n - 1 = (p - 1) * ∑ σ : Fin n, p ^ (σ : ℕ) := by
  have h := geom_sum_mul (p : ℤ) n
  rw [← Fin.sum_univ_eq_sum_range] at h
  have h1 : 1 ≤ p ^ n := Nat.one_le_pow _ _ hp
  zify [h1, hp]
  rw [← h, mul_comm]

section Main

variable {L : Type*} [Field L] (p : ℕ) [Fact p.Prime] [CharP L p]

/-- `c_t = (-1)^{d-t} C(d,t)`, the coefficients of `(z-1)^d = ∑_t c_t z^t`. -/
def coeffC (R : Type*) [Ring R] (d : ℕ) (t : ℕ) : R := (-1) ^ (d - t) * (d.choose t : R)

theorem sub_one_pow_eq (R : Type*) [CommRing R] (d : ℕ) (z : R) :
    (z - 1) ^ d = ∑ t : Fin (d + 1), coeffC R d t * z ^ (t : ℕ) := by
  rw [sub_eq_add_neg, add_pow, ← Fin.sum_univ_eq_sum_range]
  refine sum_congr rfl fun t _ => ?_
  simp only [coeffC]
  ring

/-- Expansion of `Ψ_n` as a sum over digit vectors. -/
theorem Psi_expand (n : ℕ) (d : ℕ) (y : L) :
    (y - 1) ^ (d * ∑ σ : Fin n, p ^ (σ : ℕ)) =
      ∑ k : Fin n → Fin (d + 1), (∏ σ, coeffC L d (k σ)) *
        y ^ (∑ σ, (k σ : ℕ) * p ^ (σ : ℕ)) := by
  rw [mul_sum, ← prod_pow_eq_pow_sum]
  have h1 : ∀ σ : Fin n, (y - 1) ^ (d * p ^ (σ : ℕ)) =
      ∑ t : Fin (d + 1), coeffC L d t * (y ^ p ^ (σ : ℕ)) ^ (t : ℕ) := by
    intro σ
    rw [mul_comm, pow_mul, sub_pow_char_pow, one_pow, sub_one_pow_eq]
  simp_rw [h1]
  rw [Fintype.prod_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [prod_mul_distrib, ← prod_pow_eq_pow_sum]
  congr 1
  refine prod_congr rfl fun σ _ => ?_
  rw [← pow_mul, mul_comm]

/-- **Step (d) of Lemma 2.3.** -/
theorem sum_Psi [Fintype L] (n : ℕ) (hn : 1 ≤ n) (hcard : Fintype.card L = p ^ n) (d : ℕ)
    (hd : d ≤ p - 1) :
    ∑ β : L, (β ^ (p - 1) - 1) ^ (d * ∑ σ : Fin n, p ^ (σ : ℕ)) =
      -∑ t ∈ Icc 1 d, (coeffC L d t) ^ n := by
  classical
  have hp := (Fact.out : p.Prime)
  have hp1 : 1 ≤ p := hp.one_lt.le
  set ρ := ∑ σ : Fin n, p ^ (σ : ℕ) with hρ
  have hρpos : 0 < ρ := by
    have : (⟨0, hn⟩ : Fin n) ∈ (univ : Finset (Fin n)) := mem_univ _
    exact lt_of_lt_of_le (by simp) (single_le_sum (fun _ _ => Nat.zero_le _) this)
  have hq : Fintype.card L - 1 = (p - 1) * ρ := by rw [hcard, pow_sub_one_eq p n hp1]
  -- expand and swap the sums
  simp_rw [hρ] at hq ⊢
  simp_rw [Psi_expand p n d, ← pow_mul]
  rw [sum_comm]
  simp_rw [← mul_sum, sum_pow_eq_ite, hq, ← hρ]
  -- the summand for a digit vector `k`
  set F : (Fin n → Fin (d + 1)) → L := fun k => (∏ σ, coeffC L d (k σ)) *
    (if (p - 1) * ∑ σ, (k σ : ℕ) * p ^ (σ : ℕ) ≠ 0 ∧
      (p - 1) * ρ ∣ (p - 1) * ∑ σ, (k σ : ℕ) * p ^ (σ : ℕ) then -1 else 0) with hF
  change ∑ k, F k = _
  let cst : Fin (d + 1) → (Fin n → Fin (d + 1)) := fun t _ => t
  have hcst_inj : Function.Injective cst := by
    intro a b hab
    have := congrFun hab ⟨0, hn⟩
    simpa [cst] using this
  -- `F` vanishes off constant digit vectors
  have hvan : ∀ k ∈ (univ : Finset (Fin n → Fin (d + 1))), k ∉ univ.image cst → F k = 0 := by
    intro k _ hk
    simp only [hF]
    rw [ite_eq_right_iff.mpr, mul_zero]
    rintro ⟨hne, hdvd⟩
    exfalso
    apply hk
    have hp0 : 0 < p - 1 := by have := hp.two_le; omega
    obtain ⟨t, ht⟩ := (Nat.dvd_of_mul_dvd_mul_left hp0 hdvd)
    have hle : ∑ σ, (k σ : ℕ) * p ^ (σ : ℕ) ≤ d * ρ := by
      rw [hρ, mul_sum]
      exact sum_le_sum fun σ _ => Nat.mul_le_mul_right _ (Nat.lt_succ_iff.mp (k σ).isLt)
    have htd : t ≤ d := by
      rw [ht, mul_comm] at hle
      exact Nat.le_of_mul_le_mul_right hle hρpos
    have hall := digits_eq_const (p := p) hp.pos n (fun σ => (k σ : ℕ)) t
      (fun σ => by have := (k σ).isLt; omega) (by omega) (by rw [ht, mul_comm])
    refine mem_image.mpr ⟨⟨t, by omega⟩, mem_univ _, ?_⟩
    funext σ
    exact Fin.ext (hall σ).symm
  rw [← sum_subset (subset_univ _) hvan, sum_image (fun a _ b _ h => hcst_inj h)]
  -- evaluate on constant vectors
  have hconst : ∀ t : Fin (d + 1), F (cst t) =
      if (t : ℕ) ≠ 0 then -(coeffC L d t) ^ n else 0 := by
    intro t
    simp only [hF, cst, prod_const, card_univ, Fintype.card_fin]
    have hsum : ∑ σ : Fin n, (t : ℕ) * p ^ (σ : ℕ) = t * ρ := by rw [hρ, mul_sum]
    rw [hsum]
    by_cases ht : (t : ℕ) = 0
    · simp [ht]
    · have hp0 : 0 < p - 1 := by have := hp.two_le; omega
      rw [if_pos ⟨by positivity, ⟨t, by ring⟩⟩, if_pos ht]
      ring
  simp_rw [hconst]
  rw [sum_ite, sum_const_zero, add_zero, sum_neg_distrib]
  congr 1
  refine sum_nbij' (fun t => (t : ℕ)) (fun t => (⟨min t d, by omega⟩ : Fin (d + 1)))
    ?_ ?_ ?_ ?_ ?_
  · intro t ht
    simp only [mem_filter, mem_univ, true_and] at ht
    simp only [mem_Icc]
    have := t.isLt
    omega
  · intro t ht
    simp only [mem_Icc] at ht
    simp only [mem_filter, mem_univ, true_and]
    simp only [ne_eq]
    omega
  · intro t ht
    apply Fin.ext
    simp only
    have := t.isLt
    omega
  · intro t ht
    simp only [mem_Icc] at ht
    simp only
    omega
  · intro t _
    rfl

end Main

end MO498708
