import Mathlib

/-!
# MO 498708, Lemma 2.1: reduction of Theorem 1 to the non-vanishing of one invariant

For `c : Fin (d+1) → ZMod p` let `fc c i = ∑ j, c j * i ^ j` (the value at `i` of the
polynomial with coefficient vector `c`).  We define

  `Cinv p d = ∑_{c ∈ F_p^{d+1}} c_0^{p-1-d} * ∏_{i ∈ F_p} (fc c i)^d`.

This is `(-1)^(d+1) * C(p,d)` where `C(p,d)` is the Nullstellensatz coefficient of the write-up
(Lemma 2.1 there, applied to the top homogeneous part `H`).  The main result of this file is

  `theorem1_of_Cinv_ne_zero : Cinv p d ≠ 0 → (Theorem 1 for (p,d))`.

The proof follows Lemma 2.1: for a family of `d`-sets `B i`, the weighted sum
`∑_c c_0^{p-1-d} ∏_i ∏_{a ∈ B i} (fc c i - a)` does not depend on the family, because the
difference with `Cinv p d` is the sum over `F_p^{d+1}` of a polynomial of total degree
`< (p-1)(d+1)` (Chevalley–Warning lemma `MvPolynomial.sum_eval_eq_zero`).
-/

open Finset MvPolynomial

namespace MO498708

variable {p : ℕ} [hp : Fact p.Prime]

/-- Value at `i` of the polynomial with coefficient vector `c`. -/
def fc {d : ℕ} (c : Fin (d + 1) → ZMod p) (i : ZMod p) : ZMod p :=
  ∑ j : Fin (d + 1), c j * i ^ (j : ℕ)

variable (p) in
/-- The invariant `∑_c c_0^{p-1-d} ∏_i f_c(i)^d`. -/
def Cinv (d : ℕ) : ZMod p :=
  ∑ c : Fin (d + 1) → ZMod p, c 0 ^ (p - 1 - d) * ∏ i : ZMod p, fc c i ^ d

section degree

variable {σ ι R : Type*} [CommRing R]

/-- `∏ (L_k - a_k) - ∏ L_k` has total degree `≤ #s - 1` when every `L_k` has degree `≤ 1`. -/
theorem totalDegree_prod_sub_prod_le (s : Finset ι) (L : ι → MvPolynomial σ R) (a : ι → R)
    (hL : ∀ k ∈ s, (L k).totalDegree ≤ 1) :
    (∏ k ∈ s, (L k - C (a k)) - ∏ k ∈ s, L k).totalDegree ≤ #s - 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert k s hk ih =>
    have hL' : ∀ k ∈ s, (L k).totalDegree ≤ 1 := fun j hj => hL j (mem_insert_of_mem hj)
    have ih := ih hL'
    have hLk : (L k).totalDegree ≤ 1 := hL k (mem_insert_self k s)
    have hH : (∏ k ∈ s, L k).totalDegree ≤ #s := by
      refine (totalDegree_finsetProd _ _).trans ?_
      calc ∑ j ∈ s, (L j).totalDegree ≤ ∑ _j ∈ s, 1 := sum_le_sum hL'
        _ = #s := by simp
    have hLa : (L k - C (a k)).totalDegree ≤ 1 := by
      refine (totalDegree_sub _ _).trans ?_
      simp [totalDegree_C, hLk]
    rw [prod_insert hk, prod_insert hk, card_insert_of_notMem hk, Nat.add_sub_cancel]
    have key : (L k - C (a k)) * ∏ x ∈ s, (L x - C (a x)) - L k * ∏ x ∈ s, L x
        = (L k - C (a k)) * (∏ x ∈ s, (L x - C (a x)) - ∏ x ∈ s, L x)
          - C (a k) * ∏ x ∈ s, L x := by ring
    rw [key]
    refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
    · rcases Nat.eq_zero_or_pos #s with h0 | hpos
      · rw [card_eq_zero] at h0
        subst h0
        simp
      · refine (totalDegree_mul _ _).trans ?_
        omega
    · refine (totalDegree_mul _ _).trans ?_
      simp [totalDegree_C, hH]

end degree

/-- The linear form `c ↦ fc c i` as a multivariate polynomial. -/
noncomputable def linForm (d : ℕ) (i : ZMod p) : MvPolynomial (Fin (d + 1)) (ZMod p) :=
  ∑ j : Fin (d + 1), X j * C (i ^ (j : ℕ))

theorem eval_linForm {d : ℕ} (c : Fin (d + 1) → ZMod p) (i : ZMod p) :
    eval c (linForm d i) = fc c i := by
  simp [linForm, fc]

theorem totalDegree_linForm (d : ℕ) (i : ZMod p) : (linForm d i).totalDegree ≤ 1 := by
  unfold linForm
  refine (totalDegree_finsetSum _ _).trans ?_
  refine Finset.sup_le fun j _ => ?_
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C]
  simp [totalDegree_X]

/-- **Lemma 2.1** (weighted count is independent of the family). -/
theorem weighted_sum_eq_Cinv (d : ℕ) (hd1 : 1 ≤ d) (hd : d ≤ p - 1)
    (B : ZMod p → Finset (ZMod p)) (hB : ∀ i, #(B i) = d) :
    ∑ c : Fin (d + 1) → ZMod p, c 0 ^ (p - 1 - d) * ∏ i, ∏ a ∈ B i, (fc c i - a) = Cinv p d := by
  classical
  have hp2 := hp.out.two_le
  set s : Finset (Σ _ : ZMod p, ZMod p) := univ.sigma B with hs
  have hscard : #s = p * d := by
    rw [hs, card_sigma]
    simp [hB, ZMod.card]
  set Q : MvPolynomial (Fin (d + 1)) (ZMod p) :=
    X 0 ^ (p - 1 - d) * (∏ x ∈ s, (linForm d x.1 - C x.2) - ∏ x ∈ s, linForm d x.1) with hQ
  have hdeg : Q.totalDegree < (Fintype.card (ZMod p) - 1) * Fintype.card (Fin (d + 1)) := by
    have h1 := totalDegree_prod_sub_prod_le s (fun x => linForm d x.1) (fun x => x.2)
      (fun x _ => totalDegree_linForm d x.1)
    have h2 : Q.totalDegree ≤ (p - 1 - d) + (p * d - 1) := by
      refine (totalDegree_mul _ _).trans (add_le_add ?_ ?_)
      · refine (totalDegree_pow _ _).trans ?_
        simp [totalDegree_X]
      · simpa [hscard] using h1
    refine lt_of_le_of_lt h2 ?_
    rw [ZMod.card, Fintype.card_fin]
    obtain ⟨e, he⟩ : ∃ e, p - 1 = d + e := ⟨p - 1 - d, by omega⟩
    have hp' : p = d + e + 1 := by omega
    subst hp'
    simp only [Nat.add_sub_cancel]
    have : (d + e + 1) * d = (d + e) * d + d := by ring
    rw [this]
    have : (d + e) * (d + 1) = (d + e) * d + (d + e) := by ring
    rw [this]
    omega
  have hsum := MvPolynomial.sum_eval_eq_zero Q hdeg
  have heval : ∀ c : Fin (d + 1) → ZMod p, eval c Q =
      c 0 ^ (p - 1 - d) * ∏ i, ∏ a ∈ B i, (fc c i - a)
        - c 0 ^ (p - 1 - d) * ∏ i, fc c i ^ d := by
    intro c
    simp only [hQ, map_mul, map_sub, map_pow, eval_X, map_prod, eval_C, eval_linForm]
    rw [hs, prod_sigma, prod_sigma, mul_sub]
    congr 2
    refine prod_congr rfl fun i _ => ?_
    simp [hB]
  simp only [heval, sum_sub_distrib] at hsum
  rw [Cinv]
  exact sub_eq_zero.mp hsum

/-- The polynomial with coefficient vector `c`. -/
noncomputable def polyOf {d : ℕ} (c : Fin (d + 1) → ZMod p) : Polynomial (ZMod p) :=
  ∑ j : Fin (d + 1), Polynomial.C (c j) * Polynomial.X ^ (j : ℕ)

theorem natDegree_polyOf_le {d : ℕ} (c : Fin (d + 1) → ZMod p) : (polyOf c).natDegree ≤ d := by
  unfold polyOf
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
  exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.mp j.isLt)

theorem eval_polyOf {d : ℕ} (c : Fin (d + 1) → ZMod p) (i : ZMod p) :
    (polyOf c).eval i = fc c i := by
  simp [polyOf, fc, Polynomial.eval_finsetSum]

/-- **Theorem 1 from `Cinv p d ≠ 0`** (Lemma 2.1 of the write-up). -/
theorem theorem1_of_Cinv_ne_zero (d : ℕ) (hd : d ≤ p - 1) (hC : Cinv p d ≠ 0)
    (A : ZMod p → Finset (ZMod p)) (hA : ∀ i, #(A i) ≤ d) :
    ∃ f : Polynomial (ZMod p), f.natDegree ≤ d ∧ ∀ i, f.eval i ∉ A i := by
  classical
  have hp2 := hp.out.two_le
  rcases Nat.eq_zero_or_pos d with hd0 | hd1
  · subst hd0
    refine ⟨0, by simp, fun i => ?_⟩
    have := hA i
    simp_all
  -- pad every `A i` to a `d`-set
  have hpad : ∀ i, ∃ B : Finset (ZMod p), A i ⊆ B ∧ #B = d := by
    intro i
    obtain ⟨B, h1, -, h3⟩ := exists_subsuperset_card_eq (subset_univ (A i)) (hA i)
      (by rw [card_univ, ZMod.card]; omega)
    exact ⟨B, h1, h3⟩
  choose B hAB hB using hpad
  by_contra hno
  push Not at hno
  apply hC
  rw [← weighted_sum_eq_Cinv d hd1 hd B hB]
  refine sum_eq_zero fun c _ => ?_
  obtain ⟨i, hi⟩ := hno (polyOf c) (natDegree_polyOf_le c)
  rw [eval_polyOf] at hi
  have : ∏ a ∈ B i, (fc c i - a) = 0 := prod_eq_zero (hAB i hi) (sub_self _)
  rw [prod_eq_zero (mem_univ i) this, mul_zero]

end MO498708
