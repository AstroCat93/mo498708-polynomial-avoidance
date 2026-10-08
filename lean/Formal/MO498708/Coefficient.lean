import Formal.MO498708.Main

/-!
# MO 498708: the Nullstellensatz coefficient `C(p,d)` itself

Let `H = ∏_{i ∈ F_p} (∑_{j ≤ d} c_j i^j)^d ∈ F_p[c_0, …, c_d]` and
`C(p,d) = [c_0^d c_1^{p-1} ⋯ c_d^{p-1}] H`.  Using Corollary 1.2 of the write-up
(`∑_{y ∈ K^m} Q(y) = (-1)^m [y_1^{q-1} ⋯ y_m^{q-1}] Q` when `deg Q ≤ m (q-1)`), we show
`Cinv p d = (-1)^(d+1) C(p,d)`, hence **Theorem 2** in its original form:

  `C(p,d) = (-1)^{d(d+1)/2} ∏_{k=0}^{d} C(d,k) ≠ 0` in `F_p`.
-/

open Finset MvPolynomial

namespace MO498708

open scoped Classical

section Cor12

variable {K : Type*} [Field K] [Fintype K] {m : ℕ}

/-- **Corollary 1.2**: for `deg Q ≤ m (q - 1)`, `∑_{y ∈ K^m} Q(y) = (-1)^m [∏ y_j^{q-1}] Q`. -/
theorem sum_eval_eq_coeff (Q : MvPolynomial (Fin m) K)
    (hQ : Q.totalDegree ≤ m * (Fintype.card K - 1)) :
    ∑ x : Fin m → K, eval x Q =
      (-1) ^ m * Q.coeff (Finsupp.equivFunOnFinite.symm fun _ => Fintype.card K - 1) := by
  set q := Fintype.card K with hq
  have hq2 : 2 ≤ q := Fintype.one_lt_card
  set E : Fin m →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ => q - 1 with hE
  simp_rw [eval_eq']
  rw [sum_comm]
  simp_rw [← mul_sum]
  have hterm : ∀ e ∈ Q.support, (∑ x : Fin m → K, ∏ i, x i ^ e i) =
      if e = E then (-1) ^ m else 0 := by
    intro e he
    rw [← Fintype.prod_sum (fun i y => y ^ e i)]
    simp_rw [sum_pow_eq_ite]
    have hdeg : ∑ i, e i ≤ m * (q - 1) := by
      have := le_totalDegree he
      rw [Finsupp.sum_fintype _ _ (by simp)] at this
      omega
    by_cases hall : ∀ i, e i ≠ 0 ∧ (q - 1) ∣ e i
    · have hge : ∀ i, q - 1 ≤ e i := fun i =>
        Nat.le_of_dvd (Nat.pos_of_ne_zero (hall i).1) (hall i).2
      have heq : ∀ i, e i = q - 1 := by
        intro i
        by_contra hne
        have hlt : q - 1 < e i := lt_of_le_of_ne (hge i) (Ne.symm hne)
        have : m * (q - 1) < ∑ i, e i := by
          calc m * (q - 1) = ∑ _j : Fin m, (q - 1) := by simp
            _ < ∑ j, e j := sum_lt_sum (fun j _ => hge j) ⟨i, mem_univ _, hlt⟩
        omega
      have heE : e = E := by
        ext i
        simp [hE, heq i]
      rw [if_pos heE, prod_congr rfl (fun i _ => if_pos (hall i))]
      simp
    · push Not at hall
      obtain ⟨i, hi⟩ := hall
      have hne : e ≠ E := by
        rintro rfl
        apply hi
        · simp [hE]
          omega
        · simp [hE]
      rw [if_neg hne]
      refine prod_eq_zero (mem_univ i) ?_
      rw [if_neg]
      rintro ⟨h1, h2⟩
      exact hi h1 h2
  rw [sum_congr rfl fun e he => by rw [hterm e he]]
  simp_rw [mul_ite, mul_zero]
  rw [sum_ite_eq']
  split_ifs with hmem
  · ring
  · rw [notMem_support_iff.mp hmem]
    ring

end Cor12

variable {p : ℕ} [hp : Fact p.Prime]

variable (p) in
/-- `H = ∏_{i ∈ F_p} (∑_j c_j i^j)^d`, the top homogeneous part of the Nullstellensatz
polynomial. -/
noncomputable def Hpoly (d : ℕ) : MvPolynomial (Fin (d + 1)) (ZMod p) :=
  ∏ i : ZMod p, linForm d i ^ d

/-- The exponent vector `(d, p-1, …, p-1)`. -/
noncomputable def tvec (p d : ℕ) : Fin (d + 1) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun j => if j = 0 then d else p - 1

variable (p) in
/-- **The Nullstellensatz coefficient** `C(p,d) = [c_0^d c_1^{p-1} ⋯ c_d^{p-1}] H`. -/
noncomputable def Ccoeff (d : ℕ) : ZMod p := (Hpoly p d).coeff (tvec p d)

theorem totalDegree_Hpoly_le (d : ℕ) : (Hpoly p d).totalDegree ≤ p * d := by
  unfold Hpoly
  refine (totalDegree_finsetProd _ _).trans ?_
  calc ∑ i : ZMod p, (linForm d i ^ d).totalDegree ≤ ∑ _i : ZMod p, d := by
        refine sum_le_sum fun i _ => (totalDegree_pow _ _).trans ?_
        have := totalDegree_linForm (p := p) d i
        nlinarith
    _ = p * d := by simp [ZMod.card]

/-- `Cinv p d = (-1)^(d+1) C(p,d)` (Lemma 2.1 applied to `H`, via Corollary 1.2). -/
theorem Cinv_eq_neg_one_pow_Ccoeff (d : ℕ) (hd : d ≤ p - 1) :
    Cinv p d = (-1) ^ (d + 1) * Ccoeff p d := by
  have hp1 := hp.out.one_lt
  set Q : MvPolynomial (Fin (d + 1)) (ZMod p) := X 0 ^ (p - 1 - d) * Hpoly p d with hQ
  have hevalQ : ∀ c : Fin (d + 1) → ZMod p, eval c Q = c 0 ^ (p - 1 - d) * ∏ i, fc c i ^ d := by
    intro c
    simp [hQ, Hpoly, map_prod, eval_linForm]
  have hdegQ : Q.totalDegree ≤ (d + 1) * (Fintype.card (ZMod p) - 1) := by
    rw [ZMod.card]
    refine (totalDegree_mul _ _).trans ?_
    have h1 := totalDegree_Hpoly_le (p := p) d
    have h2 : (X (0 : Fin (d + 1)) ^ (p - 1 - d) : MvPolynomial (Fin (d + 1)) (ZMod p)).totalDegree
        ≤ p - 1 - d := by
      refine (totalDegree_pow _ _).trans ?_
      simp [totalDegree_X]
    have key : (p - 1 - d) + p * d = (d + 1) * (p - 1) := by
      have h3 : 1 ≤ p := hp1.le
      zify [hd, h3]
      ring
    omega
  have hsum := sum_eval_eq_coeff Q hdegQ
  simp_rw [hevalQ] at hsum
  rw [Cinv, hsum, ZMod.card]
  congr 1
  rw [hQ, X_pow_eq_monomial, coeff_monomial_mul', if_pos, one_mul]
  · unfold Ccoeff
    congr 1
    ext j
    simp only [tvec, Finsupp.coe_tsub, Pi.sub_apply, Finsupp.coe_equivFunOnFinite_symm,
      Finsupp.single_apply]
    by_cases hj : j = 0
    · subst hj; simp; omega
    · simp [hj, Ne.symm hj]
  · intro j
    simp only [Finsupp.single_apply, Finsupp.coe_equivFunOnFinite_symm]
    split_ifs <;> omega

/-- **Theorem 2** of the write-up, in its original form: for every prime `p` and `0 ≤ d ≤ p - 1`,
`C(p,d) = [c_0^d c_1^{p-1} ⋯ c_d^{p-1}] ∏_{i ∈ F_p} (∑_j c_j i^j)^d`
`= (-1)^{d(d+1)/2} ∏_{k=0}^d C(d,k)`,
and this is nonzero in `F_p`. -/
theorem theorem2 (d : ℕ) (hd : d ≤ p - 1) :
    Ccoeff p d = (-1) ^ (d * (d + 1) / 2) * ∏ k ∈ range (d + 1), (d.choose k : ZMod p) ∧
      Ccoeff p d ≠ 0 := by
  have h1 := Cinv_eq_neg_one_pow_Ccoeff (p := p) d hd
  rw [Cinv_eq d hd] at h1
  have hu : ((-1 : ZMod p) ^ (d + 1)) ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  have h2 := (mul_left_cancel₀ hu h1).symm
  refine ⟨h2, ?_⟩
  intro h0
  apply Cinv_ne_zero (p := p) d hd
  rw [Cinv_eq_neg_one_pow_Ccoeff d hd, h0, mul_zero]

end MO498708

#print axioms MO498708.theorem2
