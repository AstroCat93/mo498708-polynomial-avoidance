import Formal.MO498708.Reduction
import Formal.MO498708.MonicSum
import Formal.MO498708.PowerSum

/-!
# MO 498708, Lemma 2.2: `C(p,d)` as a sum over monic polynomials

We show `Cinv p d = (-1)^(d+1) * A_d`, where `A_d = ∑_{F monic, deg F = d} ∏_{b ≠ 0} F(b)^d`.
(Together with `Cinv = (-1)^(d+1) C(p,d)` this is `C(p,d) = A_d`.)  The proof: strip off the
factor at `i = 0`, scale the coefficient vector so that `c_0 = 1`, and reverse the polynomial
(`i ↦ i⁻¹`), using Wilson's theorem `∏_{b ≠ 0} b = -1`.
-/

open Finset Polynomial

namespace MO498708

open scoped Classical

variable {p : ℕ} [hp : Fact p.Prime]

/-- Wilson's theorem in the form `∏_{b ∈ F_p^*} b = -1`. -/
theorem prod_units_eq_neg_one : ∏ b ∈ (univ : Finset (ZMod p)).erase 0, b = -1 := by
  have h := FiniteField.prod_univ_units_id_eq_neg_one (K := ZMod p)
  have h2 : ∏ x : (ZMod p)ˣ, (x : ZMod p) = ∏ b ∈ (univ : Finset (ZMod p)).erase 0, b := by
    refine Finset.prod_bij' (fun u _ => (u : ZMod p)) (fun x hx => Units.mk0 x (by simpa using hx))
      ?_ ?_ ?_ ?_ ?_ <;> simp
  rw [← h2, ← Units.coe_prod, h]
  simp

theorem fc_zero {d : ℕ} (c : Fin (d + 1) → ZMod p) : fc c 0 = c 0 := by
  simp [fc, Fin.sum_univ_succ]

/-- Reversal: `F(b) = b^d f(b⁻¹)` for the monic `F` with reversed coefficients of `f = 1 + …`. -/
theorem eval_monicOf_rev {d : ℕ} (w : Fin d → ZMod p) (b : ZMod p) (hb : b ≠ 0) :
    (monicOf (fun j => w (Fin.rev j))).eval b =
      b ^ d * fc (Fin.cons 1 w : Fin (d + 1) → ZMod p) b⁻¹ := by
  simp only [monicOf, eval_add, eval_pow, eval_X, eval_finsetSum, eval_mul, eval_C, fc,
    Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.val_zero, pow_zero, mul_one,
    Fin.val_succ]
  rw [mul_add, mul_one, mul_sum]
  congr 1
  rw [← Equiv.sum_comp Fin.revPerm]
  refine sum_congr rfl fun j _ => ?_
  simp only [Fin.revPerm_apply, Fin.rev_rev, Fin.val_rev]
  have hj : (j : ℕ) + 1 ≤ d := j.isLt
  have hsplit : b ^ d = b ^ (d - (j + 1)) * b ^ ((j : ℕ) + 1) := by
    rw [← pow_add, Nat.sub_add_cancel hj]
  rw [hsplit, inv_pow]
  field_simp

/-- **Lemma 2.2**: `Cinv p d = (-1)^(d+1) A_d`. -/
theorem Cinv_eq_Asum (d : ℕ) (hd : d ≤ p - 1) : Cinv p d = (-1) ^ (d + 1) * Asum p d d := by
  have hp1 := hp.out.one_lt
  -- Step 1: strip off the factor `i = 0`
  have hsplit : ∀ c : Fin (d + 1) → ZMod p, c 0 ^ (p - 1 - d) * ∏ i, fc c i ^ d =
      c 0 ^ (p - 1) * ∏ i ∈ (univ : Finset (ZMod p)).erase 0, fc c i ^ d := by
    intro c
    rw [← mul_prod_erase univ _ (mem_univ 0), fc_zero, ← mul_assoc, ← pow_add,
      Nat.sub_add_cancel hd]
  rw [Cinv]
  simp_rw [hsplit]
  -- Step 2: split `c = (c 0, tail)`
  rw [← (Fin.consEquiv (fun _ => ZMod p)).sum_comp, Fintype.sum_prod_type]
  simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.cons_zero]
  set B := ∑ w : Fin d → ZMod p,
    ∏ i ∈ (univ : Finset (ZMod p)).erase 0, fc (Fin.cons 1 w : Fin (d + 1) → ZMod p) i ^ d
    with hB
  -- Step 3: scaling
  have hscale : ∀ a : ZMod p, ∑ w : Fin d → ZMod p, a ^ (p - 1) *
      ∏ i ∈ (univ : Finset (ZMod p)).erase 0, fc (Fin.cons a w : Fin (d + 1) → ZMod p) i ^ d =
      a ^ (p - 1) * B := by
    intro a
    rw [← mul_sum]
    by_cases ha : a = 0
    · rw [ha, zero_pow (by omega), zero_mul, zero_mul]
    congr 1
    let e : (Fin d → ZMod p) ≃ (Fin d → ZMod p) :=
      { toFun := fun w => a • w
        invFun := fun w => a⁻¹ • w
        left_inv := fun w => by simp [smul_smul, inv_mul_cancel₀ ha]
        right_inv := fun w => by simp [smul_smul, mul_inv_cancel₀ ha] }
    rw [hB, ← e.sum_comp]
    refine sum_congr rfl fun w _ => ?_
    have hfc : ∀ i, fc (Fin.cons a (e w) : Fin (d + 1) → ZMod p) i =
        a * fc (Fin.cons 1 w : Fin (d + 1) → ZMod p) i := by
      intro i
      simp only [fc, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, e, Equiv.coe_fn_mk,
        Pi.smul_apply, smul_eq_mul, mul_add, mul_sum]
      congr 1
      · ring
      · exact sum_congr rfl fun j _ => by ring
    simp_rw [hfc, mul_pow, prod_mul_distrib, prod_const, card_erase_of_mem (mem_univ _),
      card_univ, ZMod.card, ← pow_mul, mul_comm d (p - 1), pow_mul,
      ZMod.pow_card_sub_one_eq_one ha, one_pow, one_mul]
  simp_rw [hscale]
  rw [← sum_mul, sum_pow_eq_ite, ZMod.card, if_pos ⟨by omega, dvd_rfl⟩]
  -- Step 4: reversal
  have hA : Asum p d d = (-1) ^ (d * d) * B := by
    rw [Asum, sum_Mon]
    let r : (Fin d → ZMod p) ≃ (Fin d → ZMod p) :=
      { toFun := fun w j => w (Fin.rev j)
        invFun := fun w j => w (Fin.rev j)
        left_inv := fun w => by simp
        right_inv := fun w => by simp }
    rw [hB, mul_sum, ← r.sum_comp]
    refine sum_congr rfl fun w _ => ?_
    simp only [chi, r, Equiv.coe_fn_mk]
    rw [prod_congr rfl fun b hb => by rw [eval_monicOf_rev w b (ne_of_mem_erase hb)]]
    simp_rw [mul_pow, prod_mul_distrib, ← pow_mul, prod_pow, prod_units_eq_neg_one]
    congr 2
    refine prod_nbij' (fun b : ZMod p => b⁻¹) (fun b : ZMod p => b⁻¹) ?_ ?_ ?_ ?_ ?_
    · intro b hb
      simp only [mem_erase, mem_univ, and_true] at hb ⊢
      exact inv_ne_zero hb
    · intro b hb
      simp only [mem_erase, mem_univ, and_true] at hb ⊢
      exact inv_ne_zero hb
    · intro b _
      exact inv_inv b
    · intro b _
      exact inv_inv b
    · intro b _
      rfl
  rw [hA, ← mul_assoc, ← pow_add]
  have he : Even (d * (d + 1)) := Nat.even_mul_succ_self d
  rw [show d + 1 + d * d = d * (d + 1) + 1 by ring, pow_succ, he.neg_one_pow, one_mul]

end MO498708
