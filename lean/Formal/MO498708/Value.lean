import Formal.MO498708.Coefficient

/-!
# MO 498708, Theorem 1 part 3: prescribing the value at one point

Using Mathlib's Combinatorial Nullstellensatz (`combinatorial_nullstellensatz_exists_eval_nonzero`)
with the nonzero coefficient `C(p,d)` (Theorem 2): for any `z, s ∈ F_p` with `s ∉ A z`, some
avoiding `f` with `natDegree f ≤ d` has `f(z) = s`.
-/

open Finset MvPolynomial

namespace MO498708

open scoped Classical

variable {p : ℕ} [hp : Fact p.Prime]

omit hp in
theorem tvec_apply_zero (d : ℕ) : tvec p d 0 = d := by
  simp [tvec]

omit hp in
theorem tvec_apply_ne (d : ℕ) {j : Fin (d + 1)} (hj : j ≠ 0) : tvec p d j = p - 1 := by
  simp [tvec, hj]

theorem sum_tvec (d : ℕ) : ∑ j, tvec p d j = p * d := by
  have hp1 := hp.out.one_lt
  rw [Fin.sum_univ_succ, tvec_apply_zero]
  simp_rw [tvec_apply_ne d (Fin.succ_ne_zero _)]
  rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  ring

theorem sum_support_tvec (d : ℕ) : ∑ i ∈ (tvec p d).support, tvec p d i = p * d := by
  rw [← sum_tvec d]
  exact sum_subset (subset_univ _) (fun i _ hi => Finsupp.notMem_support_iff.mp hi)

/-- Theorem 1 with the value at `0` prescribed, in coefficient form. -/
theorem exists_avoid_value_zero (d : ℕ) (hd : d ≤ p - 1) (A : ZMod p → Finset (ZMod p))
    (hA : ∀ i, #(A i) ≤ d) (s : ZMod p) (hs : s ∉ A 0) :
    ∃ c : Fin (d + 1) → ZMod p, (∀ i, fc c i ∉ A i) ∧ c 0 = s := by
  have hp1 := hp.out.one_lt
  rcases Nat.eq_zero_or_pos d with rfl | hd1
  · refine ⟨fun _ => s, fun i => ?_, rfl⟩
    have := hA i
    simp_all
  -- pad the sets; `B 0` avoids `s`
  have hpad : ∀ i, ∃ B : Finset (ZMod p), A i ⊆ B ∧ #B = d ∧ (i = 0 → s ∉ B) := by
    intro i
    by_cases hi : i = 0
    · subst hi
      have hsub : A 0 ⊆ univ.erase s := fun a ha => mem_erase.mpr ⟨fun h => hs (h ▸ ha), mem_univ _⟩
      obtain ⟨B, h1, h2, h3⟩ := exists_subsuperset_card_eq hsub (hA 0)
        (by rw [card_erase_of_mem (mem_univ _), card_univ, ZMod.card]; omega)
      exact ⟨B, h1, h3, fun _ hsB => (mem_erase.mp (h2 hsB)).1 rfl⟩
    · obtain ⟨B, h1, -, h3⟩ := exists_subsuperset_card_eq (subset_univ (A i)) (hA i)
        (by rw [card_univ, ZMod.card]; omega)
      exact ⟨B, h1, h3, fun h => absurd h hi⟩
  choose B hAB hB hBs using hpad
  set σs : Finset (Σ _ : ZMod p, ZMod p) := univ.sigma B with hσs
  set P : MvPolynomial (Fin (d + 1)) (ZMod p) := ∏ x ∈ σs, (linForm d x.1 - C x.2) with hP
  have hσcard : #σs = p * d := by
    rw [hσs, card_sigma]
    simp [hB, ZMod.card]
  have hHσ : ∏ x ∈ σs, linForm d x.1 = Hpoly p d := by
    rw [hσs, prod_sigma, Hpoly]
    refine prod_congr rfl fun i _ => ?_
    simp [hB]
  -- the coefficient of `t` in `P` is `C(p,d) ≠ 0`
  have hdiff := totalDegree_prod_sub_prod_le σs (fun x => linForm d x.1) (fun x => x.2)
    (fun x _ => totalDegree_linForm d x.1)
  rw [hHσ, hσcard] at hdiff
  change (P - Hpoly p d).totalDegree ≤ _ at hdiff
  have hcoeff : P.coeff (tvec p d) = Ccoeff p d := by
    have h0 : (P - Hpoly p d).coeff (tvec p d) = 0 := by
      apply coeff_eq_zero_of_totalDegree_lt
      rw [sum_support_tvec]
      have : 1 ≤ p * d := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
      omega
    rw [coeff_sub, sub_eq_zero] at h0
    exact h0
  have hCne := (theorem2 (p := p) d hd).2
  have hPdeg : P.totalDegree = (tvec p d).degree := by
    rw [Finsupp.degree_apply, sum_support_tvec]
    apply le_antisymm
    · rw [hP]
      refine (totalDegree_finsetProd _ _).trans ?_
      calc ∑ x ∈ σs, (linForm d x.1 - C x.2).totalDegree ≤ ∑ _x ∈ σs, 1 := by
            refine sum_le_sum fun x _ => (totalDegree_sub _ _).trans ?_
            simp [totalDegree_C, totalDegree_linForm]
        _ = p * d := by simp [hσcard]
    · have hmem : tvec p d ∈ P.support := by
        rw [mem_support_iff, hcoeff]
        exact hCne
      have := le_totalDegree hmem
      rw [Finsupp.sum, sum_support_tvec] at this
      exact this
  set S : Fin (d + 1) → Finset (ZMod p) := fun j => if j = 0 then insert s (B 0) else univ with hS
  have htS : ∀ j, tvec p d j < #(S j) := by
    intro j
    by_cases hj : j = 0
    · subst hj
      simp only [hS, if_pos rfl, tvec_apply_zero]
      rw [card_insert_of_notMem (hBs 0 rfl), hB]
      omega
    · simp only [hS, if_neg hj, tvec_apply_ne d hj, card_univ, ZMod.card]
      omega
  obtain ⟨c, hcS, hcP⟩ := combinatorial_nullstellensatz_exists_eval_nonzero P (tvec p d)
    (by rw [hcoeff]; exact hCne) hPdeg S htS
  have heval : eval c P = ∏ i, ∏ a ∈ B i, (fc c i - a) := by
    simp only [hP, map_prod, map_sub, eval_C, eval_linForm]
    rw [hσs, prod_sigma]
  rw [heval] at hcP
  have hnotB : ∀ i, fc c i ∉ B i := by
    intro i hi
    apply hcP
    exact prod_eq_zero (mem_univ i) (prod_eq_zero hi (sub_self _))
  refine ⟨c, fun i hi => hnotB i (hAB i hi), ?_⟩
  have hc0 := hcS 0
  simp only [hS, if_pos rfl, mem_insert] at hc0
  rcases hc0 with h | h
  · exact h
  · exfalso
    apply hnotB 0
    rw [fc_zero]
    exact h

/-- **Theorem 1, parts 1 and 3.** For every prime `p`, `d ≤ p - 1`, every family `A` with
`#(A i) ≤ d`, and every `z, s ∈ F_p` with `s ∉ A z`, there is `f ∈ F_p[x]` with
`natDegree f ≤ d`, `f(i) ∉ A i` for all `i`, and `f(z) = s`. -/
theorem theorem1_value (d : ℕ) (hd : d ≤ p - 1) (A : ZMod p → Finset (ZMod p))
    (hA : ∀ i, #(A i) ≤ d) (z s : ZMod p) (hs : s ∉ A z) :
    ∃ f : Polynomial (ZMod p), f.natDegree ≤ d ∧ (∀ i, f.eval i ∉ A i) ∧ f.eval z = s := by
  obtain ⟨c, hc, hc0⟩ := exists_avoid_value_zero d hd (fun i => A (i + z)) (fun i => hA _) s
    (by simpa using hs)
  refine ⟨(polyOf c).comp (Polynomial.X - Polynomial.C z), ?_, ?_, ?_⟩
  · rw [Polynomial.natDegree_comp, Polynomial.natDegree_X_sub_C, mul_one]
    exact natDegree_polyOf_le c
  · intro i
    rw [Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
      eval_polyOf]
    have := hc (i - z)
    simpa using this
  · rw [Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self,
      eval_polyOf, fc_zero, hc0]

/-- **Theorem 1, part 2.** At least `p - d` distinct polynomials of degree `≤ d` avoid the family.
(The write-up derives this from the Alon–Füredi theorem; here it follows from part 3, since the
values `f(0) = s` for the `≥ p - d` choices `s ∉ A 0` give distinct avoiders.) -/
theorem theorem1_count (d : ℕ) (hd : d ≤ p - 1) (A : ZMod p → Finset (ZMod p))
    (hA : ∀ i, #(A i) ≤ d) :
    ∃ F : Finset (Polynomial (ZMod p)), p - d ≤ #F ∧
      ∀ f ∈ F, f.natDegree ≤ d ∧ ∀ i, f.eval i ∉ A i := by
  have hex : ∀ s : ZMod p, s ∉ A 0 → ∃ f : Polynomial (ZMod p),
      f.natDegree ≤ d ∧ (∀ i, f.eval i ∉ A i) ∧ f.eval 0 = s :=
    fun s hs => theorem1_value d hd A hA 0 s hs
  choose! g hg using hex
  refine ⟨(univ \ A 0).image g, ?_, ?_⟩
  · rw [card_image_of_injOn]
    · rw [card_sdiff_of_subset (subset_univ _), card_univ, ZMod.card]
      have := hA 0
      omega
    · intro s hs t ht hst
      have hs' : s ∉ A 0 := (mem_sdiff.mp hs).2
      have ht' : t ∉ A 0 := (mem_sdiff.mp ht).2
      rw [← (hg s hs').2.2, ← (hg t ht').2.2, hst]
  · intro f hf
    obtain ⟨s, hs, rfl⟩ := mem_image.mp hf
    have hs' : s ∉ A 0 := (mem_sdiff.mp hs).2
    exact ⟨(hg s hs').1, (hg s hs').2.1⟩

end MO498708

#print axioms MO498708.theorem1_value
#print axioms MO498708.theorem1_count
