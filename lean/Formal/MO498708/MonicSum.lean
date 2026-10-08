import Mathlib

/-!
# MO 498708, Lemma 2.3 steps (a)–(b): sums over monic polynomials and Newton's identity

* `Mon p k` : the finset of monic polynomials of degree `k` over `F_p`;
* `chi d F = ∏_{b ≠ 0} F(b)^d` (completely multiplicative);
* `Asum d k = ∑_{F ∈ Mon p k} chi d F` (the `A_k` of the write-up);
* `Ssum d n = ∑_{π monic irreducible, deg π ∣ n} deg π · chi d π ^ (n / deg π)`.

Main result: `k · A_k = ∑_{i<k} S_{k-i} A_i`, which is the coefficient form of
`u L'(u) / L(u) = ∑ s_n u^n` (Euler product + logarithmic derivative), proved here directly from
unique factorisation via the identity `deg F = ∑_{π^m ∣ F} deg π`.
-/

open Finset Polynomial UniqueFactorizationMonoid

namespace MO498708

open scoped Classical

variable {p : ℕ} [hp : Fact p.Prime]

/-- The monic polynomial `X^k + ∑_{j<k} w_j X^j`. -/
noncomputable def monicOf {k : ℕ} (w : Fin k → ZMod p) : (ZMod p)[X] :=
  X ^ k + ∑ j : Fin k, C (w j) * X ^ (j : ℕ)

theorem monicOf_monic {k : ℕ} (w : Fin k → ZMod p) : (monicOf w).Monic :=
  monic_X_pow_add (degree_sum_fin_lt w)

theorem natDegree_monicOf {k : ℕ} (w : Fin k → ZMod p) : (monicOf w).natDegree = k := by
  unfold monicOf
  rw [natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
  rw [degree_X_pow]
  exact degree_sum_fin_lt w

theorem coeff_monicOf {k : ℕ} (w : Fin k → ZMod p) (j : Fin k) : (monicOf w).coeff j = w j := by
  unfold monicOf
  rw [coeff_add, coeff_X_pow, if_neg (by have := j.isLt; omega), zero_add, finsetSum_coeff]
  simp_rw [coeff_C_mul_X_pow]
  rw [sum_eq_single j]
  · simp
  · intro b _ hb
    rw [if_neg]
    intro h
    exact hb (Fin.ext h.symm)
  · simp

theorem monicOf_injective {k : ℕ} : Function.Injective (monicOf (p := p) (k := k)) := by
  intro w w' h
  funext j
  rw [← coeff_monicOf w j, ← coeff_monicOf w' j, h]

variable (p) in
/-- Monic polynomials of degree `k` over `F_p`. -/
noncomputable def Mon (k : ℕ) : Finset (ZMod p)[X] := univ.image (monicOf (p := p) (k := k))

theorem mem_Mon {k : ℕ} {F : (ZMod p)[X]} : F ∈ Mon p k ↔ F.Monic ∧ F.natDegree = k := by
  constructor
  · rintro hF
    obtain ⟨w, -, rfl⟩ := mem_image.mp hF
    exact ⟨monicOf_monic w, natDegree_monicOf w⟩
  · rintro ⟨hm, rfl⟩
    refine mem_image.mpr ⟨fun j => F.coeff j, mem_univ _, ?_⟩
    conv_rhs => rw [hm.as_sum]
    unfold monicOf
    rw [← Fin.sum_univ_eq_sum_range (fun i => C (F.coeff i) * X ^ i)]

theorem sum_Mon {M : Type*} [AddCommMonoid M] (k : ℕ) (g : (ZMod p)[X] → M) :
    ∑ F ∈ Mon p k, g F = ∑ w : Fin k → ZMod p, g (monicOf w) := by
  rw [Mon, sum_image (fun a _ b _ h => monicOf_injective h)]

theorem Mon_zero : Mon p 0 = {1} := by
  ext F
  rw [mem_Mon, mem_singleton]
  constructor
  · rintro ⟨hm, hd⟩
    exact Polynomial.eq_one_of_monic_natDegree_zero hm hd
  · rintro rfl
    simp

/-- Monic irreducible polynomials of degree `k`. -/
noncomputable def Irr (p : ℕ) [Fact p.Prime] (k : ℕ) : Finset (ZMod p)[X] :=
  (Mon p k).filter Irreducible

/-- Monic irreducible polynomials of degree dividing `n`. -/
noncomputable def IrrDiv (p : ℕ) [Fact p.Prime] (n : ℕ) : Finset (ZMod p)[X] :=
  n.divisors.biUnion (Irr p)

theorem mem_IrrDiv {n : ℕ} {π : (ZMod p)[X]} :
    π ∈ IrrDiv p n ↔ π.Monic ∧ Irreducible π ∧ π.natDegree ∣ n ∧ n ≠ 0 := by
  simp only [IrrDiv, Irr, mem_biUnion, mem_filter, mem_Mon, Nat.mem_divisors]
  constructor
  · rintro ⟨e, ⟨he, hn⟩, ⟨hm, rfl⟩, hirr⟩
    exact ⟨hm, hirr, he, hn⟩
  · rintro ⟨hm, hirr, he, hn⟩
    exact ⟨_, ⟨he, hn⟩, ⟨hm, rfl⟩, hirr⟩

section chi

variable (d : ℕ)

/-- `χ(F) = N(F)^d = ∏_{b ∈ F_p^*} F(b)^d`. -/
noncomputable def chi (F : (ZMod p)[X]) : ZMod p :=
  ∏ b ∈ (univ : Finset (ZMod p)).erase 0, F.eval b ^ d

theorem chi_mul (F G : (ZMod p)[X]) : chi d (F * G) = chi d F * chi d G := by
  simp [chi, eval_mul, mul_pow, prod_mul_distrib]

theorem chi_one : chi (p := p) d 1 = 1 := by simp [chi]

theorem chi_pow (F : (ZMod p)[X]) (m : ℕ) : chi d (F ^ m) = chi d F ^ m := by
  induction m with
  | zero => simp [chi_one]
  | succ m ih => rw [pow_succ, chi_mul, ih, pow_succ]

variable (p) in
/-- `A_k = ∑_{F monic, deg F = k} χ(F)`. -/
noncomputable def Asum (k : ℕ) : ZMod p := ∑ F ∈ Mon p k, chi d F

variable (p) in
/-- `s_n = ∑_{π monic irreducible, deg π ∣ n} deg π · χ(π)^{n / deg π}`. -/
noncomputable def Ssum (n : ℕ) : ZMod p :=
  ∑ π ∈ IrrDiv p n, (π.natDegree : ZMod p) * chi d π ^ (n / π.natDegree)

theorem Asum_zero : Asum p d 0 = 1 := by
  simp [Asum, Mon_zero, chi_one]

/-- Sum of `χ` over the monic multiples of degree `k` of a monic `G`. -/
theorem sum_filter_dvd (G : (ZMod p)[X]) (hG : G.Monic) (k : ℕ) (hk : G.natDegree ≤ k) :
    ∑ F ∈ (Mon p k).filter (G ∣ ·), chi d F = chi d G * Asum p d (k - G.natDegree) := by
  classical
  rw [Asum, mul_sum]
  have hG0 : G ≠ 0 := hG.ne_zero
  have himg : (Mon p k).filter (G ∣ ·) = (Mon p (k - G.natDegree)).image (G * ·) := by
    ext F
    simp only [mem_filter, mem_Mon, mem_image]
    constructor
    · rintro ⟨⟨hFm, hFd⟩, H, rfl⟩
      have hHm : H.Monic := hG.of_mul_monic_left hFm
      refine ⟨H, ⟨hHm, ?_⟩, rfl⟩
      rw [hG.natDegree_mul hHm] at hFd
      omega
    · rintro ⟨H, ⟨hHm, hHd⟩, rfl⟩
      refine ⟨⟨hG.mul hHm, ?_⟩, dvd_mul_right _ _⟩
      rw [hG.natDegree_mul hHm, hHd]
      omega
  rw [himg, sum_image (fun a _ b _ h => mul_left_cancel₀ hG0 h)]
  exact sum_congr rfl fun H _ => chi_mul d G H

end chi

section vonMangoldt

theorem pow_dvd_iff_le_count {π F : (ZMod p)[X]} (hπ : π.Monic) (hirr : Irreducible π)
    (hF : F ≠ 0) (m : ℕ) : π ^ m ∣ F ↔ m ≤ (normalizedFactors F).count π := by
  rw [dvd_iff_normalizedFactors_le_normalizedFactors (pow_ne_zero _ hirr.ne_zero) hF,
    hirr.normalizedFactors_pow, hπ.normalize_eq_self, ← Multiset.le_count_iff_replicate_le]

theorem monic_of_mem_normalizedFactors {π F : (ZMod p)[X]} (h : π ∈ normalizedFactors F) :
    π.Monic := by
  have h1 := normalize_normalized_factor π h
  have h0 : π ≠ 0 := (irreducible_of_normalized_factor π h).ne_zero
  rw [← h1]
  exact monic_normalize h0

theorem natDegree_eq_sum_count (F : (ZMod p)[X]) (hF : F.Monic) :
    F.natDegree = ∑ π ∈ (normalizedFactors F).toFinset,
      (normalizedFactors F).count π * π.natDegree := by
  have h1 : (normalizedFactors F).prod = F := by
    rw [prod_normalizedFactors_eq hF.ne_zero, hF.normalize_eq_self]
  conv_lhs => rw [← h1]
  rw [natDegree_multiset_prod_of_monic _ (fun x hx => monic_of_mem_normalizedFactors hx),
    sum_multiset_map_count]
  simp [smul_eq_mul]

variable (p) in
/-- Index set `{(n, π) : 1 ≤ n ≤ k, π monic irreducible, deg π ∣ n}`. -/
noncomputable def PP (k : ℕ) : Finset (Σ _ : ℕ, (ZMod p)[X]) :=
  (Icc 1 k).sigma (fun n => IrrDiv p n)

/-- The polynomial analogue of `log n = ∑_{d ∣ n} Λ(d)`: `deg F = ∑_{π^m ∣ F} deg π`. -/
theorem vonMangoldt (F : (ZMod p)[X]) (hF : F.Monic) (k : ℕ) (hk : F.natDegree = k) :
    ∑ x ∈ (PP p k).filter (fun x => x.2 ^ (x.1 / x.2.natDegree) ∣ F), x.2.natDegree = k := by
  have hF0 : F ≠ 0 := hF.ne_zero
  set T := (normalizedFactors F).toFinset with hT
  have hR : k = ∑ x ∈ T.sigma (fun π => Icc 1 ((normalizedFactors F).count π)), x.1.natDegree := by
    rw [sum_sigma, ← hk, natDegree_eq_sum_count F hF]
    refine sum_congr rfl fun π _ => ?_
    simp
  rw [hR]
  refine sum_nbij' (fun x => ⟨x.2, x.1 / x.2.natDegree⟩) (fun x => ⟨x.2 * x.1.natDegree, x.1⟩)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨n, π⟩ hx
    simp only [PP, mem_filter, mem_sigma, mem_Icc, mem_IrrDiv] at hx
    obtain ⟨⟨⟨hn1, hnk⟩, hm, hirr, hdvd, hn0⟩, hpow⟩ := hx
    have hdeg := hirr.natDegree_pos
    have hc := (pow_dvd_iff_le_count hm hirr hF0 _).mp hpow
    have hq : 1 ≤ n / π.natDegree := (Nat.le_div_iff_mul_le hdeg).mpr (by
      simpa using Nat.le_of_dvd (by omega) hdvd)
    simp only [mem_sigma, mem_Icc, hT, Multiset.mem_toFinset]
    refine ⟨Multiset.count_pos.mp (by omega), hq, hc⟩
  · rintro ⟨π, m⟩ hx
    simp only [mem_sigma, mem_Icc, hT, Multiset.mem_toFinset] at hx
    obtain ⟨hmem, hm1, hmc⟩ := hx
    have hirr := irreducible_of_normalized_factor π hmem
    have hmon := monic_of_mem_normalizedFactors hmem
    have hdeg := hirr.natDegree_pos
    have hpow := (pow_dvd_iff_le_count hmon hirr hF0 m).mpr hmc
    have hle : (π ^ m).natDegree ≤ F.natDegree := natDegree_le_of_dvd hpow hF0
    rw [hmon.natDegree_pow] at hle
    simp only [PP, mem_filter, mem_sigma, mem_Icc, mem_IrrDiv]
    refine ⟨⟨⟨?_, by omega⟩, hmon, hirr, dvd_mul_left _ _, ?_⟩, ?_⟩
    · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    · exact Nat.mul_ne_zero (by omega) (by omega)
    · rw [Nat.mul_div_cancel _ hdeg]
      exact hpow
  · rintro ⟨n, π⟩ hx
    simp only [PP, mem_filter, mem_sigma, mem_IrrDiv] at hx
    obtain ⟨⟨-, -, -, hdvd, -⟩, -⟩ := hx
    simp only [Nat.div_mul_cancel hdvd]
  · rintro ⟨π, m⟩ hx
    simp only [mem_sigma, hT, Multiset.mem_toFinset] at hx
    have hdeg := (irreducible_of_normalized_factor π hx.1).natDegree_pos
    simp only [Nat.mul_div_cancel _ hdeg]
  · intro x _
    rfl

/-- **Newton's identity** `k A_k = ∑_{i<k} s_{k-i} A_i` (coefficientwise `uL'/L = ∑ s_n u^n`). -/
theorem newton_Asum (d k : ℕ) :
    (k : ZMod p) * Asum p d k = ∑ i ∈ range k, Ssum p d (k - i) * Asum p d i := by
  have h1 : (k : ZMod p) * Asum p d k = ∑ F ∈ Mon p k, ∑ x ∈ PP p k,
      (if x.2 ^ (x.1 / x.2.natDegree) ∣ F then (x.2.natDegree : ZMod p) * chi d F else 0) := by
    rw [Asum, mul_sum]
    refine sum_congr rfl fun F hF => ?_
    obtain ⟨hFm, hFd⟩ := mem_Mon.mp hF
    rw [← sum_filter, ← sum_mul]
    congr 1
    have := vonMangoldt F hFm k hFd
    rw [← Nat.cast_sum, this]
  rw [h1, sum_comm]
  have h2 : ∀ x ∈ PP p k, ∑ F ∈ Mon p k,
      (if x.2 ^ (x.1 / x.2.natDegree) ∣ F then (x.2.natDegree : ZMod p) * chi d F else 0) =
      (x.2.natDegree : ZMod p) * chi d x.2 ^ (x.1 / x.2.natDegree) * Asum p d (k - x.1) := by
    rintro ⟨n, π⟩ hx
    dsimp only
    simp only [PP, mem_sigma, mem_Icc, mem_IrrDiv] at hx
    obtain ⟨⟨hn1, hnk⟩, hm, hirr, hdvd, hn0⟩ := hx
    have hdeg := hirr.natDegree_pos
    have hpm : (π ^ (n / π.natDegree)).natDegree = n := by
      rw [hm.natDegree_pow, Nat.div_mul_cancel hdvd]
    rw [← sum_filter, ← mul_sum, sum_filter_dvd d _ (hm.pow _) k (by omega), chi_pow, hpm,
      mul_assoc]
  rw [sum_congr rfl h2, PP, sum_sigma]
  simp_rw [← sum_mul]
  change ∑ n ∈ Icc 1 k, Ssum p d n * Asum p d (k - n) = _
  refine sum_nbij' (fun n => k - n) (fun i => k - i) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    simp only [mem_Icc] at hn
    simp only [mem_range]
    omega
  · intro i hi
    simp only [mem_range] at hi
    simp only [mem_Icc]
    omega
  · intro n hn
    simp only [mem_Icc] at hn
    omega
  · intro i hi
    simp only [mem_range] at hi
    omega
  · intro n hn
    simp only [mem_Icc] at hn
    rw [Nat.sub_sub_self hn.2]

end vonMangoldt

end MO498708
