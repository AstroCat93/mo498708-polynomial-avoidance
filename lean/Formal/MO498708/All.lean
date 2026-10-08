import Formal.MO498708.Value
import Formal.MO498708.SmallCases

/-!
# MO 498708 (Michael Ren): formalization of Theorems 1 and 2 of `solution.md`

Everything below is proved in Lean 4 / Mathlib without `sorry`, extra axioms or `native_decide`.

## Main statements

* `MO498708.theorem1` (Theorem 1, part 1 = question (Q1)): for every prime `p`, every
  `d ≤ p - 1` and every `A : ZMod p → Finset (ZMod p)` with `(A i).card ≤ d`, some
  `f : Polynomial (ZMod p)` with `f.natDegree ≤ d` satisfies `f.eval i ∉ A i` for all `i`.
* `MO498708.theorem1_count` (part 2): at least `p - d` distinct such `f` exist.
* `MO498708.theorem1_value` (part 3): for any `z, s` with `s ∉ A z`, some such `f` has `f(z) = s`.
* `MO498708.theorem2` (Theorem 2): the Combinatorial-Nullstellensatz coefficient
  `C(p,d) = [c_0^d c_1^{p-1} ⋯ c_d^{p-1}] ∏_{i ∈ F_p} (∑_j c_j i^j)^d` equals
  `(-1)^{d(d+1)/2} ∏_{k=0}^{d} C(d,k)` in `F_p` and is nonzero.
* `MO498708.theorem2_Asum`: `∑_{F monic, deg F = d} ∏_{b ∈ F_p^*} F(b)^d
  = (-1)^{d(d+1)/2} ∏_{k=0}^{d} C(d,k)`.
* `MO498708.Asum_eq_esymm`, `MO498708.Asum_eq_zero` (Theorem 2, "moreover"): for `k ≤ p - 1`,
  `∑_{F monic, deg F = k} N(F)^d = (-1)^k e_k(γ_1, …, γ_d)` with `γ_t = (-1)^{d-t} C(d,t)`,
  which is the `u^k`-coefficient of `∏_t (1 - γ_t u)` (this standard identification is not
  restated in Lean); in particular the sum vanishes for `d < k ≤ p - 1`.

## Route (file by file)

* `Reduction`   – Lemma 2.1: Theorem 1 follows from `Cinv p d ≠ 0`
                  (Chevalley–Warning style vanishing `MvPolynomial.sum_eval_eq_zero`).
* `CinvAd`      – Lemma 2.2: `Cinv p d = (-1)^(d+1) A_d` (scaling, reversal, Wilson).
* `MonicSum`    – Lemma 2.3 (a)–(b) in coefficient form: Newton's identity
                  `k A_k = ∑_{i<k} s_{k-i} A_i`, from unique factorisation in `F_p[X]` via
                  `deg F = ∑_{π^m ∣ F} deg π` (no power series needed).
* `Galois`      – Lemma 2.3 (c): `s_n = ∑_{β ∈ GF(p^n)} (β^{p-1}-1)^{dρ}` (grouping by minimal
                  polynomials; field norm `N(x) = x^ρ`).
* `PowerSum`    – Lemma 2.3 (d): `∑_β (β^{p-1}-1)^{dρ} = -∑_{t=1}^d γ_t^n` (power sums, base-`p`
                  digits).
* `Newton`      – Lemma 2.3 (e): the recursion determines `A_k = (-1)^k e_k(γ)` for `k < p`.
* `Main`        – assembly: `A_d` closed form, `Cinv p d ≠ 0`, Theorem 1.
* `Coefficient` – Corollary 1.2 and `Cinv p d = (-1)^(d+1) C(p,d)`, giving Theorem 2 verbatim.
* `Value`       – parts 2 and 3 of Theorem 1 (Mathlib's Combinatorial Nullstellensatz).
* `SmallCases`  – independent kernel evaluation (`decide +kernel`) of `Cinv p d ≠ 0` for
                  `p ∈ {2, 3, 5}`.
-/

#print axioms MO498708.theorem1
#print axioms MO498708.theorem1_count
#print axioms MO498708.theorem1_value
#print axioms MO498708.theorem2
#print axioms MO498708.theorem2_Asum
#print axioms MO498708.Asum_eq_esymm
#print axioms MO498708.Asum_eq_zero
#print axioms MO498708.theorem1_p5
