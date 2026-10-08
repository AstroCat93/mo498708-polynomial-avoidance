import Formal.MO498708.Reduction

/-!
# MO 498708: machine-checked instances of Theorem 1 for `p ∈ {2, 3, 5}`

For each such `p` and each `d ≤ p - 1` the invariant `Cinv p d` is evaluated by the kernel
(`decide +kernel`, i.e. evaluation by the kernel only), and Theorem 1 follows from
`theorem1_of_Cinv_ne_zero`.
-/

namespace MO498708

open Finset

instance fact_prime_five : Fact (Nat.Prime 5) := ⟨by norm_num⟩

set_option maxRecDepth 100000

theorem Cinv_two_ne_zero : ∀ d : Fin 2, Cinv 2 d ≠ 0 := by decide +kernel

theorem Cinv_three_ne_zero : ∀ d : Fin 3, Cinv 3 d ≠ 0 := by decide +kernel

theorem Cinv_five_ne_zero : ∀ d : Fin 5, Cinv 5 d ≠ 0 := by decide +kernel

/-- Theorem 1 for `p = 2`. -/
theorem theorem1_p2 (d : ℕ) (hd : d ≤ 1) (A : ZMod 2 → Finset (ZMod 2)) (hA : ∀ i, #(A i) ≤ d) :
    ∃ f : Polynomial (ZMod 2), f.natDegree ≤ d ∧ ∀ i, f.eval i ∉ A i :=
  theorem1_of_Cinv_ne_zero d hd (Cinv_two_ne_zero ⟨d, by omega⟩) A hA

/-- Theorem 1 for `p = 3`. -/
theorem theorem1_p3 (d : ℕ) (hd : d ≤ 2) (A : ZMod 3 → Finset (ZMod 3)) (hA : ∀ i, #(A i) ≤ d) :
    ∃ f : Polynomial (ZMod 3), f.natDegree ≤ d ∧ ∀ i, f.eval i ∉ A i :=
  theorem1_of_Cinv_ne_zero d hd (Cinv_three_ne_zero ⟨d, by omega⟩) A hA

/-- Theorem 1 for `p = 5`. -/
theorem theorem1_p5 (d : ℕ) (hd : d ≤ 4) (A : ZMod 5 → Finset (ZMod 5)) (hA : ∀ i, #(A i) ≤ d) :
    ∃ f : Polynomial (ZMod 5), f.natDegree ≤ d ∧ ∀ i, f.eval i ∉ A i :=
  theorem1_of_Cinv_ne_zero d hd (Cinv_five_ne_zero ⟨d, by omega⟩) A hA

end MO498708

#print axioms MO498708.theorem1_p5
