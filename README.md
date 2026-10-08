# Avoiding $d$-sets with low-degree polynomials over $\mathbb F_p$ (MathOverflow 498708)

This repository contains a proposed answer to [MathOverflow question 498708](https://mathoverflow.net/questions/498708), together with the code and logs needed to check it.

- **(Q1) is answered yes, with a complete proof that does not use a computer.** The key step is an explicit formula for a Combinatorial Nullstellensatz coefficient.
- **(Q2), read per pair $(p,d)$, is answered "not always" by an exhaustive computer search.** At $(p,d)=(11,8)$ and $(13,10)$ the degree bound $d$ is not the least possible.

The full write-up is [`solution.md`](solution.md). **The mathematics, code and text were produced by AI** (see [AI disclosure](#ai-disclosure-and-authorship)). No human has verified the mathematics.

## The problem

The question was asked on 2025-08-05 by [Michael Ren](https://mathoverflow.net/users/570015/michael-ren) under the title "Interpolating a degree $d$ polynomial over $\mathbb F_p$ to avoid sets of size $d$". As of 2026-10-08 it had no answers. Paraphrased:

> Let $p$ be a prime and $0\le d<p$. Let $A_i\subseteq\mathbb F_p$, for $i\in\mathbb F_p$, be sets of size $d$.
>
> **(Q1)** Is there always a polynomial $f\in\mathbb F_p[x]$ with $\deg f\le d$ such that $f(i)\notin A_i$ for every $i\in\mathbb F_p$?
>
> **(Q2)** If so, is $d$ the lowest possible degree bound? In other words, are there $d$-sets $A_i$ such that every $f$ with $\deg f\le d-1$ has $f(i)\in A_i$ for some $i$? (Call such a family *blocking*.)

The poster proved (Q1) for $d=0,1,2,p-2,p-1$. They also gave blocking families for $d=1,2,p-2,p-1$, and they note that a special case of $d=2$ appeared as ISL 2024 N6. The question uses the convention $\deg 0=0$.

## Results

| | Statement | Status |
|---|---|---|
| **Theorem 1** | (Q1) holds for every prime $p$ and every $0\le d\le p-1$. In fact at least $p-d$ polynomials of degree $\le d$ avoid the family, and the value at any one prescribed point can be chosen freely (outside the forbidden set there). | Proved, without computer assistance (§2 of `solution.md`) |
| **Theorem 2** | The Nullstellensatz coefficient is $C(p,d)\equiv(-1)^{d(d+1)/2}\prod_{k=0}^{d}\binom dk\not\equiv0\pmod p$. More generally, $\sum_{F\text{ monic},\ \deg F=k}N(F)^d\equiv[u^k]\prod_{t=1}^d\bigl(1-(-1)^{d-t}\binom dt u\bigr)$ for $k<p$, where $N(F)=\prod_{a\ne0}F(a)$. | Proved, without computer assistance (§2) |
| **Proposition 3** | Blocking families exist for $d\in\{1,2,p-2,p-1\}$ and every $p$. These are the poster's constructions, re-checked. So $d$ is sharp for all $d$ when $p\le5$. | Proved (§3.2) |
| **Proposition 4** | Blocking families exist for $p=7$, $d=3,4$; the families are explicit. So $d$ is sharp for all $1\le d\le6$ at $p=7$. | Proved by a finite check of $7^3$ and $7^4$ polynomials (§3.3) |
| **Theorem 5** | At $(p,d)=(11,8)$ and $(13,10)$ **no** blocking family exists: every family of $d$-sets is avoided by some $f$ with $\deg f\le d-1$. | **Computer-assisted**: exhaustive search, no formal certificate (§3.4; see below) |
| Open | Sharpness at $p=11$ for $3\le d\le7$, at $p=13$ for $3\le d\le9$, and at every $p\ge17$ for $3\le d\le p-3$. | Not decided; heuristic data only (§3.5) |

## Proof sketch of Theorems 1 and 2

We may assume $|A_i|=d$. For $c=(c_0,\dots,c_d)\in\mathbb F_p^{d+1}$ put $f_c(x)=\sum_j c_jx^j$ and
$$P(c)=\prod_{i\in\mathbb F_p}\prod_{a\in A_i}\bigl(f_c(i)-a\bigr).$$
Then $P(c)\ne0$ exactly when $f_c$ avoids the family. Two facts drive the proof:

- $\deg P\le pd$;
- the top-degree part of $P$ is $H(c)=\prod_i f_c(i)^d$, which **does not depend on the family**.

**Step 1 (Combinatorial Nullstellensatz).** Look at the monomial $c_0^{\,d}c_1^{\,p-1}\cdots c_d^{\,p-1}$. It has degree $pd$, and every exponent is $<p$. Summing $c_0^{\,p-1-d}P(c)$ over the grid $\mathbb F_p^{d+1}$ gives
$$\sum_c c_0^{\,p-1-d}P(c)=(-1)^{d+1}C(p,d),\qquad C(p,d):=[c_0^dc_1^{p-1}\cdots c_d^{p-1}]\,H .$$
Since $C(p,d)$ does not depend on the family, $C(p,d)\ne0$ implies that **every** family is avoided by some $f_c$. This is Alon's Combinatorial Nullstellensatz, made explicit.

**Step 2 (the coefficient identity).** Strip off the factor $i=0$, then apply the power-sum identity $\sum_{x\in\mathbb F_p}x^e=-[\,e\ge1,\ (p-1)\mid e\,]$ twice, together with Wilson's theorem. This turns the coefficient into a character sum over monic polynomials:
$$C(p,d)=\sum_{F\text{ monic},\ \deg F=d}N(F)^d,\qquad N(F)=\prod_{a\in\mathbb F_p^*}F(a).$$

**Step 3 (generating function).** $\chi(F)=N(F)^d$ is completely multiplicative, so $L(u)=\sum_F\chi(F)u^{\deg F}$ has an Euler product over monic irreducibles. Its logarithmic derivative has $n$-th coefficient
$$s_n=\sum_{\beta\in\mathbb F_{p^n}}\prod_{\sigma=0}^{n-1}\bigl(\beta^{(p-1)p^\sigma}-1\bigr)^d .$$
Expanding binomially and using power sums in $\mathbb F_{p^n}$, a base-$p$ digit argument shows that only "constant digit" terms survive. This gives $s_n=-\sum_{t=1}^d\gamma_t^{\,n}$ with $\gamma_t=(-1)^{d-t}\binom dt$. Hence
$$L(u)\equiv\prod_{t=1}^d(1-\gamma_tu)\pmod{u^p}.$$

**Step 4.** Reading off the coefficient of $u^d$:
$$C(p,d)=\prod_t(-\gamma_t)=(-1)^{d(d+1)/2}\prod_{k=0}^d\binom dk .$$
This is nonzero mod $p$ because $d<p$. This proves Theorem 2, and with it Theorem 1(1). The count $\ge p-d$ follows from the Alon–Füredi theorem. The prescribed value at one point follows from the Nullstellensatz applied with a $(d+1)$-element set in the $c_0$ coordinate. For example, at $p=7$ the values $C(7,d)$ for $d=0,\dots,6$ are $1,6,5,2,5,6,1$.

The full proofs are in §§1–2 of [`solution.md`](solution.md). The identity was also checked numerically in several independent ways (see `logs/`).

## Theorem 5 is computer-assisted

For $d=p-3$, let $C_i=\mathbb F_p\setminus A_i$, so $|C_i|=3$. A family is blocking iff $0\notin\sum_iC_i\,(1,i,i^2)$, a sumset in $\mathbb F_p^3$ (Lemma 3.1). After normalisations that are proved in the write-up (Lemmas 3.2–3.4), this becomes a finite search. The search was carried out by three programs, written independently, using different reductions:

| program | reduction | $p=11$ | $p=13$ |
|---|---|---|---|
| `indep_k3.c` | normalisation N1 (Lemma 3.3) | 8,984,250 cases, 0 blocking | — |
| `dualk3c.c` / `dualk3d.c` | normalisation N2 (Lemma 3.4), plus the symmetry $x\mapsto3x$ at $p=13$ | 5,823,125 cases, 0 blocking | 32,533,176 cases (2/3 skipped by symmetry), 0 blocking |
| `boxsearch/boxsearch.c` (written by a reviewer) | box formulation (Remark 3.5): no normalisation, any $Z$ | 6 runs, 0 blocking | 2 runs ($Z=\{1,2,3\}$ and $\{2,5,11\}$), 0 blocking |

The search code was validated in four ways:

- the DFS of `indep_k3` was compared with a pruning-free enumeration at $p=5,7$ (earlier runs, not repeated here, also compared the per-box verdicts of `dualk3d` and its predecessors with the SAT solver CaDiCaL);
- every family found at $p=7$, where blocking families do exist, was checked against all $7^4$ polynomials;
- the box search was compared end to end with a brute-force program at $p=7$;
- the completeness of normalisation N1 was tested at $p=7$.

**Caveats.** Theorem 5 rests on these computations. No machine-checkable certificate (such as a DRAT proof) was produced, and all of the programs were written by AI instances. The reductions themselves are proved, without computer assistance, in §3.4 of the write-up.

## Two readings of (Q2)

The question "is $d$ the lowest possible degree bound?" can be read in two ways (§3.6 of the write-up).

- **Per pair $(p,d)$.** This is our reading, and it matches the poster's own examples. Here the answer is **no in general**, by Theorem 5 at $(11,8)$ and $(13,10)$.
- **As a bound depending on $d$ alone, uniformly over all primes $p>d$.** Here $d$ is the least uniform bound iff *some* prime $p>d$ admits a blocking family. The answer is **yes** for $d=1,2$ and whenever $d+1$ or $d+2$ is prime, using the $d=p-1$ and $d=p-2$ constructions with $p=d+1$ or $p=d+2$. It is **open** for the remaining $d$: those with $d+1$ and $d+2$ both composite, namely $d=7,8,13,14,19,20,\dots$. For example, for $d=8$ Theorem 5 excludes only $p=11$, and $p=13,17,\dots$ remain open.

## Open cases

- Sharpness (existence of a blocking family) for $p=11$ with $3\le d\le7$, for $p=13$ with $3\le d\le9$, and for every $p\ge17$ with $3\le d\le p-3$.
- (Q2) in the uniform reading, for $d=7,8,13,14,\dots$.
- A heuristic conjecture: for $p\ge11$, $d$ is sharp exactly when $d\in\{1,2,p-2,p-1\}$. This is based only on local-search data (§3.5). It is not a result.
- Obstacles: the method used for $d=p-3$ does not scale. At $(11,7)$ there are about $10^{10}$ boxes, and SAT solvers did not finish on $(11,3)$.

## Repository layout

```
README.md              this file
solution.md            full write-up: statements, proofs, search reductions, reproduction tables
code/existence/        checks of Theorems 1 and 2 (Python, one C program)
code/sharpness/        Propositions 3 and 4, and the Theorem 5 searches (indep_k3.c, dualk3c.c, dualk3d.c)
code/sharpness/boxsearch/   the box-formulation search of Remark 3.5, with its validators
scripts/quick_check.sh runs the quick (and optionally the medium) checks and prints PASS/FAIL
logs/                  outputs of the runs reported in solution.md (2026-10-08)
```

## Reproducing

You need Python 3 with `numpy` and `sympy`, and a C compiler. Everything was tested on macOS (Apple silicon) with Python 3.9.6, numpy 2.0.2, sympy 1.14.0 and Apple clang 21. Running times below are for one core on that machine.

**Quick checks (about 40 seconds in total):**

```sh
scripts/quick_check.sh
```

This runs the following and prints PASS/FAIL for each. Outputs go to `out/quick/`, and `logs/` is not touched.

- the identity of Theorem 2, checked by brute force over monic polynomials, in extension fields, and by direct sympy expansion of the coefficient;
- the Lemma 2.1 identity on random families;
- the closed form for all $p\le61$;
- the constructions of Propositions 3 and 4;
- the DFS-versus-enumeration and normalisation tests at $p=5,7$;
- the box-search validators;
- **a complete run of Theorem 5 at $(11,8)$ by the box search (about 10 s).**

**Medium checks (about 17 minutes in total, using up to 3 cores):**

```sh
scripts/quick_check.sh --medium
```

| check | time |
|---|---|
| `verify_L.py`: the generating-function identity, separate code, $p\le13$ | ≈ 75 s |
| `run_coef_direct.sh`: dense expansion of $P$ itself for random families, 146 runs | ≈ 30 s on 3 cores |
| `endtoend_11_8.py`: 4,665 families at $(11,8)$, with an explicit avoider $f$ for each | ≈ 40 s |
| `run_boxsearch.sh p13`: **a complete run of Theorem 5 at $(13,10)$** by the box search | 3 × 3.7 min in parallel |
| `verify_exist.py`: Theorem 1 by exhaustive search for $p\le5$, plus adversarial search at $p=7,11$ | ≈ 10–12 min |

On 2026-10-08 all 21 quick and medium checks passed in a fresh clone of this repository.

**Long runs.** These were not repeated in the fresh-clone test. Their logs from 2026-10-08 are in `logs/`.

| command | what | time |
|---|---|---|
| `code/sharpness/run_sharpness_searches.sh` | Theorem 5 with `indep_k3` ($p=11$), `dualk3c` ($p=11$) and `dualk3d` ($p=13$), as 13 jobs | ≈ 2.8 CPU-hours; ≈ 1 hour on 3 cores (each job < 18 min) |
| `code/sharpness/boxsearch/run_boxsearch.sh p13full` | Theorem 5 at $p=13$ by the box search without the scaling reduction, $Z=\{2,5,11\}$ | ≈ 80 CPU-minutes (6 × 13 min) |

`run_sharpness_searches.sh` and `run_boxsearch.sh` write into `logs/` by default, overwriting the committed logs, so `git diff logs/` shows what changed. Set `LOGDIR` for the box search, and for `run_coef_direct.sh`, to write somewhere else. Section 4 of `solution.md` lists every command with its log file.

## AI disclosure and authorship

- **Author:** Nathan Durfee, as composer and prompter. He conceived and directed the project. He has **not** personally verified the mathematics.
- **Mathematics, code and text:** produced by Claude (Anthropic, model Claude Opus 5.5). The process was as follows.
  1. Several independent exploratory attempts.
  2. A combined write-up in which every proof was re-derived and every computation re-run.
  3. Adversarial review by three separate Claude instances, covering logic, computation, and statement/novelty.
  4. A final freshness check of the literature.

  The reviewers found no error. Their minor corrections are incorporated: the §3.4 wording, code comments, a note on what the search validation does and does not cover, and the two readings of (Q2). One reviewer wrote the box-formulation search (`code/sharpness/boxsearch/`).
- **No human referee** has checked any part of this. Treat it as an unrefereed preprint. In particular, Theorem 5 depends on AI-written search code (see the caveats above).

## Novelty

To our knowledge, there is no prior solution of either part of the question as of 2026-10-08. The searches made were:

- the MathOverflow / StackExchange API: the question has 0 answers, one comment on the degree of the zero polynomial, and no linked questions;
- keyword searches on MathOverflow and Mathematics Stack Exchange;
- the arXiv API, with targeted queries and scans of recent math.CO, math.NT and cs.IT listings;
- general web search, including the exact title;
- GitHub code, issue and repository search, including `the-omega-institute/trureturing`;
- Zenodo and OpenAlex;
- the OpenAI release of 2026-10-06 (`github.com/openai/math`).

Semantic Scholar was rate-limited and Google Scholar was not searched, so a prior solution elsewhere cannot be excluded. We do not claim that the closed form of Theorem 2 is new, since it may appear elsewhere in another form. Related but different work includes matrix choosability (DeVos) and nowhere-zero points of linear maps (Alon–Jaeger–Tarsi, Nagy–Pach, Jafari); references are in `solution.md`.

## License

- Code (`code/`, `scripts/`): [MIT](LICENSE).
- Documents (`README.md`, `solution.md`, `logs/`): [CC BY 4.0](LICENSE-docs.md).

Both are copyright © 2026 Nathan Durfee. The question itself is by Michael Ren on MathOverflow (CC BY-SA 4.0).
