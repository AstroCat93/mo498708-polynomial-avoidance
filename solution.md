# MathOverflow 498708: avoiding $d$-sets with polynomials of degree $\le d$ over $\mathbb F_p$

*Composed and prompted by Nathan Durfee. The mathematics, code and text were produced by Claude (Anthropic, Claude Opus 5.5), with adversarial review by separate Claude instances. Nathan Durfee has not personally verified the mathematics, and no human has refereed this document. Version of 2026-10-08.*

*How it was produced.* Four independent exploratory attempts were combined into this write-up. Every proof was re-derived for it, and every computation that a result depends on was re-run from `code/`, with logs in `logs/`. The few earlier computations that were not re-run are marked "not re-run", and nothing proved depends on them. Three further independent reviews (logic, computation, statement and novelty) found no error; their minor corrections and one simplification are incorporated (§3.4 wording, Remark 3.5, §3.6, §5).

---

## 0. The question and what is proved

**Question ([MathOverflow 498708](https://mathoverflow.net/questions/498708), asked 2025-08-05 by Michael Ren).** Let $p$ be prime and $0\le d<p$. For sets $A_i\subseteq\mathbb F_p$ ($i\in\mathbb F_p$) with $|A_i|=d$:

- **(Q1)** Is there always an $f\in\mathbb F_p[x]$ with $\deg f\le d$ and $f(i)\notin A_i$ for every $i$?
- **(Q2)** If so, is $d$ the least degree bound that always works? That is, for degree $\le d-1$, is there always a *blocking family*: $d$-sets $A_i$ such that every $f$ with $\deg f\le d-1$ has $f(i)\in A_i$ for some $i$?

The poster handled $d=0,1,2,p-2,p-1$ for (Q1), and showed sharpness for $d=1,2,p-2$ (and, trivially, $p-1$).

### Results

| | Statement | Status |
|---|---|---|
| **Theorem 1** | (Q1) holds for **every** prime $p$ and every $0\le d\le p-1$. Moreover, at least $p-d$ polynomials of degree $\le d$ avoid the family, and the value at one prescribed point can be fixed arbitrarily. | **Proved** (complete proof without computer assistance, §2) |
| **Theorem 2** | The Nullstellensatz coefficient satisfies $C(p,d)\equiv(-1)^{d(d+1)/2}\prod_{k=0}^{d}\binom dk\pmod p$, which is nonzero. More generally, $\sum_{F\text{ monic},\,\deg F=k}N(F)^d\equiv[u^k]\prod_{t=1}^d\bigl(1-(-1)^{d-t}\tbinom dt u\bigr)$ for all $k<p$. | **Proved** (§2) |
| **Proposition 3** | Sharpness holds for $d\in\{1,2,p-2,p-1\}$ for every $p$. Consequently it holds for every $1\le d\le p-1$ when $p\le 5$. | **Proved** (§3.2) |
| **Proposition 4** | Sharpness holds for $p=7$ and $d=3,4$, via explicit blocking families. So it holds for every $1\le d\le 6$ at $p=7$. | **Proved**, computer-verified finite check (§3.3) |
| **Theorem 5** | **The answer to (Q2), read per pair $(p,d)$, is negative in general.** For $(p,d)=(11,8)$ and $(p,d)=(13,10)$, *every* family of $d$-sets is avoided by some $f$ with $\deg f\le d-1$. So $d$ is **not** the least degree bound there. | **Proved by exhaustive computer search** (§3.4). At $p=11$ three independently written programs agree (two different normalisations, and the normalisation-free box formulation of Remark 3.5). At $p=13$ two independently written programs agree. No formal proof certificate exists. |
| Open | Sharpness for $p\ge 11$, $3\le d\le p-3$, except the two cases above. | **Not decided.** Heuristic search data only (§3.5). |

So (Q1) is answered **yes** with a complete proof. (Q2), read per pair $(p,d)$, is answered **"not always"** by a computer-assisted counterexample. What remains open is the exact set of pairs $(p,d)$ for which $d$ is sharp. (Q2) can also be read as asking for a bound that depends on $d$ alone, uniformly over all primes $p>d$; under that reading the answer is "yes" for $d=1,2$ and whenever $d+1$ or $d+2$ is prime, and open for all other $d$, the smallest being $d=7$ and $d=8$. See §3.6.

---

## 1. Notation and two standard facts

Throughout, $0^0:=1$. $N(F):=\prod_{a\in\mathbb F_p^{*}}F(a)$ for $F\in\mathbb F_p[x]$. For a power series $G$, $[u^k]G$ is its $k$-th coefficient.

**Fact 1.1 (power sums).** Let $q=p^n$ and let $e\ge0$ be an integer. Then
$$\sigma_q(e):=\sum_{x\in\mathbb F_q}x^e=\begin{cases}-1,& e\ge1\text{ and }(q-1)\mid e,\\ 0,&\text{otherwise}.\end{cases}$$

*Proof.*
- If $e=0$, the sum is $q\cdot1=0$.
- If $e\ge1$, the term $x=0$ contributes $0$. Let $g$ generate the cyclic group $\mathbb F_q^*$. If $(q-1)\mid e$, the sum is $\sum_{j=0}^{q-2}1=q-1=-1$. Otherwise $g^e\ne1$, and the sum is $\sum_j(g^e)^j=\bigl((g^e)^{q-1}-1\bigr)/(g^e-1)=0$. $\square$

**Corollary 1.2.** Let $Q\in\mathbb F_p[y_1,\dots,y_n]$ with $\deg Q\le n(p-1)$. Then
$$\sum_{y\in\mathbb F_p^n}Q(y)=(-1)^n\,[y_1^{p-1}\cdots y_n^{p-1}]\,Q.$$
In particular, the sum is $0$ if $\deg Q<n(p-1)$.

*Proof.* A monomial $y^{e}$ sums to $\prod_j\sigma_p(e_j)$. By Fact 1.1 this is nonzero only if every $e_j\ge p-1$. Since $\sum e_j\le n(p-1)$, that forces $e_j=p-1$ for all $j$, and then the value is $(-1)^n$. $\square$

**Fact 1.3 (interpolation and moments).** For $y:\mathbb F_p\to\mathbb F_p$, the unique polynomial of degree $\le p-1$ with $f_y(i)=y_i$ is $f_y(x)=\sum_i y_i\bigl(1-(x-i)^{p-1}\bigr)$, and
$$[x^m]f_y=-\sum_{i\in\mathbb F_p}y_i\,i^{\,p-1-m}\qquad(1\le m\le p-1).$$

*Proof.* By Fermat, $1-(x-i)^{p-1}$ is the indicator function of $i$. Its $x^m$-coefficient, for $m\ge1$, is $-\binom{p-1}{m}(-i)^{p-1-m}$. We have $\binom{p-1}{m}\equiv(-1)^m$, so for odd $p$ the coefficient is $-(-1)^{p-1}i^{p-1-m}=-i^{p-1-m}$. For $p=2$ signs do not matter. $\square$

---

## 2. Existence: proof of Theorems 1 and 2

Fix $p$ and $d$. If some $|A_i|<d$, enlarging it only makes the problem harder, so assume $|A_i|=d$ for all $i$. For $d=0$ every $f$ works, so assume $1\le d\le p-1$ unless stated otherwise.

### 2.1 Reduction to one coefficient

For $c=(c_0,\dots,c_d)\in\mathbb F_p^{d+1}$ put $f_c(x)=\sum_{j=0}^dc_jx^j$ and
$$P(c)=\prod_{i\in\mathbb F_p}\ \prod_{a\in A_i}\bigl(f_c(i)-a\bigr)\in\mathbb F_p[c_0,\dots,c_d].$$

- $P(c)\neq0$ exactly when $f_c$ avoids the family.
- Each factor is a linear form in $c$ minus a constant, so $\deg P\le pd$.
- The homogeneous part of degree $pd$ is $H(c)=\prod_{i\in\mathbb F_p}f_c(i)^d$, which **does not depend on the family**.

Define
$$C(p,d):=[\,c_0^{\,d}\,c_1^{\,p-1}\cdots c_d^{\,p-1}\,]\,H .$$

**Lemma 2.1 (weighted count).** For every family,
$$\sum_{c\in\mathbb F_p^{d+1}}c_0^{\,p-1-d}\,P(c)=(-1)^{d+1}C(p,d).$$
Hence if $C(p,d)\ne0$, some $f_c$ with $\deg f_c\le d$ avoids the family.

*Proof.* $Q=c_0^{p-1-d}P$ has degree $\le(p-1-d)+pd=(d+1)(p-1)$ in $d+1$ variables. By Corollary 1.2, the sum equals $(-1)^{d+1}[\prod_{j=0}^dc_j^{p-1}]Q=(-1)^{d+1}[c_0^dc_1^{p-1}\cdots c_d^{p-1}]P$. That monomial has degree $pd=\deg H$, so only $H$ contributes, and its coefficient is $C(p,d)$. $\square$

(Lemma 2.1 is Alon's Combinatorial Nullstellensatz [Al], made explicit for the grid $\mathbb F_p^{d+1}$ with exponents $(d,p-1,\dots,p-1)$, all $<p$.)

### 2.2 $C(p,d)$ as a sum over monic polynomials

**Lemma 2.2.** For $1\le d\le p-1$,
$$C(p,d)=A_d,\qquad\text{where }A_k:=\sum_{F\text{ monic},\ \deg F=k}N(F)^d\in\mathbb F_p.$$

*Proof.*

1. **Strip off $i=0$.** $H=f_c(0)^d\prod_{i\ne0}f_c(i)^d=c_0^d\prod_{i\ne0}(c_0+\ell_i)^d$, where $\ell_i=\sum_{j\ge1}c_ji^j$. Taking the coefficient of $c_0^d$ in $H$ forces $c_0$-degree $0$ in the remaining product. Hence $C(p,d)=[c_1^{p-1}\cdots c_d^{p-1}]R$ with $R:=\prod_{i\ne0}\ell_i^{\,d}$.
2. **Turn the coefficient into a sum.** $R$ is homogeneous of degree $d(p-1)$ in $d$ variables. By Corollary 1.2, $C(p,d)=(-1)^d\sum_{c'\in\mathbb F_p^d}R(c')$.
3. **Rewrite the summand.** Write $g_{c'}(x)=\sum_{j=1}^dc_jx^{j-1}$, so that $\ell_i=i\,g_{c'}(i)$. Wilson gives $\prod_{i\ne0}i=-1$, so $R(c')=(-1)^dN(g_{c'})^d$. Hence
$$C(p,d)=\sum_{g:\ \deg g\le d-1}N(g)^d.$$
4. **Pass to monic polynomials.** $\widetilde R(c'):=\prod_{i\ne0}(i^d+g_{c'}(i))^d$ is a polynomial in $c'$ of degree $\le d(p-1)$. Its degree-$d(p-1)$ part is $\prod_{i\ne0}g_{c'}(i)^d=N(g_{c'})^d$. By Corollary 1.2, $\sum_{c'}\bigl(\widetilde R(c')-N(g_{c'})^d\bigr)=0$. As $c'$ ranges over $\mathbb F_p^d$, $x^d+g_{c'}$ ranges over all monic polynomials of degree $d$, so $C(p,d)=A_d$. $\square$

### 2.3 Generating function over $\mathbb F_p$

Put $\chi(F):=N(F)^d$. It is completely multiplicative on monic polynomials, with $\chi(1)=1$. Let
$$L(u):=\sum_{F\text{ monic}}\chi(F)\,u^{\deg F}=\sum_{k\ge0}A_ku^k\in\mathbb F_p[[u]],\qquad \gamma_t:=(-1)^{d-t}\binom dt\quad(1\le t\le d).$$

**Lemma 2.3.** For $1\le d\le p-1$: $\;L(u)\equiv G(u):=\prod_{t=1}^d(1-\gamma_tu)\pmod{u^p}$. That is, $A_k=[u^k]G$ for $0\le k\le p-1$.

*Proof.*

**(a) Euler product.** In $\mathbb F_p[[u]]$,
$$L=\prod_{\pi}(1-\chi(\pi)u^{\deg\pi})^{-1},$$
the product running over monic irreducible $\pi$. There are finitely many $\pi$ of each degree, so the product converges $u$-adically. Modulo $u^{n+1}$ it is a finite product. Expanding the geometric series, the coefficient of $u^m$ ($m\le n$) is $\sum\prod_\pi\chi(\pi)^{e_\pi}$, summed over exponent vectors with $\sum e_\pi\deg\pi=m$. By unique factorisation and complete multiplicativity this equals $\sum_{\deg F=m}\chi(F)=A_m$.

**(b) Logarithmic derivative.** For $G\in1+u\mathbb F_p[[u]]$ put $\mathcal D(G):=uG'/G$.
- $\mathcal D$ turns products into sums.
- $\mathcal D(G)\bmod u^{n+1}$ depends only on $G\bmod u^{n+1}$, so $\mathcal D$ commutes with the $u$-adically convergent product.
- For a single factor, $\mathcal D\bigl((1-au^k)^{-1}\bigr)=kau^k/(1-au^k)=\sum_{m\ge1}k\,a^mu^{km}$.

Hence $\mathcal D(L)=\sum_{n\ge1}s_nu^n$ with
$$s_n=\sum_{k\mid n}\ k\!\!\sum_{\deg\pi=k}\chi(\pi)^{n/k}\qquad(k\text{ read in }\mathbb F_p).$$

**(c) Rewrite $s_n$ as a sum over $\mathbb F_q$, $q=p^n$.**
- We have $\prod_{a\in\mathbb F_p^*}(a-y)=(-1)^{p-1}(y^{p-1}-1)=y^{p-1}-1$ (for $p=2$ the sign is irrelevant).
- Let $\deg\pi=k\mid n$ and let $\beta\in\mathbb F_q$ be a root of $\pi$, so $\pi=\prod_{\sigma<k}(x-\beta^{p^\sigma})$. Then $N(\pi)=\prod_{\sigma<k}(\beta^{(p-1)p^\sigma}-1)$.
- As $\sigma$ runs over $0,\dots,n-1$, $\beta^{p^\sigma}$ runs over the $k$ conjugates, each $n/k$ times. Hence $\chi(\pi)^{n/k}=\Psi_n(\beta)$, where $\Psi_n(\beta):=\prod_{\sigma=0}^{n-1}(\beta^{(p-1)p^\sigma}-1)^d$.
- Every $\beta\in\mathbb F_q$ is a root of exactly one monic irreducible $\pi$, of some degree $k\mid n$, and each such $\pi$ has exactly $k$ roots in $\mathbb F_q$ (because $x^q-x=\prod_{k\mid n}\prod_{\deg\pi=k}\pi$).

Therefore $s_n=\sum_{\beta\in\mathbb F_q}\Psi_n(\beta)$.

**(d) Evaluate the sum.** Expand each factor binomially:
$$\Psi_n(\beta)=\sum_{(k_\sigma)\in[0,d]^n}\ \prod_\sigma\binom d{k_\sigma}(-1)^{d-k_\sigma}\cdot\beta^{(p-1)M},\qquad M=\sum_{\sigma<n}k_\sigma p^\sigma.$$
By Fact 1.1, $\sum_\beta\beta^{(p-1)M}\ne0$ only if $M\ge1$ and $(q-1)\mid(p-1)M$. Equivalently, $\rho:=1+p+\dots+p^{n-1}$ divides $M$.
- Since $0\le M\le d\rho$, this means $M=t\rho$ for some $1\le t\le d\le p-1$.
- The base-$p$ digits of $t\rho$ are all equal to $t$, and the digits $k_\sigma\le d\le p-1$ of $M$ are a base-$p$ expansion. By uniqueness, $k_\sigma=t$ for every $\sigma$.
- Each such tuple contributes $-\bigl(\binom dt(-1)^{d-t}\bigr)^n=-\gamma_t^n$.

So $s_n=-\sum_{t=1}^d\gamma_t^n$.

**(e) Compare with $G$.** $\mathcal D(G)=\sum_t\frac{-\gamma_tu}{1-\gamma_tu}=-\sum_{n\ge1}\sum_t\gamma_t^nu^n=\mathcal D(L)$. So $Q:=L/G\in1+u\mathbb F_p[[u]]$ satisfies $uQ'/Q=0$, i.e. $Q'=0$. Then $mq_m=0$ for all $m$, so $q_m=0$ unless $p\mid m$. Hence $Q\equiv1\pmod{u^p}$, and $L\equiv G\pmod{u^p}$. $\square$

### 2.4 Conclusion

**Theorem 2.** For every prime $p$ and $0\le d\le p-1$:
$$C(p,d)\equiv(-1)^{d(d+1)/2}\prod_{k=0}^d\binom dk\not\equiv0\pmod p .$$
Moreover, $\sum_{\deg F=k,\ F\text{ monic}}N(F)^d\equiv[u^k]\prod_{t=1}^d(1-\gamma_tu)$ for $0\le k\le p-1$. In particular this sum is $0$ for $d<k\le p-1$.

*Proof.* For $d=0$, $H=1$ and $C=1$. For $d\ge1$, Lemmas 2.2 and 2.3 (with $d\le p-1$) give
$$C=A_d=[u^d]G=\prod_{t=1}^d(-\gamma_t)=\prod_{t=1}^d(-1)^{d-t+1}\binom dt=(-1)^{d(d+1)/2}\prod_{t=0}^d\binom dt.$$
Since $d<p$, $p\nmid d!$, so no $\binom dt$ is divisible by $p$. $\square$

For example, at $p=7$ the values for $d=0,\dots,6$ are $1,6,5,2,5,6,1$.

**Theorem 1.** For every prime $p$, every $0\le d\le p-1$ and all $A_i\subseteq\mathbb F_p$ with $|A_i|\le d$:
1. some $f$ with $\deg f\le d$ has $f(i)\notin A_i$ for all $i\in\mathbb F_p$;
2. in fact there are at least $p-d$ such $f$;
3. for any $z\in\mathbb F_p$ and any $s\in\mathbb F_p$, if $s\notin A_z$ (or if $A_z$ is left unconstrained), some such $f$ also satisfies $f(z)=s$.

*Proof.*
1. Theorem 2 and Lemma 2.1.
2. Apply the Alon–Füredi theorem [AF, Thm. 5] to $P$ on the grid $\mathbb F_p^{d+1}$. Here $\deg P\le pd$ and $P$ is not identically zero on the grid by part 1. So $P$ is nonzero at at least $\min\{\prod_jy_j:1\le y_j\le p,\ \sum_jy_j\ge p(d+1)-pd=p\}$ points. That minimum is $p-d$, attained at $y=(p-d,1,\dots,1)$, because $ab\ge a+b-1$ for $a,b\ge1$.
3. After the translation $x\mapsto x+z$, assume $z=0$. Enlarge $A_0$ to a $d$-set not containing $s$ (possible since $d\le p-1$), and apply the Combinatorial Nullstellensatz [Al, Thm 1.2] to $P$ with $S_0=A_0\cup\{s\}$ ($|S_0|=d+1>d$) and $S_j=\mathbb F_p$ ($p>p-1$) for $j\ge1$. The coefficient of $c_0^dc_1^{p-1}\cdots c_d^{p-1}$ is $C(p,d)\ne0$ and $\deg P=pd$. So there is $c$ with $c_0\in S_0$ and $P(c)\ne0$. Then $c_0\notin A_0$, so $c_0=s=f_c(0)$. $\square$

**Remarks.**
- The bound $p-d$ in part 2 is attained for $d=1$, $d=p-2$ and $d=p-1$, and the attaining families are those of §3.2:
  - $d=1$, $A_i=\{i\}$: $f=ax+b$ avoids iff $(a-1)i+b\ne0$ for all $i$, iff $a=1$ and $b\ne0$. That gives $p-1$ avoiders.
  - $d=p-2$, $C_i=\{g(i),g(i)+1\}$ with $\deg g=p-2$: a $y\in\prod C_i$ has $\deg f_y\le p-2$ iff $\sum_i y_i=0$. As in §3.2 this forces $y=g$ or $y=g+1$, so there are exactly $2$ avoiders.
  - $d=p-1$: exactly $1$ avoider.

  At $p=5$ the exhaustive minima (re-run, `logs/verify_exist.txt`) are $4,7,2,1$ for $d=1,\dots,4$, so the bound is attained exactly at $d=1,p-2,p-1$. At $p=7$ an earlier exploratory exhaustive computation (not re-run here) found the minima $6,21,32,30,2,1$ for $d=1,\dots,6$, so the bound is not attained for $2\le d\le p-3$ there.
- Lemma 2.3 is an elementary mod-$p$ shadow of the Jacobi-sum (Stickelberger) description of the relevant Kummer $L$-function. The proof above uses only power sums and unique factorisation.
- One of the exploratory attempts gave a variant of §2.2–2.3 that uses $\sum_{n<d}a_n$ over all $g$ of degree $<d$ together with Newton's identities. Lucas' theorem can replace the digit argument in (d). Both variants lead to the same formula.

---

## 3. Sharpness (Q2)

### 3.1 The moment criterion

Let $1\le d\le p-1$, $k:=p-d$, $C_i:=\mathbb F_p\setminus A_i$ (so $|C_i|=k$), and $v_i:=(i^0,i^1,\dots,i^{k-1})\in\mathbb F_p^k$.

**Lemma 3.1.** $(A_i)$ is a blocking family for degree $\le d-1$ if and only if
$$0\notin\sum_{i\in\mathbb F_p}C_i\,v_i:=\Bigl\{\sum_iy_iv_i:\ y_i\in C_i\Bigr\}.$$

*Proof.* Every function $y$ is $f_y$ for a unique $f_y$ of degree $\le p-1$. By Fact 1.3, $\deg f_y\le d-1$ holds iff $[x^m]f_y=0$ for $m=d,\dots,p-1$, iff $\sum_iy_ii^{j}=0$ for $j=0,\dots,k-1$, iff $\sum_iy_iv_i=0$. A polynomial of degree $\le d-1$ avoids the family iff its value vector lies in $\prod C_i$. $\square$

**Lemma 3.2 (invariances).** The property of being blocking for degree $\le d-1$ is preserved by:
- (a) $C_i\mapsto\lambda C_i+h(i)$, where $\lambda\in\mathbb F_p^*$ and $\deg h\le d-1$;
- (b) $C_i\mapsto C_{\alpha i+\beta}$, where $\alpha\in\mathbb F_p^*$.

*Proof.* $f\mapsto\lambda f+h$ and $f\mapsto f(\alpha x+\beta)$ are bijections of $\{f:\deg f\le d-1\}$ that carry avoiders of one family to avoiders of the other. $\square$

### 3.2 Sharp cases for all $p$ (Proposition 3)

Each of the following families of $d$-sets blocks every $f$ with $\deg f\le d-1$.

- **$d=1$:** $A_i=\{i\}$. A constant $f\equiv c$ has $f(c)=c\in A_c$.
- **$d=2$ ($p\ge3$):** $A_0=\{0,1\}$ and $A_i=\{0,i\}$ for $i\ne0$. Take $f=ax+b$.
  - If $a\ne1$, then $f(i)=i$ at $i_0=-b/(a-1)$. If $i_0\neq0$ we are done. If $i_0=0$ then $b=0$ and $f(0)=0\in A_0$.
  - If $a=1$ and $b=0$, then $f(0)=0\in A_0$.
  - If $a=1$ and $b\ne0$, then $f(-b)=0\in A_{-b}$.
- **$d=p-2$ ($p\ge3$):** $C_i=\{g(i),g(i)+1\}$ with $\deg g=p-2$. If $y\in\prod C_i$, write $y=g+\varepsilon$ with $\varepsilon_i\in\{0,1\}$. By Lemma 3.1 with $k=2$ and $\sum_ig(i)=-[x^{p-1}]g=0$, $y$ is admissible iff $\sum_i\varepsilon_i=0$ and $\sum_ii\,(g(i)+\varepsilon_i)=0$.
  - The first condition forces $|\{i:\varepsilon_i=1\}|\in\{0,p\}$, so $\varepsilon$ is constant.
  - Then $f_y=g$ or $g+1$, which has degree $p-2>d-1$. Contradiction.
- **$d=p-1$:** $C_i=\{y_i\}$, where $y$ is any function with $\sum_iy_i\ne0$. The only candidate has degree $p-1$.

For $p\le5$ every $1\le d\le p-1$ lies in $\{1,2,p-2,p-1\}$. (For $d=0$ the question is vacuous: there are no polynomials of degree $\le-1$ under the poster's convention $\deg0=0$.)

*Machine re-check:* `code/sharpness/verify_poster.py` checks these four constructions for all primes $p\le61$ (log `logs/verify_poster.txt`). `code/sharpness/verify_known.py` checks $d=p-2,p-1$ by moment DP for $p\le23$.

### 3.3 $p=7$, $d=3,4$ (Proposition 4)

Let $\chi(i)=i^3\in\{\pm1\}$ be the quadratic character mod 7.

- $d=3$: $A_0=\{0,1,6\}$ and $A_i=\chi(i)\cdot\{1,2,3\}$ for $i\ne0$.
- $d=4$: $A_0=\{0,1,2,4\}$ and $A_i=i^4\cdot\{0,1,2,6\}$ for $i\ne0$.

Both families block: all $7^3=343$ (respectively $7^4=2401$) polynomials of degree $\le d-1$ were checked directly (`code/sharpness/verify_p7.py`, log `logs/verify_p7.txt`). The exhaustive search in §3.4 also finds 903 normalised blocking families for $(7,4)$, each re-verified by direct enumeration of all 2401 polynomials (`logs/indep_k3_p7_check.txt`).

Together with §3.2, **for $p\le7$, $d$ is sharp for every $1\le d\le p-1$.**

### 3.4 Non-sharpness for $(p,d)=(11,8)$ and $(13,10)$ (Theorem 5)

Here $d=p-3$, so $k=3$, $|C_i|=3$ and $v_i=(1,i,i^2)$. By Lemma 3.1, Theorem 5 says that for $p\in\{11,13\}$ and **every** choice of 3-sets $C_i$,
$$0\in\sum_{i\in\mathbb F_p}C_i(1,i,i^2).$$
Equivalently, some $f$ of degree $\le p-4$ satisfies $f(i)\in C_i$ for all $i$. This is a finite statement, decided by exhaustive search after the following reductions.

Fix three distinct nonzero columns $Z=\{z_1,z_2,z_3\}$. Let $W=\mathbb F_p\setminus Z$; then $|W|=p-3=d$ and $0\in W$. Since $p>3$, a 3-set $S\ni0$ has exactly three translates containing $0$, namely $S-x$ for $x\in S$; they are distinct because no proper nonempty subset of $\mathbb F_p$ is invariant under a nonzero translation. Call $S$ *canonical* if it is the lexicographically least of these three (as sorted triples). Canonical sets will be used for the columns $w\in W\setminus\{0\}$.

**Lemma 3.3 (normalisation N1; used by `indep_k3.c`).** Every family of 3-sets can be moved by a map of type 3.2(a) to a family with:
- $C_0=\{0,1,u\}$, where $u$ is the least element of its orbit $\{u,1-u,1/u,1/(1-u),u/(u-1),(u-1)/u\}$;
- $C_w$ canonical for every $w\in W\setminus\{0\}$;
- $C_z$ ($z\in Z$) arbitrary.

*Proof.*
- Write $C_0=\{a,b,c\}$ in any of its $6$ orders, and set $\lambda=(b-a)^{-1}$. Then $\lambda C_0-\lambda a=\{0,1,u\}$ with $u=(c-a)/(b-a)$.
- Swapping $b,c$ gives $1/u$, and swapping $a,b$ gives $1-u$. These generate the order-6 anharmonic group, so all six orbit values occur, and we choose the order giving the least one.
- Next choose $h$ with $\deg h\le|W|-1=d-1$ by Lagrange interpolation on $W$. Put $h(0)=-\lambda a$. For each $w\in W\setminus\{0\}$, put $h(w)=-x_w$, where $x_w\in\lambda C_w$ is chosen so that $\lambda C_w-x_w$ is canonical. The three translates of $\lambda C_w$ containing $0$ are exactly the sets $\lambda C_w-x$ with $x\in\lambda C_w$. $\square$

**Lemma 3.4 (normalisation N2; used by `dualk3c.c`, `dualk3d.c`).** Order the $\mathrm{AGL}(1,p)$-orbits ("types") of 3-sets by the lexicographically least representative $R_t$. Every family can be moved by maps 3.2(a),(b) to one in which:
- $t$ is the least type occurring;
- $C_0=R_t$;
- every $C_i$ has type $\ge t$;
- $C_w$ is canonical for $w\in W\setminus\{0\}$.

If moreover $\alpha Z=Z$ for some $\alpha\in\mathbb F_p^*$, the map $C_i\mapsto C_{\alpha i}$ preserves these conditions and permutes the $Z$-columns. So a $Z$-box needs to be checked only up to this permutation.

*Proof.*
- Translate the domain (3.2(b)) so that a column of least type $t$ sits at $0$. Then $C_0=mR_t+s$ for some $m\ne0$ and $s$.
- Scale by $\lambda=m^{-1}$ and use $h$ as in Lemma 3.3 with $h(0)=-m^{-1}s$. This makes $C_0=R_t$ (note $0\in R_t$) and makes every $C_w$ canonical.
- Types are invariant under all these maps, so every column keeps type $\ge t$.
- For the last claim: $\alpha\cdot0=0$ and $\alpha W=W$, canonicity is a property of the set alone, and types are unchanged. $\square$

**Search (both programs).** For each admissible $C_0$ and each $Z$-box $(C_z)_{z\in Z}$, set $T:=-\sum_{z\in Z}C_zv_z$ (at most 27 points). Then
$$0\in\sum_iC_iv_i\iff S_W\cap T\ne\varnothing,\qquad S_W:=\sum_{w\in W}C_wv_w .$$
So a blocking family exists iff, for some admissible $C_0$ and $Z$-box, the canonical sets on $W\setminus\{0\}$ can be chosen with $S_W\cap T=\varnothing$.

A depth-first search assigns the $W$-columns one at a time (most-constrained column first).
- Because $0\in C_w$, a partial sumset is contained in every extension of it. So a branch is cut exactly when the partial sumset meets $T$. This test is $(S+av_w)\cap T=\varnothing$ and $(S+bv_w)\cap T=\varnothing$ for a candidate $\{0,a,b\}$, implemented as $S\cap(T-av_w)=\varnothing$.
- When all columns are assigned, the partial sumset is $S_W$ itself.

Hence the DFS is exact.

**Results.**

| $p$ | program | normalisation | $Z$ | cases ($C_0$, $Z$-box) | completions found |
|---|---|---|---|---|---|
| 11 | `indep_k3` (written for this write-up, independently of the others) | N1 | $\{8,9,10\}$ | 8,984,250 | **0** |
| 11 | `dualk3c` (first search) | N2 | $\{8,9,10\}$ | 4,492,125 + 1,331,000 | **0** |
| 13 | `dualk3d` (first search) | N2 + symmetry $x\mapsto3x$ | $\{1,3,9\}$ | 23,393,656 + 8,998,912 + 140,608 (2/3 skipped by symmetry) | **0** |
| 11, 13 | `boxsearch` (written by a reviewer) | none (Remark 3.5) | several | see Remark 3.5 | **0** |

The numbers in this table come from the re-runs in `logs/` (see §4). The original runs of the first search, before this write-up, found 0 in all of the following, consistent with the re-runs (not re-run):
- $p=11$: $Z=\{1,2,3\}$, $\{2,5,7\}$ and $\{8,9,10\}$ with `dualk3c`, and a six-chunk run of `dualk3` without canonical-translate reduction.
- $p=13$: $Z=\{2,5,6\}$ as well as $\{1,3,9\}$, with `dualk3d`.

**Validation of the search code.**
1. **DFS against a pruning-free enumeration.** `indep_k3 p brute` enumerates *all* normalised $W$-assignments and their full sumsets, and compares the DFS verdict for every ($C_0$, $Z$-box) pair.
   - $p=5$: 1,000 pairs (91 with a completion).
   - $p=7$: 85,750 pairs (903 with a completion).
   - **0 mismatches** in both.
2. **Soundness of what is found.** All 903 blocking families found at $p=7$ were verified against all $7^4$ polynomials of degree $\le3$ (0 failures).
3. **Agreement between programs.** At $p=11$, two independently written programs with different normalisations (N1 vs N2) agree, and so does the box search of Remark 3.5. At $p=13$, `dualk3d` and the box search agree.
4. **Earlier cross-checks (first search, not re-run here).**
   - The per-box verdicts of `dualk3`, `dualk3b` and `dualk3d` were compared with the SAT solver CaDiCaL on 2,074 + 7,497 + 14,315 boxes at $p=7$ and several hundred at $p=11,13$, with 0 disagreements.
   - A random end-to-end test at $(11,8)$ explicitly constructs an avoiding $f$, $\deg f\le7$, for 4,665 families (`endtoend_11_8.py`, re-run: `logs/endtoend_11_8.txt`).
5. **Completeness of the normalisation.** The brute-mode test of item 1 compares the DFS with an enumeration *inside* normalisation N1, so it does not test that N1 loses nothing. That rests on Lemmas 3.3 and 3.4, which are proved above. Two further checks address it directly:
   - `check_normalisation_p7.py` (written by a reviewer) normalises the explicit $(7,4)$ blocking family of Proposition 4, and 200 random images of it under the maps of Lemma 3.2, as in Lemma 3.3. Every resulting ($C_0$, $Z$-box) pair is among the 903 found by `indep_k3` (200/200).
   - The box search of Remark 3.5 does not use N1, N2 or any symmetry of $Z$.

**Remark 3.5 (a simpler box formulation; suggested by a reviewer).** Let $Z=\{z_1,z_2,z_3\}$ be *any* three distinct columns and $W=\mathbb F_p\setminus Z$. The vectors $v_{z_1},v_{z_2},v_{z_3}$ form a basis of $\mathbb F_p^3$ (Vandermonde); write points of $\mathbb F_p^3$ in coordinates with respect to this basis. Then $\sum_{z\in Z}C_zv_z=C_{z_1}\times C_{z_2}\times C_{z_3}$ is a *combinatorial box*.

For $w\in W$ write $C_w=D_w+t_w$, where $D_w$ is a fixed representative, containing $0$, of the translation class of $C_w$. Then
$$\sum_iC_iv_i=S_W+\tau+C_{z_1}\times C_{z_2}\times C_{z_3},\qquad S_W:=\sum_{w\in W}D_wv_w,\quad \tau:=\sum_{w\in W}t_wv_w .$$
So $0\notin\sum_iC_iv_i$ iff $S_W$ is disjoint from $-\tau-(C_{z_1}\times C_{z_2}\times C_{z_3})$, which is again a box with sides of size $3$. Conversely, every box $B_1\times B_2\times B_3$ with $|B_j|=3$ arises this way (take all $t_w=0$ and $C_{z_j}=-B_j$). Hence, by Lemma 3.1:

> **A blocking family for degree $\le p-4$ exists iff, for some choice of translation classes $(D_w)_{w\in W}$, the complement of $S_W$ contains a box $B_1\times B_2\times B_3$ with $|B_1|=|B_2|=|B_3|=3$.**

Since $0\in D_w$, $S_W$ only grows as columns are added, so "the complement contains no box" passes to every extension and can be used to prune a depth-first search over the $(p-1)(p-2)/6$ translation classes per column (15 at $p=11$, 22 at $p=13$). Global scaling $C_i\mapsto\lambda C_i$ (Lemma 3.2(a) with $h=0$) lets one restrict the class of the first $W$-column to one representative per scaling orbit; this reduction is optional. The formulation uses only Lemma 3.1 and this scaling: it does not depend on Lemmas 3.3, 3.4 or on the choice of $Z$.

`code/sharpness/boxsearch/boxsearch.c`, written from scratch by a reviewer, implements this. Its box test was compared with a brute-force box search on 3,900 random, realistic and planted inputs at $p=7,11,13$ (0 disagreements). At $p=7$ it was compared end to end with `brute7.c`, which enumerates all $35^3$ $Z$-boxes and all $7^4$ polynomials of degree $\le3$ for each of the $625$ $W$-assignments. Results:

| $p$ | $Z$ | scaling reduction | DFS nodes | result | time (one core) |
|---|---|---|---|---|---|
| 7 | $\{4,5,6\},\{1,2,4\},\{1,3,6\},\{2,3,5\}$ | no | — | 573, 595, 573, 595 blocking $W$-assignments, identical to `brute7` | seconds |
| 11 | $\{1,2,3\}$ | yes | 5,069,550 | **0 found** | ≈ 10 s |
| 11 | $\{1,2,3\}$ | no | 36,709,725 | **0 found** | ≈ 80 s |
| 11 | $\{8,9,10\},\{2,5,7\},\{3,4,9\},\{1,5,10\}$ | yes | ≈ $5.0\cdot10^6$ each | **0 found** | ≈ 10 s each |
| 13 | $\{1,2,3\}$ | yes | 366,320,834 (3 chunks) | **0 found** | ≈ 3.7 min per chunk |
| 13 | $\{2,5,11\}$ | no | $2.68\cdot10^9$ (6 chunks) | **0 found** | ≈ 13 min per chunk (reviewer's run, not re-run) |

All runs except the last were re-run for this repository (`logs/boxsearch/`). This is a third independent confirmation of Theorem 5 at $p=11$ and a second at $p=13$, and it is much faster than the normalised searches.

**Status of Theorem 5.** It is a computer-assisted proof. The mathematical reductions (Lemmas 3.1–3.4, Remark 3.5) are proved above. At $p=11$ the finite search was run with three independently written programs (`indep_k3`, `dualk3c`, `boxsearch`). At $p=13$ it was run with two (`dualk3d`, re-run; `boxsearch`, with two different choices of $Z$). All of these programs were written by AI instances. No machine-checkable certificate (e.g. a DRAT proof) was produced.

### 3.5 What is not decided, and heuristic data (NOT proofs)

Sharpness is **open** for:
- $p=11$, $3\le d\le7$;
- $p=13$, $3\le d\le9$;
- every $p\ge17$ with $3\le d\le p-3$.

Obstacles:
- The $k=3$ method does not extend cheaply. At $k=4$, i.e. $(11,7)$, there are about $10^{10}$ boxes.
- For small $d$, e.g. $(11,3)$, SAT solvers (CaDiCaL, with cube-and-conquer) did not finish within the run limits.

Local search and simulated annealing in the exploratory attempts (not re-run) found the following minimum numbers of avoiders of degree $\le d-1$. These are **upper bounds on the minimum found by search, not proofs of anything**:

| $(p,d)$ | (11,3) | (11,4) | (11,5) | (11,6) | (11,7) | (13,3) | (13,4) | (13,5) |
|---|---|---|---|---|---|---|---|---|
| fewest avoiders found | 7 | 7 | 70 | ≈166 | 96 | 20 | 89 | 493 |

Structured searches found no blocking family at $p=11,13$. These included shift families $A+g(i)$, families of the form $\{\alpha i^e+\beta\}$, and multiplicative or quadratic-character ansätze.

**Conjecture (heuristic only).** For $p\ge11$, $d$ is sharp exactly when $d\in\{1,2,p-2,p-1\}$.

The first-moment heuristic is unreliable here: it also wrongly predicts failure at $d=2$. The moment-LP method of the poster gives no obstruction for $3\le d$. A proof for general $p$ even at $d=p-3$ would need a structure-vs-randomness argument for the sumset $\sum_iD_i(1,i,i^2)$ of $0$-containing 3-sets.

### 3.6 Two readings of (Q2)

The poster asks: "If so, is $d$ the lowest possible degree bound?" This can be read in two ways.

**(R1) Per pair $(p,d)$.** For the given $p$ and $d$, is there a family of $d$-sets that blocks every polynomial of degree $\le d-1$? This is the reading used throughout this document, and it matches the poster's own sharpness examples for $d=1,2,p-2,p-1$, which are per $(p,d)$. Under (R1):
- the answer is **no in general**, by Theorem 5 ($(11,8)$ and $(13,10)$);
- it is yes for $d\in\{1,2,p-2,p-1\}$ for every $p$, and for every $d$ when $p\le7$ (Propositions 3 and 4);
- it is open in the remaining cases listed in §3.5.

**(R2) A bound depending on $d$ alone.** Theorem 1 shows that the degree bound $d$ works for every prime $p>d$ simultaneously. One may ask whether $d$ is the least bound $D(d)$ that works uniformly for all primes $p>d$. That is the case iff there is *at least one* prime $p>d$ with a blocking family of $d$-sets for degree $\le d-1$. Under (R2):
- the answer is **yes** for $d=1,2$, and for every $d$ such that $d+1$ or $d+2$ is prime: take $p=d+1$ with the $d=p-1$ construction, or $p=d+2$ with the $d=p-2$ construction (§3.2);
- the remaining $d$ are those $\ge3$ with $d+1$ and $d+2$ both composite: $d=7,8,13,14,19,20,23,24,25,26,\dots$. For these, every prime $p>d$ satisfies $3\le d\le p-3$ and $p\ge11$, so none is settled by Propositions 3 and 4;
- Theorem 5 does not settle any of them: for $d=8$ it rules out $p=11$ only, and $p=13,17,\dots$ remain open. For $d=7$ every prime $p\ge11$ is open.

So under (R2) the question is **open**, the smallest open cases being $d=7$ and $d=8$. If the heuristic conjecture of §3.5 were true, the answer under (R2) would be **no** for every such $d$.

---

## 4. Reproduction

All paths are relative to the repository root. Tested on macOS (Apple silicon) with Python 3.9 (numpy 2.0, sympy 1.14) and Apple clang 21. At most 3 cores were used, and every single run takes under 40 minutes. `scripts/quick_check.sh` runs the fast checks (about 40 seconds in total) and prints PASS/FAIL for each, and `scripts/quick_check.sh --medium` adds the medium ones (about 17 minutes); the README lists the medium and long runs with their running times.

### Existence (§2)

| command (run in `code/existence/`) | checks | log |
|---|---|---|
| `python3 verify_formula.py` | $A_k(d)=[u^k]\prod(1-\gamma_tu)$ for all $k<p$, $p^k\le3\cdot10^6$, $p\le23$, all $d$; and $C(p,d)=A_d(d)$ = closed form ($p\le31$, where feasible) | `logs/verify_formula.txt` |
| `python3 verify_L.py` | the same identity, separate code ($p\le13$) | `logs/verify_L.txt` |
| `python3 verify_sn.py`, `python3 verify_Sr.py` | step (d): $\sum_{\beta\in\mathbb F_{p^n}}\Psi_n(\beta)=-\sum_t\gamma_t^n$, computed in genuine extension fields | `logs/verify_sn.txt`, `logs/verify_Sr.txt` |
| `python3 verify_C_direct.py` | $C(p,d)$ read directly off the sympy expansion of $\prod_i(\sum_jc_ji^j)^d$, with no reductions | `logs/verify_C_direct.txt` |
| `./run_coef_direct.sh` (compiles `coef_direct.c`) | $C(p,d)$ by dense truncated expansion of $P$ itself for random families $A_i$ (66 runs: all $d$ for $p\le7$, $d\le5$ at $p=11$, $d\le4$ at $p=13$), and of the reduced product of Lemma 2.2 step 1 (80 runs, $p\le61$, $d\le7$/$6$/$5$/$4$ by size), compared with the closed form: **146 runs, 0 mismatches** | `logs/coef_direct.txt` |
| `python3 verify_coef.py` | direct coefficient extraction, and the fact that $c_0^d\prod c_j^{p-1}$ is the only admissible top monomial (observation only) | `logs/verify_coef.txt` |
| `python3 verify_invariant.py` | Lemma 2.1 identity on random families, and that the number of avoiders is $>0$ | `logs/verify_invariant.txt` |
| `python3 closed_form.py` (writes `out/C_table.txt`) | closed form vs Newton-identity route for all $p\le61$; never $0$ | `logs/closed_form.txt` |
| `python3 verify_exist.py` | Theorem 1 by exhaustive search over all families for $p\le5$, plus adversarial local search at $p=7,11$ | `logs/verify_exist.txt` |

### Sharpness (§3)

| command (run in `code/sharpness/`) | purpose | log |
|---|---|---|
| `python3 verify_poster.py` | §3.2 constructions, $p\le61$ | `logs/verify_poster.txt` |
| `python3 verify_known.py` | §3.2 ($d=p-2,p-1$) by moment DP | `logs/verify_known.txt` |
| `python3 verify_p7.py` | §3.3 explicit $p=7$ families | `logs/verify_p7.txt` |
| `clang -O3 -o indep_k3 indep_k3.c && ./indep_k3 5 brute && ./indep_k3 7 brute` | DFS vs pruning-free enumeration | `logs/indep_k3_brute.txt` |
| `./indep_k3 7 \| python3 check_found_p7.py` | the 903 $p=7$ families really block | `logs/indep_k3_p7_check.txt` |
| `./indep_k3 7 > found7.txt && python3 check_normalisation_p7.py found7.txt` | completeness of normalisation N1 at $p=7$ (§3.4, item 5) | printed |
| `./run_sharpness_searches.sh` | Theorem 5: `indep_k3` at $p=11$ (3 chunks), `dualk3c` at $p=11$ ($t=0,1$), `dualk3d` at $p=13$ ($Z=\{1,3,9\}$, all types) | `logs/indep_k3_p11_s*.txt`, `logs/dualk3c_p11_t*.txt`, `logs/dualk3d_p13_*.txt` |
| `python3 endtoend_11_8.py` | random/structured sanity test at $(11,8)$ | `logs/endtoend_11_8.txt` |
| `boxsearch/run_boxsearch.sh quick` | Remark 3.5: box test vs brute force, $p=7$ vs `brute7`, and all of $(11,8)$ (six runs) | `logs/boxsearch/test_hasbox.txt`, `p7_crosscheck.txt`, `box_p11.txt` |
| `boxsearch/run_boxsearch.sh p13` | Remark 3.5: all of $(13,10)$, $Z=\{1,2,3\}$, with scaling (3 chunks) | `logs/boxsearch/box_p13_Z123_c*.txt` |
| `boxsearch/run_boxsearch.sh p13full` | Remark 3.5: all of $(13,10)$, $Z=\{2,5,11\}$, without scaling (6 chunks) | reviewer's logs: `logs/boxsearch/box_p13_Z2511_noscale_c*.txt` |

### Outcome of the re-runs (2026-10-08)

All logs are in `logs/`.

**Existence checks:**
- `verify_formula`: 573 $(p,k,d)$ cases, 0 mismatches. $C=A_d(d)$ matches the closed form for every computed case with $p\le31$.
- `verify_L`, `verify_Sr`, `verify_C_direct`, `verify_invariant`: each reports ALL OK.
- `verify_sn`: 36/36 OK.
- `verify_coef`: all 6 cases equal the closed form.
- `coef_direct`: 146 runs, 0 mismatches.
- `closed_form`: 501 pairs $(p,d)$ with $p\le61$, closed form = Newton route, never $0$. Table in `logs/C_table.txt`.
- `verify_exist`: exhaustive minimum number of avoiders $\ge1$ for all $p\le5$ and all $d$. Adversarial searches at $p=7,11$ never reached $0$.

**Sharpness checks:**
- `verify_poster`: all constructions verified for $p\le61$.
- `verify_known`: True for $p\le23$.
- `verify_p7`: both families block.
- `indep_k3` brute-mode checks: 0 mismatches. All 903 blocking families found at $p=7$ were verified.
- `endtoend_11_8`: 4,665 families, all avoided by some $f$ with $\deg f\le7$.

**Theorem 5 searches**, every chunk ending with `found=0`:

| run | cases checked | DFS nodes | time |
|---|---|---|---|
| `indep_k3` at $p=11$, 3 chunks | $3\times2{,}994{,}750=8{,}984{,}250$ | $1.41\cdot10^9$ | $\approx16$ min per chunk |
| `dualk3c` at $p=11$, $t=0$ / $t=1$ | 4,492,125 / 1,331,000 | $7.0\cdot10^8$ / $6.8\cdot10^7$ | 235 s / 23 s |
| `dualk3d` at $p=13$, $t=0$ (6 chunks) / $t=1$ / $t=2$ | 7,798,076 / 2,999,776 / 46,904 checked, the rest skipped by the $x\mapsto3x$ symmetry | $1.17\cdot10^{10}$ / $1.49\cdot10^9$ / $5.4\cdot10^5$ | $\approx17$ min per chunk |

In each `dualk3d` run, checked plus skipped boxes add up exactly to the stated totals: 23,393,656, 8,998,912 and 140,608.

The box-search runs of Remark 3.5 are summarised in the table there.

---

## 5. Exactly what is proved, and remaining gaps

**Proved without computer assistance (complete proofs):**
- Theorem 1 (existence, (Q1) = yes), for all primes $p$ and $0\le d\le p-1$, including the $\ge p-d$ count and the prescribed value at one point.
- Theorem 2 (closed form of the Nullstellensatz coefficient and of $\sum_{\deg F=k}N(F)^d$ for $k<p$).
- Proposition 3 (sharpness for $d=1,2,p-2,p-1$).
- Lemmas 3.1–3.4 and Remark 3.5 (reductions underlying the searches).

**Proved with computer assistance (finite exhaustive checks):**
- Proposition 4 (sharpness at $p=7$, $d=3,4$; a trivially checkable finite verification of 343 and 2401 polynomials).
- Theorem 5 (non-sharpness at $(11,8)$ and $(13,10)$; exhaustive search with three independently written programs at $p=11$ and two at $p=13$; no formal certificate). **This gives a negative answer to (Q2) read per pair $(p,d)$** (reading (R1) of §3.6).

**Not proved / open:**
- Sharpness at $p=11$, $3\le d\le7$; at $p=13$, $3\le d\le9$; and at all $p\ge17$, $3\le d\le p-3$.
- The conjectured characterisation in §3.5. Everything in §3.5 is heuristic.
- (Q2) under reading (R2) of §3.6, for $d=7,8,13,14,\dots$ ($d\ge3$ with $d+1$ and $d+2$ both composite).
- Two observations from an exploratory attempt, "the target monomial is the unique admissible one" and "Lagrange-coordinate coefficients all equal $C$", are numerical only and are not used anywhere.

**Novelty and literature.** To our knowledge, there is no prior solution of either part of the question as of 2026-10-08. The poster notes that a special case of $d=2$ is ISL 2024 N6. The following searches were made (all by AI agents, on 2026-10-08):
- MathOverflow / StackExchange API: question 498708 has 0 answers, one comment (on the degree of the zero polynomial) and no linked questions, and its body has not been edited since 2025-08-05; keyword searches on MathOverflow and Mathematics Stack Exchange found nothing else on topic.
- arXiv API: targeted keyword queries, and keyword scans of about 800 recent listings in each of math.CO, math.NT and cs.IT.
- General web search, including the exact question title.
- GitHub code, issue and repository search, including the repository `the-omega-institute/trureturing`.
- Zenodo API and OpenAlex keyword searches.
- The OpenAI release of 2026-10-06 (`github.com/openai/math`, a local copy searched for the question number and topic).

Semantic Scholar was rate-limited and Google Scholar was not searched, so a prior solution elsewhere cannot be excluded. The closest related work found concerns matrix choosability and nowhere-zero points of linear maps [DeV, NP21, NP26, Ja]; none of it addresses this problem. The closed form in Theorem 2 may appear elsewhere in another guise (for example in work on Jacobi sums or $L$-functions of Kummer characters), and we do not claim that it is new.

### References

- [Al] N. Alon, *Combinatorial Nullstellensatz*, Combin. Probab. Comput. 8 (1999), 7–29.
- [AF] N. Alon, Z. Füredi, *Covering the cube by affine hyperplanes*, European J. Combin. 14 (1993), 79–83.
- [DeV] M. DeVos, *Matrix choosability*, J. Combin. Theory Ser. A 90 (2000), 197–209.
- [Ja] A. Jafari, *A nowhere-zero point for several linear mappings simultaneously*, arXiv:2608.23647 (2026).
- [MO] M. Ren, *Interpolating a degree $d$ polynomial over $\mathbb F_p$ to avoid sets of size $d$*, MathOverflow question 498708 (2025), https://mathoverflow.net/questions/498708.
- [NP21] J. Nagy, P. P. Pach, *The Alon–Jaeger–Tarsi conjecture via group ring identities*, arXiv:2107.03956 (2021).
- [NP26] J. Nagy, P. P. Pach, *On a group ring identity related to the Alon–Jaeger–Tarsi conjecture*, arXiv:2604.26320 (2026).
