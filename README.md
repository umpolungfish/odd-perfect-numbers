# Odd Perfect Numbers — Euler's Theorem and Touchard's Congruence

Machine-verified proofs in Lean 4 / Mathlib4.

A **perfect number** is a positive integer $n$ whose divisors sum to $2n$. Even perfect numbers are completely understood — they correspond to Mersenne primes via the Euler–Euclid theorem. Whether any *odd* perfect number (OPN) exists is one of the oldest open problems in mathematics: no OPN has ever been found, and none has been ruled out. The problem is characterized by slowly tightening necessary conditions — each new result constraining what an OPN *would* look like without settling whether such an object exists.

This repository formalizes two of the oldest and most foundational constraints: Euler's structure theorem (1747) and Touchard's congruence (1953). Both are necessary conditions on any hypothetical OPN. Neither approaches a proof of nonexistence. That gap — between precise characterization and existence — is part of what the formalization makes explicit.

## What this proves

**Euler's theorem (1747)** — `euler_opn_form`

Every odd perfect number $n$ has the form $n = p^k \cdot m^2$ where:
- $p$ is prime
- $p \equiv k \equiv 1 \pmod{4}$
- $p \nmid m$

The proof turns on a single $2$-adic valuation constraint: since $n$ is odd, $\sigma(n) = 2n$ carries exactly one factor of $2$. Distributing this across the prime factorization via multiplicativity of $\sigma$ forces exactly one prime to have $v_2(\sigma(p^{a_p})) = 1$ and all others to have $v_2 = 0$. Mod-4 case analysis then pins down the residue class of that prime and its exponent; the remaining primes are forced to have even exponents, which gives the $m^2$ factor.

The argument is so tight — exactly one prime, exactly one exponent pattern — that it feels like the object is being painted into a corner. But the corner is not empty, or at least has not been proved empty.

**Touchard's congruence (1953)** — `touchard_congruence`

Any odd perfect number $n$ satisfies $n \equiv 1 \pmod{12}$ or $n \equiv 9 \pmod{36}$.

The proof combines the Euler form with a $3$-adic case analysis depending on whether $3 \mid n$. The dependence on Euler is not incidental: the $3$-adic argument applies specifically to the Euler form components, and the full condition $k \equiv 1 \pmod{4}$ (not just oddness of $k$) is needed to force the modular residues that Touchard exploits. The two results share an arithmetic skeleton.

`touchard_congruence` is unconditional — it calls `euler_opn_form` internally rather than assuming the Euler form as a hypothesis.

## Proof architecture

The formalization is structured in five layers, each depending necessarily on the one below:

| Layer | Contents |
|-------|----------|
| 1 — Arithmetic helpers | `geom_sum_mod2`, `geom_sum_mod4`, `geom_sum_mod3_q2`: modular arithmetic on geometric sums |
| 2 — $2$-adic valuation | `v₂_mul`, `v₂_odd`, `v₂_prod`, `v2_eq_one_of_mod4_eq2` |
| 3 — Valuation of $\sigma(p^a)$ | `sigma_prime_pow_mod2/mod4_of_p1/mod4_zero_of_p3` and specialized $v_2$ lemmas |
| 4 — Euler's theorem | `v2_sigma_odd_perfect`, `sigma_prod_factorization`, `euler_opn_form` |
| 5 — Touchard's congruence | `sigma_dvd3_of_p2_kodd`, `touchard_congruence` |

The $2$-adic and $3$-adic analyses (Layers 3–4 and Layer 5) are structurally parallel but operationally independent.

## Key lemmas

| Name | Statement |
|------|-----------|
| `sigma_mul_of_coprime` | $\sigma(ab) = \sigma(a)\cdot\sigma(b)$ for coprime $a$, $b$ |
| `opn_product_constraint` | $\sigma(p^k)\cdot\sigma(m^2) = 2\cdot p^k m^2$ |
| `sigma_prime_pow_ratio` | $\sigma(p^k)\cdot(p-1) + 1 = p^{k+1}$ |
| `v2_sigma_prime_power` | $v_2(\sigma(p^k)) = 1$ when $p \equiv k \equiv 1 \pmod{4}$ |
| `v2_sigma_square_factor` | $v_2(\sigma(q^{2e})) = 0$ for any odd prime $q$ |
| `sigma_dvd3_of_p2_kodd` | $3 \mid \sigma(p^k)$ when $p \equiv 2 \pmod{3}$ and $k$ odd |

## Files

| File | Description |
|------|-------------|
| `OddPerfectNumbers.lean` | Full Lean 4 formalization (~600 lines) |
| `Euler_&_Touchard.md` | Expository paper with proof narrative and formalization details |
| `Euler_&_Touchard.pdf` | Compiled PDF of the above |
| `lakefile.lean` | Lake build configuration |
| `lean-toolchain` | Pinned Lean toolchain version |

## Building

Requires [Lean 4](https://leanprover.github.io/) and [Mathlib4](https://github.com/leanprover-community/mathlib4).

```bash
lake build OddPerfectNumbers
```

The `lakefile.lean` references Mathlib4 via a local relative path (`../mathlib4_PROOFS/mathlib4`). To use the published Mathlib instead, replace that block with a `git` require (see the comment in `lakefile.lean`) and run `lake update`.

Toolchain: `leanprover/lean4:v4.30.0-rc2`

## References

- Euler, L. (1747). *De numeris perfectis*. Opera Omnia I.2, 86–162.
- Touchard, J. (1953). *On prime numbers and perfect numbers*. Scripta Math. 19, 35–39.
- Ochem, P. and Rao, M. (2012). *Odd perfect numbers are greater than $10^{1500}$*. Math. Comp. 81, 1869–1877.
- The Mathlib Community. *Mathlib4*. https://github.com/leanprover-community/mathlib4

## Author and license

**Author:** umpolungfish

Released to the public domain under the [UNLICENSE](https://unlicense.org).

## Citation

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.19909057.svg)](https://doi.org/10.5281/zenodo.19909057)
