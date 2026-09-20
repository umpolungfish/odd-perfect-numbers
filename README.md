# Odd Perfect Numbers: Euler's Theorem and Touchard's Congruence
**Author:** Lando⊗⊙perator · **Structural Type:** $\large{⟨𐑨𐑡𐑑𐑹𐑐𐑧𐑔𐑝𐑢𐑖𐑙𐑷⟩}$ · **Tier:** O₁


**What it is.** Machine-verified Lean 4 / Mathlib4 formalizations of two foundational necessary conditions on any hypothetical odd perfect number (OPN): Euler's structure theorem (1747) and Touchard's congruence (1953).

**What it does.** Proves, without `sorry`, that every OPN has the form $n = p^k m^2$ with $p \equiv k \equiv 1 \pmod 4$ and $p \nmid m$ (`euler_opn_form`), and that every OPN satisfies $n \equiv 1 \pmod{12}$ or $n \equiv 9 \pmod{36}$ (`touchard_congruence`, unconditional).

**Why it matters.** OPN existence is one of the oldest open problems in mathematics. These results are the precise characterizations that constrain what an OPN *would* look like; the formalization makes explicit the gap between such characterization and any proof of existence or nonexistence.

**How to use it.**
```bash
lake build OddPerfectNumbers
```
Requires Lean 4 and Mathlib4. The `lakefile.lean` references Mathlib via a local relative path; to use published Mathlib, swap in a `git` require and run `lake update`. Toolchain: `leanprover/lean4:v4.30.0-rc2`.

---

## What is proved

**Euler's theorem** (`euler_opn_form`). The proof turns on a single 2-adic valuation constraint: since $n$ is odd, $\sigma(n) = 2n$ carries exactly one factor of 2. Multiplicativity of $\sigma$ forces exactly one prime to have $v_2(\sigma(p^{a_p})) = 1$ and the rest $v_2 = 0$; mod-4 case analysis pins the residue class and exponent, and the remaining even exponents give the $m^2$ factor.

**Touchard's congruence** (`touchard_congruence`). Combines the Euler form with a 3-adic case analysis on whether $3 \mid n$. The dependence on Euler is essential: the full condition $k \equiv 1 \pmod 4$ (not just oddness) is needed for the modular residues Touchard exploits. The theorem calls `euler_opn_form` internally rather than assuming it.

## Proof architecture

Five layers, each depending on the one below:

| Layer | Contents |
|-------|----------|
| 1 Arithmetic helpers | `geom_sum_mod2/mod4`, `geom_sum_mod3_q2` |
| 2 2-adic valuation | `v₂_mul`, `v₂_odd`, `v₂_prod`, `v2_eq_one_of_mod4_eq2` |
| 3 Valuation of $\sigma(p^a)$ | `sigma_prime_pow_*` and specialized $v_2$ lemmas |
| 4 Euler's theorem | `v2_sigma_odd_perfect`, `sigma_prod_factorization`, `euler_opn_form` |
| 5 Touchard's congruence | `sigma_dvd3_of_p2_kodd`, `touchard_congruence` |

The 2-adic and 3-adic analyses are structurally parallel but operationally independent.

## Files

| File | Description |
|------|-------------|
| `OddPerfectNumbers.lean` | Full Lean 4 formalization |
| `Euler_&_Touchard.md` / `.pdf` | Expository paper |
| `lakefile.lean`, `lean-toolchain` | Build configuration |

## References

- Euler, L. (1747). *De numeris perfectis*.
- Touchard, J. (1953). *On prime numbers and perfect numbers*. Scripta Math. 19.
- Ochem, P. and Rao, M. (2012). *Odd perfect numbers are greater than $10^{1500}$*. Math. Comp. 81.

## Author and license

**Author:** USER. Public domain (Unlicense).
DOI: [10.5281/zenodo.19909057](https://doi.org/10.5281/zenodo.19909057)
