# B₂: a candidate exception-free replacement for Alpöge's `QH.twistK`

**Scientific direction:** Maicol Borghetti — Laboratorio Teoria dello Zero (RH)  
**Assisted derivation and formal proof engineering:** GPT-6  
**Date:** 23 November 2026  
**Status:** Mathematical derivation from a cited external OpenAI quantitative AP corollary. **Not** a complete Lean proof of `twistK` or `meanSqK`; not a proof of RH or GRH. Priority of any mathematical novelty is **not** established.

## 1. Precise lemma to replace

Alpöge's [`twistK.lean`, pinned source lines 148–151](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AutomorphicArithmetic/MeanSquareBounds/twistK.lean) proves

```
∀ ε A B : ℝ, 0<ε → 0<A → 0<B → ∃ Y₀,
∀ Y≥Y₀, ∀ U m₀ a₀, QH.admitted ε Y U m₀ a₀ →
∃ nstar : ℕ, ∀ s : ℕ,
  1<s → Odd s → Squarefree s → s.Coprime m₀ →
  (s : ℝ)≤Y^A → s≠nstar →
|∑ q ∈ PPset m₀ a₀ U, jacobiSym(q,s)| ≤ Y^(−B) |PPset|.
```

The original `QH.meanSqK` invokes this with `A=800K`, `B=K+1` ([source lines 51–73](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AutomorphicArithmetic/MeanSquareBounds/meanSqK.lean)). The proposed replacement proves the same conclusion for **every** admissible `s`, then chooses `nstar=2`. Since `s` is odd, `s≠2` automatically.

This keeps the original mean-square framework (`meanSq_abs`, `sPsq_le`, `RR_le`, `sum_cN_le`) intact and targets `twistK` (356 lines) directly. It does **not** claim 356 lines are already removed.

## 2. External input

OpenAI, *The Quasi-Riemann Hypothesis*, October 5, 2026, [paper2.tex, corollary `cor:primes-ap`](https://github.com/openai/math/blob/main/preprints/The-Quasi-Riemann-Hypothesis-October-5-2026/build/paper2.tex), gives for `x≥2, 1≤M≤x, (b,M)=1`, with absolute effective `C_AP`,

```
|π(x;M,b) − Li₂(x)/φ(M)| ≤ C_AP x^(11/12) log x,
Li₂(x)=∫₂ˣ dt/log t.
```

**Crucial:** this is an explicitly stated corollary in the **paper**, not an available imported quantitative Lean theorem in the pinned OpenAI repository. Formalizing or importing this corollary remains a genuine gate.

## 3. Modulus scale, uniform in the Alpöge parameters

From `QH.admitted ε Y U m a`,

```
(log Y)² log m / 4 ≤ log U,       log U ≥ Y^(ε/6).
```

For `s≤Y^A`,

```
log (m s)/log U ≤ 4/(log Y)² + A log Y / Y^(ε/6) → 0.
```

Choose `Y₀(ε,A)` so that `m s≤U^(1/64)<sqrt U`. All large prime `q∈PPset(m,a,U)` are therefore coprime to `m s`. This also permits applying the OpenAI AP corollary with modulus `m s`.

## 4. The squarefree Jacobi character has exactly zero mean

Let `R=clsB m s a={b mod(m s):b≡a(modm), gcd(b,s)=1}`. Since `(m,s)=1`, CRT identifies `R` with units modulo `s`, so `|R|=φ(s)≤s`.

For odd squarefree `s>1`, the function `χ_s(b)=(b/s)` is a nonprincipal quadratic character. Choose a prime `p|s` and a nonresidue modulo `p`, with residues `1` at all other prime factors: CRT produces `u≡1(modm)` such that `χ_s(u)=-1`. Multiplication `b↦ub mod(m s)` permutes `R` and reverses every sign. Therefore

```
∑_{b∈R} χ_s(b)=0.
```

**Major formalization shortcut already available in Alpöge:**

- [MSqOrth.lean](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqOrth.lean) provides `exists_jacobi_neg_one` (33–57), `sum_perm` (15–31), `card_cls` (142–175).
- [MSqTwistA.lean](https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqTwistA.lean) already proves `sum_jacobiSym_eq_sum_residueClass`, `cnt_add_small` and `sum_small_le`.

An isolated test of this cancellation, [`B2JacobiClassZero.lean`](B2JacobiClassZero.lean), is being compiled against the actual pinned Alpöge source by [GitHub Actions run 45128105923](https://github.com/maicborg/rh-b1-verification/actions/runs/45128105923). No green outcome is asserted here before inspection.

## 5. Only **one AP endpoint** is needed

The exact Alpöge identities imply

```
∑_{q∈PPset} χ_s(q)
 = ∑_{b∈R} χ_s(b) [π(U;m s,b) − smallCnt(U,m s,b)].
```

Using `∑χ_s=0`, we may subtract the common main term `Li₂(U)/φ(m s)`; the OpenAI AP estimate is applied **only at `x=U`**:

```
|∑_{q∈PPset} χ_s(q)|
 ≤ C_AP |R| U^(11/12) log U
   + ∑_{b∈R}smallCnt(U,m s,b)
 ≤ C_AP s U^(11/12) log U + sqrt U.
```

The last step is exactly the existing `MSqTwistA.sum_small_le`. There is no need for an AP estimate at `x=sqrt U`. This one-endpoint approach is more efficient than the initial two-endpoint version.

The **denominator** must be stronger than the `|PPset|≥U^(9/10)` used elsewhere in Alpöge (because `11/12>9/10`). Applying OpenAI at `x=U` with modulus `m`, then counting small primes in one residue class by `π(sqrt U;m,a)≤sqrt U/m+1`, gives

```
|PPset(m,a,U)| ≥ c U/(m log U)
```

for large `Y`, with `c>0` absolute, since `m≤U^(1/64)`.

Hence

```
|∑χ_s(q)|/|PPset|
  ≪ m s U^(−1/12) (log U)² + m U^(−1/2) log U
  ≪ U^(−13/192)(log U)² + U^(−31/64) log U.
```

Because `log U≥Y^(ε/6)`, both errors are `o(Y^(−B))` for fixed positive `ε,A,B`, uniformly in the other variables. This is precisely the desired `twistK` conclusion, with no exceptional `nstar`.

## 6. What is and is not certified

**Supported:** the external OpenAI paper states the AP estimate; the algebraic number-theoretic reduction above is a paper-level argument reusing exact Lean definitions and known lemmas; the bounded-parameter exponents have been checked; finite tests for nine squarefree moduli including composites passed in [CI 45127117468](https://github.com/maicborg/rh-b1-verification/actions/runs/45127117468).

**Still open in the kernel:** (1) the full sign-cancellation theorem in the pinned Alpöge environment, (2) the absolute quantitative OpenAI AP theorem in Lean, (3) the asymptotic uniform scaling and denominator count, (4) a substitute `QH.twistK` that compiles without depending on the original `twistK`, (5) recompilation of original `QH.meanSqK` and `QH.stage`.

**No new RH or GRH claim.** We do not claim originality without prior-art review; we credit OpenAI's AP theorem and all reused Alpöge lemmas.
