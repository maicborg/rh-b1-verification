#!/usr/bin/env python3
"""Adversarial finite check for the proposed exceptional-free B2 twistK replacement.

This checks squarefree ODD COMPOSITE s (not only products of two primes),
CRT residue class cancellation and exact Jacobi sums over PPset.
It does NOT prove an asymptotic uniform estimate or the OpenAI AP corollary.

Scientific direction: Maicol Borghetti. Python check: GPT-6.
"""
from collections import Counter
from math import gcd, isqrt
from B2CRTCheck import primes_upto, jacobi


def factor_squarefree(n):
    p = 2
    factors = []
    while p * p <= n:
        if n % p == 0:
            factors.append(p)
            n //= p
            if n % p == 0:
                raise ValueError("not squarefree")
        p += 1
    if n > 1:
        factors.append(n)
    return factors


def legendre_mod_prime(a: int, p: int) -> int:
    if a % p == 0:
        return 0
    x = pow(a % p, (p - 1) // 2, p)
    return -1 if x == p - 1 else x


def run() -> None:
    U, m, a = 100000, 24, 1
    P = [q for q in primes_upto(U) if isqrt(U) < q and q % m == a]
    assert len(P) == 1176
    values = (5, 7, 35, 55, 65, 77, 91, 143, 385)
    for s in values:
        assert s > 1 and s % 2 == 1 and gcd(s, m) == 1
        factors = factor_squarefree(s)
        M = m * s
        residues = [b for b in range(1, M) if b % m == a and gcd(b, M) == 1]
        phi_s = sum(1 for b in range(1, s) if gcd(b, s) == 1)
        assert len(residues) == phi_s
        signs = {}
        for b in residues:
            j = jacobi(b, s)
            independently = 1
            for p in factors:
                independently *= legendre_mod_prime(b, p)
            assert j == independently
            signs[b] = j
        assert sum(signs.values()) == 0, (s, "nonzero CRT sign sum")
        counts = Counter(q % M for q in P)
        via_residues = sum(signs[b] * counts[b] for b in residues)
        direct = sum(jacobi(q, s) for q in P)
        assert direct == via_residues
        print(
            f"s={s}, factors={factors}, residues={len(residues)}, "
            f"sign_sum=0, Jacobi_corr={direct}"
        )
    print(f"PASS: {len(values)} odd squarefree s tested against {len(P)} primes.")


if __name__ == "__main__":
    run()
