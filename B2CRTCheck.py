#!/usr/bin/env python3
"""Finite exact-integer test of the B2 CRT quadratic-correlation reduction.

This is a diagnostic test only, not a proof of OpenAI 11/12 or of meanSqK.
Program director: Maicol Borghetti. Test prepared with GPT-6.
"""
from collections import Counter
from math import gcd, isqrt


def primes_upto(n: int) -> list[int]:
    sieve = bytearray(b"\x01") * (n + 1)
    sieve[0:2] = b"\x00\x00"
    for p in range(2, isqrt(n) + 1):
        if sieve[p]:
            sieve[p*p:n+1:p] = b"\x00" * ((n - p*p)//p + 1)
    return [p for p in range(2, n + 1) if sieve[p]]


def jacobi(a: int, n: int) -> int:
    assert n >= 1 and n % 2 == 1
    a %= n
    sign = 1
    while a:
        while a % 2 == 0:
            a //= 2
            if n % 8 in (3, 5):
                sign = -sign
        a, n = n, a
        if a % 4 == n % 4 == 3:
            sign = -sign
        a %= n
    return sign if n == 1 else 0


def test_crt() -> None:
    U, m, a = 100_000, 24, 1
    P = [q for q in primes_upto(U) if isqrt(U) < q and q % m == a]
    assert len(P) == 1176
    expected = {(5, 7): -22, (5, 11): -6, (7, 13): 12, (11, 17): -18}

    for (p, r), target in expected.items():
        assert gcd(m, p*r) == 1 and p != r
        M = m*p*r
        R = [b for b in range(1, M) if b % m == a and gcd(b, M) == 1]
        assert len(R) == (p - 1)*(r - 1)
        sigma = {b: jacobi(p, b)*jacobi(r, b) for b in R}
        assert all(abs(x) == 1 for x in sigma.values())
        assert sum(sigma.values()) == 0
        counts = Counter(q % M for q in P)
        direct = sum(jacobi(p, q)*jacobi(r, q) for q in P)
        by_classes = sum(sigma[b]*counts[b] for b in R)
        assert direct == by_classes == target
        print(f"p={p} r={r}: R={len(R)} sign-sum=0, correlation={direct}")

    print(f"PASS: {len(P)} primes; all 4 CRT reductions exact.")


if __name__ == "__main__":
    test_crt()
