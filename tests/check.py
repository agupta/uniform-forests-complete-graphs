#!/usr/bin/env python3
"""
check.py -- single standalone verifier for

    "Edges of the uniform random forest of K_n are pairwise negatively
    correlated for every n"

Everything is exact: Python integers and fractions.Fraction only.  No floating
point value decides any test.  The irrational constants e, pi, sqrt(2*pi),
zeta(3/2) enter only through rational enclosures that are constructed and
self-tested here.

Usage
-----
    python3 tests/check.py --nmax 260 --quick   # fast, intentionally incomplete
    python3 tests/check.py                      # default proof run, NMAX = 700
    python3 tests/check.py --nmax 650           # least proof-complete seam
    python3 tests/check.py --nmax 1200          # full published seam

NMAX = 650 is the least proof-complete endpoint: the analytic lemmas of the
note hold from n >= 651, so exact 3..650 and analytic n >= 651 leave no gap.
The default NMAX = 700 provides a convenient overlap check.
NMAX = 1200 reproduces the wider seam quoted in Computation A.2 of the note.

Section C (every analytic constant of the note) is independent of NMAX and is
fully exercised at any NMAX.  Only the *finite* half of the proof shrinks when
NMAX is reduced.  A run with NMAX < 650 therefore does not establish the
theorem; without --quick such a run is refused (exit 1), and with --quick it
exits 0 but prints a NOT PROOF-COMPLETE banner naming every block it skipped.

Exit status is 0 if and only if every check passes (and, absent --quick, the
seam is proof complete).

Stdlib only.  Tested on CPython 3.13.
"""

import argparse
import itertools
import math
import sys
from fractions import Fraction as Fr

# Load-bearing theorem constants.  Section B verifies the finite ranges that
# establish these exact values; Section C consumes the same objects in the
# analytic assembly.  Keeping one definition prevents a mutation in the
# assembly from silently disconnecting it from its finite-range certificate.
A_LO = Fr(1647767, 10 ** 6)
A_HI = Fr(17, 10)
EC_MEAN_HI = Fr(1538952, 10 ** 6)
EC_TAIL_HI = Fr(15604, 10 ** 4)

# ---------------------------------------------------------------------------
# 0.  Test harness
# ---------------------------------------------------------------------------

PASS = 0
FAIL = 0
FAILURES = []


def check(tag, ok, detail=""):
    global PASS, FAIL
    if ok:
        PASS += 1
    else:
        FAIL += 1
        FAILURES.append((tag, detail))
        print("FAIL %-46s %s" % (tag, detail))


def report(tag, ok, detail=""):
    """check() plus an always-printed line, for headline quantities."""
    check(tag, ok, detail)
    print("%-4s %-46s %s" % ("PASS" if ok else "FAIL", tag, detail))


def dec(x, k=9):
    """Decimal *display* of an exact Fraction.  Never used in a decision."""
    if isinstance(x, int):
        return str(x)
    n, d = x.numerator, x.denominator
    sign = "-" if n < 0 else ""
    n = abs(n)
    q, r = divmod(n * 10 ** k, d)
    return "%s%d.%0*d" % (sign, q // 10 ** k, k, q % 10 ** k)


# ---------------------------------------------------------------------------
# 1.  Rational enclosures for e, pi, sqrt(2 pi), zeta(3/2), exp
# ---------------------------------------------------------------------------

def _fact(n):
    return math.factorial(n)


# e = sum_{i>=0} 1/i!, and the tail past N satisfies
#   sum_{i>=N} 1/i! = (1/N!) sum_{r>=0} 1/((N+1)...(N+r)) <= (1/N!) sum_r (N+1)^{-r}
#                   = (1/N!)(N+1)/N <= 2/N!    for N >= 2.
_E_TERMS = 25
ELO = sum(Fr(1, _fact(i)) for i in range(_E_TERMS))     # <= e
EHI = ELO + Fr(2, _fact(_E_TERMS))                      # >= e

# Rounding helpers.  Every exponential bound below is rounded outwards to a
# fixed number of decimals, which keeps denominators small without ever
# invalidating the direction of the bound.
_ROUND_DIGITS = 80


def _ceil_frac(x, digits=_ROUND_DIGITS):
    """Smallest multiple of 10^-digits that is >= x."""
    s = 10 ** digits
    return Fr(-((-x.numerator * s) // x.denominator), s)


def _floor_frac(x, digits=_ROUND_DIGITS):
    """Largest multiple of 10^-digits that is <= x."""
    s = 10 ** digits
    return Fr((x.numerator * s) // x.denominator, s)


def sqrt_lo(q, digits=40):
    """Rational L with L <= sqrt(q), q >= 0 rational."""
    assert q >= 0
    s = 10 ** digits
    num = math.isqrt(q.numerator * s * s * q.denominator)
    return Fr(num, q.denominator * s)


def sqrt_hi(q, digits=40):
    """Rational H with H >= sqrt(q)."""
    return q / sqrt_lo(q, digits) if q > 0 else Fr(0)


def _arctan_inv(x, terms):
    """Two-sided enclosure of arctan(1/x) from its alternating series."""
    lo = hi = Fr(0)
    acc = Fr(0)
    for i in range(terms):
        t = Fr(1, (2 * i + 1) * x ** (2 * i + 1))
        acc += t if i % 2 == 0 else -t
        if i % 2 == 0:
            hi = acc          # partial sum ending on a + term is an upper bound
        else:
            lo = acc
    return lo, hi


def _pi_bounds(terms=30):
    a_lo, a_hi = _arctan_inv(5, terms)
    b_lo, b_hi = _arctan_inv(239, terms)
    # pi = 16*arctan(1/5) - 4*arctan(1/239)
    return 16 * a_lo - 4 * b_hi, 16 * a_hi - 4 * b_lo


PI_LO, PI_HI = _pi_bounds()
TWOPI_LO, TWOPI_HI = 2 * PI_LO, 2 * PI_HI
SQRT2PI_LO = sqrt_lo(TWOPI_LO)          # <= sqrt(2 pi)
INV_SQRT2PI_HI = 1 / SQRT2PI_LO         # >= 1/sqrt(2 pi)


_EXP_TERMS = 32


def _frac_series(s, terms=_EXP_TERMS):
    """(sum_{i<terms} s^i/i!, s^terms/terms!) for 0 <= s < 1."""
    tot = Fr(0)
    term = Fr(1)
    for i in range(terms):
        tot += term
        term = term * s / (i + 1)
    return tot, term


def _frac_ub(s, terms=_EXP_TERMS):
    """Upper bound for e^s, 0 <= s < 1 rational.

    sum_{i>=terms} s^i/i! <= (s^terms/terms!) * sum_{r>=0} (s/(terms+1))^r
                          <= (s^terms/terms!) * (terms+1)/terms      (s < 1).
    """
    assert 0 <= s < 1
    tot, term = _frac_series(s, terms)
    return tot + term * Fr(terms + 1, terms)


def exp_pos_ub(x):
    """Upper bound for e^x, x >= 0 rational.

    Split off the INTEGER part first: x = a + s with a = floor(x), s in [0,1),
    then e^x <= EHI^a * _frac_ub(s).

    Doing the reduction by repeated halving instead -- bounding e^{x/2^j} by
    1 + y + y^2/(2(1-y)) with y just under 1/2 and squaring back j times --
    raises a per-step overshoot of about 5% to the power 2^j, and is already
    19% adrift at x = 3 and a factor of ~430 adrift at x = 60.  That is what
    this function used to do; selftest_constants() now asserts the relative
    tightness that would have caught it.
    """
    assert x >= 0
    a = int(x)                      # floor, x >= 0
    return _ceil_frac(EHI ** a * _frac_ub(x - a))


def exp_pos_lb(x, terms=_EXP_TERMS):
    """Lower bound for e^x, x >= 0 rational (integer part + truncated series)."""
    assert x >= 0
    a = int(x)
    tot, _ = _frac_series(x - a, terms)
    return _floor_frac(ELO ** a * tot)


def exp_neg_ub(t):
    """Upper bound for e^{-t}, t >= 0 rational."""
    assert t >= 0
    return _ceil_frac(1 / exp_pos_lb(t))


def exp_neg_lb(t):
    """Lower bound for e^{-t}, t >= 0 rational."""
    assert t >= 0
    return _floor_frac(1 / exp_pos_ub(t))


def zeta32_ub(J=20000, digits=30):
    """Upper bound for sum_{j>=1} j^{-3/2}, via exact head + midpoint tail.

    Tail: x^{-3/2} is convex, so f(j) <= int_{j-1/2}^{j+1/2} f and therefore
    sum_{j>J} j^{-3/2} <= int_{J+1/2}^inf x^{-3/2} dx = 2/sqrt(J+1/2).

    J must be large enough that the tail estimate is not the dominant error:
    the plain tail 2/sqrt(J) at J = 1000 overshoots by about 1.6e-5, which is
    two orders of magnitude more than the margin available in the Theorem U
    far-block constant.  selftest_constants() pins the result two-sidedly.
    """
    S = 10 ** digits
    tot = 0
    for j in range(1, J + 1):
        # j^{3/2} >= isqrt(j^3 * 10^{2d}) / 10^d, so j^{-3/2} <= 10^d/isqrt(...)
        r = math.isqrt(j ** 3 * S * S)
        tot += -((-S * S) // r)          # ceil(S*S / r), i.e. ceil(S * 10^d/r)
    head = Fr(tot, S)
    tail = 2 / sqrt_lo(Fr(2 * J + 1, 2))
    return head + tail


ZETA32_UB = zeta32_ub()


def selftest_constants():
    check("const/e-lower", Fr(27182818, 10 ** 7) < ELO)
    check("const/e-upper", EHI < Fr(27182819, 10 ** 7))
    check("const/e-order", ELO < EHI)
    check("const/pi-encloses",
          Fr(31415926535, 10 ** 10) < PI_LO and PI_HI < Fr(31415926536, 10 ** 10))
    check("const/pi-order", PI_LO < PI_HI)
    check("const/pi-tight", PI_HI - PI_LO < Fr(1, 10 ** 20))
    check("const/sqrt2pi", SQRT2PI_LO ** 2 <= TWOPI_LO)
    check("const/sqrt2pi-tight", SQRT2PI_LO > Fr(250662, 10 ** 5))
    check("const/sqrt-lo", sqrt_lo(Fr(2)) ** 2 <= 2 <= sqrt_hi(Fr(2)) ** 2)
    check("const/exp-ub-lb", exp_pos_lb(Fr(3, 4)) <= exp_pos_ub(Fr(3, 4)))
    check("const/exp-neg-sandwich",
          exp_neg_lb(Fr(7, 2)) <= exp_neg_ub(Fr(7, 2)))
    # e^{-1} is between 0.3678794411 and 0.3678794412
    check("const/exp-neg-1",
          exp_neg_lb(Fr(1)) < Fr(3678794412, 10 ** 10)
          and exp_neg_ub(Fr(1)) > Fr(3678794411, 10 ** 10))
    # zeta(3/2) = 2.61237534868... : pin it two-sidedly, not just "< 3".
    # The old J = 1000 plain-integral tail returned 2.6123911, which this
    # upper guard rejects.
    check("const/zeta32", Fr(2612375, 10 ** 6) < ZETA32_UB < Fr(26123754, 10 ** 7),
          dec(ZETA32_UB, 12))
    # exp_pos_ub must really dominate on a grid
    ok = True
    for num in range(0, 40):
        x = Fr(num, 8)
        if exp_pos_ub(x) < exp_pos_lb(x):
            ok = False
    check("const/exp-grid", ok)
    # ... and it must dominate TIGHTLY, over the whole range of arguments the
    # analytic lemmas actually use (0 <= x <= 60).  This is the check whose
    # absence let a loose exp_pos_ub silently starve every constant in [C].
    worst = Fr(0)
    for num in (0, 1, 3, 8, 17, 40, 121, 320, 400, 480):
        x = Fr(num, 8)
        lb = exp_pos_lb(x)
        ratio = exp_pos_ub(x) / lb - 1
        if ratio > worst:
            worst = ratio
    check("const/exp-enclosure-tight (rel < 1e-12)", worst < Fr(1, 10 ** 12),
          "worst relative width %s over 0 <= x <= 60" % dec(worst, 18))
    # The same tightness demand on the reciprocal bounds, which are what the
    # v_j and w_k lower bounds are built from.
    worstn = Fr(0)
    for num in (0, 1, 3, 8, 17, 40, 121, 320, 400, 480):
        t = Fr(num, 8)
        lo, up = exp_neg_lb(t), exp_neg_ub(t)
        if not (0 < lo <= up):
            worstn = Fr(1)
            break
        r = up / lo - 1
        if r > worstn:
            worstn = r
    check("const/exp-neg-enclosure-tight (rel < 1e-12)",
          worstn < Fr(1, 10 ** 12),
          "worst relative width %s over 0 <= t <= 60" % dec(worstn, 18))
    # e = 2.718281828459045...
    check("const/exp-1-anchored",
          Fr(2718281828, 10 ** 9) < exp_pos_lb(Fr(1))
          and exp_pos_ub(Fr(1)) < Fr(2718281829, 10 ** 9))


# ---------------------------------------------------------------------------
# 2.  Exact combinatorial sequences
# ---------------------------------------------------------------------------

def tree_count(k):
    """t(k) = k^{k-2}, labelled trees on a k-set; t(1) = t(2) = 1."""
    return 1 if k <= 2 else k ** (k - 2)


def t2(k):
    """Trees on a k-set containing one fixed edge: 2 k^{k-3} (k>=3), t2(2)=1."""
    if k < 2:
        return 0
    return 1 if k == 2 else 2 * k ** (k - 3)


def t3(k):
    """Trees on a k-set containing a fixed 2-edge path: 3 k^{k-4}, t3(3)=1."""
    if k < 3:
        return 0
    return 1 if k == 3 else 3 * k ** (k - 4)


def t4(k):
    """Trees on a k-set containing two fixed disjoint edges: 4 k^{k-4}."""
    return 0 if k < 4 else 4 * k ** (k - 4)


def gdeg(k):
    """g(k) = sum over labelled trees on [k] of deg(1)^2."""
    if k <= 0:
        return 0
    if k == 1:
        return 0
    if k == 2:
        return 1
    if k == 3:
        return 6
    return (k ** (k - 2) + 3 * (k - 2) * k ** (k - 3)
            + (k - 2) * (k - 3) * k ** (k - 4))


def binom_row(n):
    """[C(n,0), ..., C(n,n)] by exact integer recurrence."""
    row = [1] * (n + 1)
    c = 1
    for k in range(1, n + 1):
        c = c * (n - k + 1) // k
        row[k] = c
    return row


def build_sequences(nmax):
    """
    Returns dicts indexed 0..nmax:
      A   -- number of forests of K_n                       (A001858)
      Sc  -- sum over forests of c(F)
      Scc -- sum over forests of c(F)(c(F)-1)
      SD  -- sum over forests of D(F) = sum_v deg(v)^2
    """
    A = [0] * (nmax + 1)
    Sc = [0] * (nmax + 1)
    Scc = [0] * (nmax + 1)
    SD = [0] * (nmax + 1)
    A[0] = 1
    T = [tree_count(k) for k in range(nmax + 1)]
    G = [gdeg(k) for k in range(nmax + 1)]
    for n in range(1, nmax + 1):
        rowm = binom_row(n - 1)      # C(n-1, .)
        rown = binom_row(n)          # C(n, .)
        a = 0
        sc = 0
        scc = 0
        sd = 0
        for k in range(1, n + 1):
            anm = A[n - k]
            cm = rowm[k - 1]
            cn = rown[k]
            tk = T[k]
            a += cm * tk * anm
            sc += cn * tk * anm
            scc += cn * tk * Sc[n - k]
            sd += cm * G[k] * anm
        A[n] = a
        Sc[n] = sc
        Scc[n] = scc
        SD[n] = n * sd
    return A, Sc, Scc, SD


def pair_counts(n, A, Sc, Scc, SD):
    """
    (Ne, Nadj, Ndis) from the moment identities of the note (Prop. 2.4).
    Each division is asserted exact -- a strong internal consistency test.
    """
    An = A[n]
    Sm = n * An - Sc[n]
    Sm2 = n * n * An - 2 * n * Sc[n] + Scc[n] + Sc[n]
    Ne = Nadj = Ndis = None
    if n >= 2:
        num = 2 * Sm
        den = n * (n - 1)
        assert num % den == 0, ("Ne not integral", n)
        Ne = num // den
    if n >= 3:
        num = SD[n] - 2 * Sm
        den = n * (n - 1) * (n - 2)
        assert num % den == 0, ("Nadj not integral", n)
        Nadj = num // den
    if n >= 4:
        num = 4 * (Sm2 + Sm - SD[n])
        den = n * (n - 1) * (n - 2) * (n - 3)
        assert num % den == 0, ("Ndis not integral", n)
        Ndis = num // den
    return Ne, Nadj, Ndis


def direct_pair_counts(nmax, A):
    """
    (Ne, Nadj, Ndis) from the *component-peeling* recurrences of the note
    (Prop. 2.2), i.e. by a derivation sharing nothing with pair_counts()
    beyond the forest numbers A(n) themselves.
    """
    Ne = [0] * (nmax + 1)
    Nadj = [0] * (nmax + 1)
    Ndis = [0] * (nmax + 1)
    for n in range(2, nmax + 1):
        row = binom_row(n - 2)
        Ne[n] = sum(row[k - 2] * t2(k) * A[n - k] for k in range(2, n + 1))
    for n in range(3, nmax + 1):
        row = binom_row(n - 3)
        Nadj[n] = sum(row[k - 3] * t3(k) * A[n - k] for k in range(3, n + 1))
    for n in range(4, nmax + 1):
        row = binom_row(n - 4)
        s = sum(row[k - 4] * t4(k) * A[n - k] for k in range(4, n + 1))
        s += sum(row[k - 2] * t2(k) * Ne[n - k] for k in range(2, n - 1))
        Ndis[n] = s
    return Ne, Nadj, Ndis


# ---------------------------------------------------------------------------
# 3.  Brute force ground truth (all edge subsets of K_n, n <= 7)
# ---------------------------------------------------------------------------

def brute_force(n):
    """Enumerate every acyclic edge subset of K_n; return the six sequences."""
    edges = [(i, j) for i in range(n) for j in range(i + 1, n)]
    m = len(edges)
    e0 = edges.index((0, 1)) if n >= 2 else None
    f_adj = edges.index((0, 2)) if n >= 3 else None
    f_dis = edges.index((2, 3)) if n >= 4 else None
    A = Sc = Scc = SD = Ne = Nadj = Ndis = 0
    for mask in range(1 << m):
        par = list(range(n))

        def find(x):
            while par[x] != x:
                par[x] = par[par[x]]
                x = par[x]
            return x

        ok = True
        deg = [0] * n
        cnt = 0
        for idx in range(m):
            if mask >> idx & 1:
                u, v = edges[idx]
                ru, rv = find(u), find(v)
                if ru == rv:
                    ok = False
                    break
                par[ru] = rv
                deg[u] += 1
                deg[v] += 1
                cnt += 1
        if not ok:
            continue
        c = n - cnt
        A += 1
        Sc += c
        Scc += c * (c - 1)
        SD += sum(d * d for d in deg)
        if e0 is not None and mask >> e0 & 1:
            Ne += 1
            if f_adj is not None and mask >> f_adj & 1:
                Nadj += 1
            if f_dis is not None and mask >> f_dis & 1:
                Ndis += 1
    return A, Sc, Scc, SD, Ne, Nadj, Ndis


def brute_force_spanning_trees(n):
    """Spanning trees of K_n: (T, T_e, T_adj, T_dis).  Stark 2011 Thm 1.2."""
    edges = [(i, j) for i in range(n) for j in range(i + 1, n)]
    m = len(edges)
    e0 = edges.index((0, 1))
    f_adj = edges.index((0, 2)) if n >= 3 else None
    f_dis = edges.index((2, 3)) if n >= 4 else None
    T = Te = Tadj = Tdis = 0
    for comb in itertools.combinations(range(m), n - 1):
        par = list(range(n))

        def find(x):
            while par[x] != x:
                par[x] = par[par[x]]
                x = par[x]
            return x

        ok = True
        for idx in comb:
            u, v = edges[idx]
            ru, rv = find(u), find(v)
            if ru == rv:
                ok = False
                break
            par[ru] = rv
        if not ok:
            continue
        T += 1
        s = set(comb)
        if e0 in s:
            Te += 1
            if f_adj is not None and f_adj in s:
                Tadj += 1
            if f_dis is not None and f_dis in s:
                Tdis += 1
    return T, Te, Tadj, Tdis


# ---------------------------------------------------------------------------
# 4.  Section A -- definition-level controls
# ---------------------------------------------------------------------------

A001858_HEAD = [1, 1, 2, 7, 38, 291, 2932, 36961, 561948, 10026505, 205608536]


def section_A(A, Sc, Scc, SD, Ne, Nadj, Ndis):
    print("\n[A] definition-level controls")
    check("A/A001858-head", A[:len(A001858_HEAD)] == A001858_HEAD,
          str(A[:9]))
    for n in range(2, 8):
        bA, bSc, bScc, bSD, bNe, bNadj, bNdis = brute_force(n)
        ok = (bA == A[n] and bSc == Sc[n] and bScc == Scc[n] and bSD == SD[n])
        check("A/brute-moments-n=%d" % n, ok,
              "A=%d Sc=%d Scc=%d SD=%d" % (bA, bSc, bScc, bSD))
        ok = bNe == Ne[n]
        if n >= 3:
            ok = ok and bNadj == Nadj[n]
        if n >= 4:
            ok = ok and bNdis == Ndis[n]
        check("A/brute-pairs-n=%d" % n, ok,
              "Ne=%d Nadj=%s Ndis=%s" % (bNe, bNadj, bNdis))
    # published anchors
    check("A/anchor-n=4", (A[4], Ne[4], Nadj[4], Ndis[4]) == (38, 14, 4, 5))
    check("A/anchor-n=7", (A[7], Ne[7], Nadj[7], Ndis[7])
          == (36961, 9193, 1763, 2251))
    # negative self-test: the comparison must be able to fail
    check("A/selftest-can-fail", not (Ne[7] ** 2 <= Nadj[7] * A[7]))
    # Stark 2011 Theorem 1.2 reproduced by brute force on spanning trees
    for n in range(3, 8):
        T, Te, Tadj, Tdis = brute_force_spanning_trees(n)
        ok = (T == n ** (n - 2) and Te == 2 * n ** (n - 3)
              and Tadj == 3 * n ** (n - 4))
        if n >= 4:
            ok = ok and Tdis == 4 * n ** (n - 4)
            # exact independence of a disjoint pair in the UST
            ok = ok and Tdis * T == Te * Te
            # adjacent pair sits at exactly 3/4
            ok = ok and 4 * Tadj * T == 3 * Te * Te
        check("A/stark-thm1.2-n=%d" % n, ok,
              "T=%d Te=%d Tadj=%d Tdis=%d" % (T, Te, Tadj, Tdis))


# ---------------------------------------------------------------------------
# 5.  Section B -- the exact seam
# ---------------------------------------------------------------------------

def section_B(nmax, A, Sc, Scc, SD, Ne, Nadj, Ndis, ncross):
    print("\n[B] exact integer seam 3 <= n <= %d" % nmax)

    # B0: two independent derivations of the pair counts agree
    dNe, dNadj, dNdis = direct_pair_counts(ncross, A)
    ok = all(dNe[n] == Ne[n] for n in range(2, ncross + 1))
    ok = ok and all(dNadj[n] == Nadj[n] for n in range(3, ncross + 1))
    ok = ok and all(dNdis[n] == Ndis[n] for n in range(4, ncross + 1))
    report("B/two-derivations-agree(n<=%d)" % ncross, ok)

    # B1: the target inequalities
    bad_adj = [n for n in range(3, nmax + 1) if Nadj[n] * A[n] > Ne[n] ** 2]
    bad_dis = [n for n in range(4, nmax + 1) if Ndis[n] * A[n] > Ne[n] ** 2]
    report("B/ADJ 3..%d" % nmax, not bad_adj, "violations: %s" % bad_adj[:5])
    report("B/DIS 4..%d" % nmax, not bad_dis, "violations: %s" % bad_dis[:5])

    bad_adj_strict = [n for n in range(3, nmax + 1)
                      if Nadj[n] * A[n] >= Ne[n] ** 2]
    bad_dis_strict = [n for n in range(4, nmax + 1)
                      if Ndis[n] * A[n] >= Ne[n] ** 2]
    report("B/ADJ strict 3..%d" % nmax, not bad_adj_strict,
           "violations: %s" % bad_adj_strict[:5])
    report("B/DIS strict 4..%d" % nmax, not bad_dis_strict,
           "violations: %s" % bad_dis_strict[:5])

    worst_adj = max((Fr(Nadj[n] * A[n], Ne[n] ** 2) for n in range(3, nmax + 1)))
    worst_dis = max((Fr(Ndis[n] * A[n], Ne[n] ** 2) for n in range(4, nmax + 1)))
    report("B/worst-adjacent-ratio", worst_adj == Fr(7, 9),
           "%s = %s (at n=3)" % (worst_adj, dec(worst_adj, 12)))
    report("B/worst-disjoint-ratio", worst_dis < 1,
           "%s (at n=%d)" % (dec(worst_dis, 12), nmax))

    # B2: Delta(n) and the exact coefficient-pinning identity behind DIS
    mono = True
    mono_adj = True
    prev = None
    prev_adj = Fr(Nadj[3] * A[3], Ne[3] ** 2)
    bad_delta = []
    bad_delta_identity = []
    bad_delta_closed_form = []
    missing_variance_control = None
    for n in range(4, nmax + 1):
        An = A[n]
        Sm = n * An - Sc[n]
        Sm2 = n * n * An - 2 * n * Sc[n] + Scc[n] + Sc[n]
        Em = Fr(Sm, An)
        Em2 = Fr(Sm2, An)
        ED = Fr(SD[n], An)
        Delta = ED - Em - (Em2 - Em * Em) - Fr(4 * n - 6, n * (n - 1)) * Em * Em
        if Delta < 0:
            bad_delta.append(n)
        gap_form = Fr(
            n * (n - 1) * (n - 2) * (n - 3)
            * (Ne[n] ** 2 - Ndis[n] * An),
            4 * An ** 2,
        )
        if Delta != gap_form:
            bad_delta_identity.append(n)
        mu = Fr(Sc[n], An)
        Ec2n = Fr(Scc[n] + Sc[n], An)
        R = Fr((4 * mu ** 2 + 4 * mu - 2) * n - 6 * mu ** 2,
               n * (n - 1))
        Delta2 = (ED - 5 * n) + 2 + 9 * mu + mu ** 2 - Ec2n - R
        if Delta != Delta2:
            bad_delta_closed_form.append(n)
        if n == 4:
            Delta_without_variance = (
                ED - Em - Fr(4 * n - 6, n * (n - 1)) * Em * Em
            )
            missing_variance_control = Delta_without_variance != gap_form
        r = Fr(Ndis[n] * An, Ne[n] ** 2)
        if prev is not None and not (r > prev):
            mono = False
        prev = r
        ar = Fr(Nadj[n] * A[n], Ne[n] ** 2)
        if prev_adj is not None and not (ar < prev_adj):
            mono_adj = False
        prev_adj = ar
    report("B/Delta>=0 4..%d" % nmax, not bad_delta, "%s" % bad_delta[:5])
    report("B/exact Delta-gap identity", not bad_delta_identity,
           "%s" % bad_delta_identity[:5])
    report("B/Delta closed form", not bad_delta_closed_form,
           "%s" % bad_delta_closed_form[:5])
    check("B/negative control: missing Var(m) changes identity",
          missing_variance_control)
    check("B/adjacent-ratio-strictly-decreasing", mono_adj)
    check("B/disjoint-ratio-strictly-increasing", mono)

    # B3: exact ranges required by the analytic lemmas
    # a_n = A(n)/n^{n-2}; n^{n-2} = 1 for n in {1,2} (1^{-1} = 1, 2^0 = 1).
    an = {n: Fr(A[n], 1 if n <= 2 else n ** (n - 2))
          for n in range(1, nmax + 1)}
    check("B/a_2=2", an[2] == 2, str(an[2]))
    check("B/a_80>17/10", an[80] > A_HI, dec(an[80]))
    check("B/display a_80", dec(an[80], 9) == "1.700555369", dec(an[80], 12))
    check("B/display a_4", an[4] == Fr(19, 8), str(an[4]))
    hi = max(n for n in (500, nmax) if n <= nmax)
    bad = [n for n in range(81, hi + 1) if an[n] > A_HI]
    report("B/a_n<=17/10 on 81..%d" % hi, not bad, "%s" % bad[:5])
    bad = [n for n in range(2, hi + 1) if an[n] < A_LO]
    report("B/a_n>=1.647767 on 2..%d" % hi, not bad, "%s" % bad[:5])
    bad = [n for n in range(1, nmax + 1) if an[n] > Fr(5, 2)]
    report("B/a_n<=5/2 on 1..%d" % nmax, not bad,
           "max = %s at n=%d" % (dec(max(an.values())),
                                 max(an, key=lambda n: an[n])))

    Ec = {n: Fr(Sc[n], A[n]) for n in range(1, nmax + 1)}
    Ec2 = {n: Fr(Scc[n] + Sc[n], A[n]) for n in range(1, nmax + 1)}
    bad = [n for n in range(1, nmax + 1) if Ec[n] > 2]
    report("B/E[c]<=2 on 1..%d" % nmax, not bad, "%s" % bad[:5])

    hi41 = min(nmax, 700)
    bad = [n for n in range(41, hi41 + 1) if Ec[n] > EC_TAIL_HI]
    report("B/E[c_j]<=1.5604 on 41..%d" % hi41, not bad, "%s" % bad[:5])
    check("B/split-at-40-is-forced", Ec[40] > EC_TAIL_HI, dec(Ec[40]))
    check("B/display E[c_40]", dec(Ec[40], 9) == "1.561838942", dec(Ec[40], 12))
    check("B/display E[c_41]", dec(Ec[41], 9) == "1.560354926", dec(Ec[41], 12))

    if nmax >= 651:
        bad = [n for n in range(651, nmax + 1)
               if not (Fr(14819, 10 ** 4) <= Ec[n] <= EC_MEAN_HI)]
        report("B/E[c] in [1.4819,1.538952] on 651..%d" % nmax, not bad,
               "E[c_651] = %s" % dec(Ec[651]))
        bad = [n for n in range(651, nmax + 1) if Ec2[n] > Fr(29123, 10 ** 4)]
        report("B/E[c^2]<=2.9123 on 651..%d" % nmax, not bad,
               "E[c^2_651] = %s" % dec(Ec2[651]))
        check("B/display a_651", dec(an[651], 9) == "1.655058038",
              dec(an[651], 12))
        check("B/display E[c_651]", dec(Ec[651], 9) == "1.503838989",
              dec(Ec[651], 12))
        check("B/display E[c^2_651]", dec(Ec2[651], 9) == "2.765376527",
              dec(Ec2[651], 12))

    hi24 = min(nmax, 650)
    bad = [n for n in range(24, hi24 + 1)
           if 2 * SD[n] < (10 * n - 29) * A[n]]
    report("B/E[D]>=5n-29/2 on 24..%d" % hi24, not bad, "%s" % bad[:5])
    check("B/E[D] threshold 24 is sharp",
          all(2 * SD[n] < (10 * n - 29) * A[n] for n in range(7, 24)),
          "fails for every n in 7..23")

    # B4: the termwise adjacent lemma and the surrogate S(n)
    bad = [n for n in range(3, nmax + 1) if 2 * (n - 2) * Nadj[n] >= 3 * Ne[n]]
    report("B/2(n-2)Nadj<3Ne on 3..%d" % nmax, not bad, "%s" % bad[:5])
    bad = [n for n in range(12, nmax + 1) if 2 * (n - 2) * Ne[n] < 3 * A[n]]
    report("B/S(n) holds on 12..%d" % nmax, not bad, "%s" % bad[:5])
    # What fails at n = 11 is the SUFFICIENT CONDITION of the adjacent
    # proposition -- the inequality 2(n-2)(n-mu) >= 3*C(n,2) after inserting the
    # worst admissible mean mu = 2, i.e. 4(n-2)^2 >= 3n(n-1) -- and NOT S(n)
    # itself.  E[c_11] is well below 2, so S(11) may hold, and it does; asserting
    # "S(11) fails" was simply the wrong statement.  n <= 11 is covered by the
    # exact range regardless.
    check("B/mu=2 sufficient condition: fails at 11, holds at 12",
          4 * (11 - 2) ** 2 < 3 * 11 * 10 and 4 * (12 - 2) ** 2 >= 3 * 12 * 11,
          "n=11: 324 < 330 ; n=12: 400 >= 396")
    s_low = [n for n in range(3, min(nmax, 11) + 1)
             if 2 * (n - 2) * Ne[n] < 3 * A[n]]
    print("     %-46s %s"
          % ("B/S(n) on 3..11 (reported, not asserted)",
             "fails at n in %s" % (s_low if s_low else "none")))
    check("B/n^2-13n+16-threshold",
          all((n * n - 13 * n + 16 >= 0) == (n >= 12) for n in range(3, 60)))

    # B5: the identity Ne/A = (n - E[c]) / C(n,2)
    bad = [n for n in range(2, nmax + 1)
           if Fr(n * (n - 1), 2) * Ne[n] != n * A[n] - Sc[n]]
    report("B/Ne identity", not bad, "%s" % bad[:5])
    return an, Ec, Ec2


# ---------------------------------------------------------------------------
# 6.  Section C -- the analytic constants
# ---------------------------------------------------------------------------

def v(j, A, up):
    """One-sided rational bound for v_j = A(j) e^{-j} / j!."""
    f = Fr(A[j], _fact(j))
    return f * (exp_neg_ub(Fr(j)) if up else exp_neg_lb(Fr(j)))


def w(k, up):
    """One-sided rational bound for w_k = k^{k-2} e^{-k} / k!."""
    f = Fr(tree_count(k), _fact(k))
    return f * (exp_neg_ub(Fr(k)) if up else exp_neg_lb(Fr(k)))


def section_C(A, Ec):
    print("\n[C] analytic constants (exact rational enclosures)")

    # ---- Theorem L : a_n >= 1.647767 -------------------------------------
    # R_m(n) >= 1 whenever 9 m (n-m) >= (m+1)^3 ; worst m <= 60 is m = 60.
    NL = 481
    ok = all(9 * m * (NL - m) >= (m + 1) ** 3 for m in range(1, 61))
    report("C/ThmL threshold n>=481 for m<=60", ok,
           "m=60: 9*60*421=%d vs 61^3=%d" % (9 * 60 * 421, 61 ** 3))
    check("C/ThmL threshold sharp at n=480",
          not all(9 * m * (480 - m) >= (m + 1) ** 3 for m in range(1, 61)),
          "9*60*420=%d < 61^3=%d" % (9 * 60 * 420, 61 ** 3))
    QL = 1 + sum(v(m, A, up=False) for m in range(1, 61))
    report("C/ThmL: a_n >= 1.647767", QL >= A_LO, dec(QL))

    # ---- Theorem U : a_n <= 17/10 for n >= 81 -----------------------------
    N0 = 500
    # HEAD  m <= 60 : sum v_m * exp(3m/2n + m^2(m+2)/2n^2), n = 500
    head = Fr(0)
    for m in range(1, 61):
        x = Fr(3 * m, 2 * N0) + Fr(m * m * (m + 2), 2 * N0 * N0)
        head += v(m, A, up=True) * exp_pos_ub(x)
    report("C/ThmU head(500)", head <= Fr(652836237, 10 ** 9), dec(head))

    # MIDDLE  60 < m <= n/2 :  q_m <= 2^{3/2} / (sqrt(2pi) m^{5/2})
    def tail_pow(a, b, p):
        """Upper bound for sum_{j=a+1}^{b} j^{-p}, p = 5/2, via the integral."""
        assert p == Fr(5, 2)
        lo = Fr(2, 3) / (Fr(a) * sqrt_lo(Fr(a)))
        if b is None:
            return lo
        return lo - Fr(2, 3) / (Fr(b) * sqrt_hi(Fr(b)))

    c32 = sqrt_hi(Fr(8))               # >= 2^{3/2}
    c52 = sqrt_hi(Fr(32))              # >= 2^{5/2}
    middle = INV_SQRT2PI_HI * c32 * (
        Fr(5, 2) * tail_pow(60, 80, Fr(5, 2))
        + A_HI * tail_pow(80, None, Fr(5, 2)))
    report("C/ThmU middle (n-free)", middle <= Fr(320544, 10 ** 8), dec(middle))

    # FAR  m > n/2 :  <= (17/10) 2^{5/2} zeta(3/2) / (sqrt(2pi) n)
    far = A_HI * c52 * ZETA32_UB * INV_SQRT2PI_HI / N0
    report("C/ThmU far(500)", far <= Fr(20044700, 10 ** 9), dec(far))

    total = 1 + head + middle + far
    check("C/ThmU displayed total <= 1.676086377",
          total <= Fr(1676086377, 10 ** 9), dec(total, 12))
    report("C/ThmU total at n=500 <= 17/10", total <= A_HI,
           "%s  (margin %s)" % (dec(total), dec(A_HI - total)))

    # ---- Lemma 2 : two-sided E[c_n], n >= 651 -----------------------------
    n0 = 651
    rho = A_LO / A_HI

    P40lo = sum(w(k, up=False) for k in range(1, 41))
    KW = sum(k * w(k, up=True) for k in range(1, 41))
    check("C/ThmMean sum k w_k <= 1", KW <= 1, dec(KW))
    lower = 1 + rho * (P40lo - KW / n0)
    report("C/ThmMean lower: E[c_n] >= 1.4819", lower >= Fr(14819, 10 ** 4),
           dec(lower))

    # upper: head with Theta_k, tail by Robbins
    headc = Fr(0)
    for k in range(1, 41):
        x = Fr(5 * k, 2 * n0) + Fr(k ** 3, 2 * n0 * n0) + Fr(k * k, n0 * n0)
        headc += w(k, up=True) * exp_pos_ub(x)
    headc *= A_HI / A_LO
    report("C/ThmMean head <= 0.518390291", headc <= Fr(518390291, 10 ** 9),
           dec(headc))

    tail = (INV_SQRT2PI_HI *
            (c32 * tail_pow(40, None, Fr(5, 2)) + c52 * ZETA32_UB / n0)
            * Fr(5, 2) / A_LO)
    report("C/ThmMean tail <= 0.018251379", tail <= Fr(18251379, 10 ** 9), dec(tail))

    upper = 1 + headc + tail
    check("C/ThmMean displayed total <= 1.536641670",
          upper <= Fr(1536641670, 10 ** 9), dec(upper, 12))
    report("C/ThmMean upper: E[c_n] <= 1.538952", upper <= EC_MEAN_HI, dec(upper))
    check("C/ThmMean upper < 2", upper < 2)

    # ---- Lemma 3 : E[c_n^2] <= 2.9123, n >= 651 ---------------------------
    U = Fr(0)
    neg_idx = []
    for j in range(1, 41):
        d = Ec[j] - EC_TAIL_HI
        x = Fr(5 * j, 2 * n0) + Fr(j ** 3, 2 * n0 * n0) + Fr(j * j, n0 * n0)
        if d >= 0:
            U += exp_pos_ub(x) * v(j, A, up=True) * d       # theta_j <= Theta_j
        else:
            neg_idx.append(j)
            U += 1 * v(j, A, up=False) * d                  # theta_j >= 1
    report("C/ThmSecondMoment head U <= -0.1873399", U <= Fr(-1873399, 10 ** 7),
           "U = %s ; negative-d indices %s" % (dec(U), neg_idx))
    check("C/ThmSecondMoment U-M is negative",
          U - EC_TAIL_HI < 0, dec(U - EC_TAIL_HI))
    Ec2_bound = ((U - EC_TAIL_HI) / A_HI
                 + (EC_TAIL_HI + 1) * EC_MEAN_HI)
    report("C/ThmSecondMoment: E[c_n^2] <= 2.9123",
           Ec2_bound <= Fr(29123, 10 ** 4), dec(Ec2_bound))
    check("C/ThmSecondMoment < 2.99", Ec2_bound < Fr(299, 100))
    # The printed constant, corrected (see evidence/PROVENANCE.md)
    exact_printed = (Fr(-17477399, 10 ** 7)) / A_HI + \
        (EC_TAIL_HI + 1) * EC_MEAN_HI
    report("C/ThmSecondMoment corrected printed constant",
           exact_printed == Fr(30942660571, 10625000000),
           "%s = %s (NOT 2.912248)" % (exact_printed, dec(exact_printed, 7)))

    # ---- Remark 5.5: limiting and finite tail-bound thresholds ------------
    check("C/Remark5.5 limiting threshold M'=1.98",
          2 + Fr(198, 100) / 2 == Fr(299, 100))

    def second_moment_scheme(Mp):
        """Finite n=651 majorant with an arbitrary valid tail bound Mp."""
        Up = Fr(0)
        for j in range(1, 41):
            d = Ec[j] - Mp
            x = (Fr(5 * j, 2 * n0) + Fr(j ** 3, 2 * n0 * n0)
                 + Fr(j * j, n0 * n0))
            if d >= 0:
                Up += exp_pos_ub(x) * v(j, A, up=True) * d
            else:
                Up += v(j, A, up=False) * d
        return (Up - Mp) / A_HI + (Mp + 1) * EC_MEAN_HI

    remark_lo = second_moment_scheme(Fr(16971, 10000))
    remark_hi = second_moment_scheme(Fr(16972, 10000))
    remark_two = second_moment_scheme(Fr(2))
    report("C/Remark5.5 finite threshold 1.6971/1.6972",
           remark_lo <= Fr(299, 100) < remark_hi,
           "%s <= 2.99 < %s" % (dec(remark_lo, 9), dec(remark_hi, 9)))
    report("C/Remark5.5 M'=2 bound <= 3.1626",
           Fr(299, 100) < remark_two <= Fr(31626, 10000),
           dec(remark_two, 9))

    # ---- Theorem D (E[D] >= 5n - 29/2) : POS and NEG -----------------------
    nD = 500
    J = 16
    ok = all(Fr(29, 2) - Fr(11 * nD, nD - j) > 0 for j in range(J + 1))
    check("C/ThmD betaL_j > 0 for j<=16", ok)
    check("C/ThmD kept block disjoint from negative range",
          nD - J > Fr(22 * nD, 29))
    POS = Fr(0)
    for j in range(J + 1):
        beta = Fr(29, 2) - Fr(11 * nD, nD - j)
        POS += (Fr(A[j], _fact(j)) * exp_neg_lb(Fr(j))
                * (1 - Fr(j, nD)) ** (j - 1) * beta)
    report("C/ThmD POS >= 5.69291", POS >= Fr(569291, 10 ** 5), dec(POS))

    CF = A_HI                # a_m <= 17/10 whenever m >= 81 (Theorem U)
    HEAD = Fr(0)
    for k in range(1, 31):
        coef = Fr((11 * k - 6) * (k ** (k - 4) if k >= 4 else
                                  Fr(1, k ** (4 - k))), _fact(k - 1))
        HEAD += coef * exp_neg_ub(Fr(k * (nD - 2 - k), nD))
    HEAD *= CF

    def pw52(q):
        """Upper bound for q^{5/2}, q > 0 rational."""
        return q * q * sqrt_hi(q)

    base = 11 * CF * INV_SQRT2PI_HI
    M1 = base * pw52(Fr(500, 440)) * tail_pow(30, 60, Fr(5, 2))
    M2 = base * pw52(Fr(500, 400)) * tail_pow(60, 100, Fr(5, 2))
    M3 = base * pw52(Fr(2)) * tail_pow(100, None, Fr(5, 2))
    # FAR: three blocks, per-term n^{5/2}/(k^{5/2}(n-k)^{5/2}) and a term count
    far_blocks = [(Fr(2) * Fr(5, 2), Fr(1, 10)),        # (n/2, 3n/5]
                  (Fr(5, 3) * Fr(10, 3), Fr(1, 10)),    # (3n/5, 7n/10]
                  (Fr(10, 7) * Fr(29, 7), Fr(17, 290))]  # (7n/10, 22n/29]
    FAR = Fr(0)
    for ratio, dens in far_blocks:
        FAR += base * pw52(ratio) * (dens + Fr(1, nD)) / (Fr(nD) * sqrt_lo(Fr(nD)))
    NEG = HEAD + M1 + M2 + M3 + FAR
    report("C/ThmD NEG <= 5.37050", NEG <= Fr(537050, 10 ** 5), dec(NEG))
    report("C/ThmD POS >= NEG", POS >= NEG, "margin %s" % dec(POS - NEG))

    # ---- Assembly : Delta(n) >= 0 for n >= 651 ----------------------------
    mu_lo = Fr(14819, 10 ** 4)
    Rub = Fr(22, 650)          # (4 mu^2 + 4 mu - 2)/(n-1) at mu <= 2, n >= 651
    check("C/assembly R bound arithmetic",
          4 * 2 ** 2 + 4 * 2 - 2 == 22)
    Delta = Fr(-29, 2) + 2 + 9 * mu_lo + mu_lo ** 2 - Fr(299, 100) - Rub
    report("C/assembly Delta(n) >= 0 for n >= 651", Delta > 0,
           "%s = %s" % (Delta, dec(Delta)))
    check("C/assembly matches quoted value",
          Delta == Fr(12065893, 1300000000), str(Delta))


# ---------------------------------------------------------------------------
# 7.  main
# ---------------------------------------------------------------------------

DEFAULT_NMAX = 700        # convenient proof-complete run with overlap values
MIN_PROOF_NMAX = 650      # exact n<=650 plus analytic n>=651 leaves no gap


def skipped_blocks(nmax):
    """Which proof-complete requirements a run at this NMAX does NOT establish."""
    missing = []
    if nmax < 650:
        missing.append(
            "ADJ/DIS on %d..650 (the analytic argument starts only at n=651)"
            % (nmax + 1))
    if nmax < 650:
        missing.append(
            "E[c_j] <= 1.5604 on %d..650, needed by Corollary cor:M "
            "(E[c_j] <= 1.5604 for every j >= 41)"
            % (nmax + 1))
    if nmax < 500:
        missing.append("a_n <= 17/10 on %d..500 (base of Theorem thm:U)"
                       % (nmax + 1))
        missing.append("a_n >= 1.647767 on %d..500 (base of Theorem thm:L)"
                       % (nmax + 1))
    if nmax < 650:
        missing.append("E[D_n] >= 5n - 29/2 on %d..650 (base of Theorem thm:D)"
                       % (nmax + 1))
    return missing


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--nmax", type=int, default=DEFAULT_NMAX,
                    help="upper end of the exact seam (default %d)"
                         % DEFAULT_NMAX)
    ap.add_argument("--ncross", type=int, default=400,
                    help="range for the second, independent pair-count "
                         "derivation (default 400)")
    ap.add_argument("--quick", action="store_true",
                    help="permit NMAX < %d; the run then verifies every "
                         "analytic constant but only part of the finite seam, "
                         "and says so." % MIN_PROOF_NMAX)
    args = ap.parse_args()
    nmax = args.nmax
    if nmax < 120:
        print("NMAX must be at least 120 to exercise anything; refusing.")
        return 2
    if nmax < MIN_PROOF_NMAX and not args.quick:
        print("NMAX = %d < %d would leave part of the finite seam unverified."
              % (nmax, MIN_PROOF_NMAX))
        print("Re-run with --quick if a partial seam is what you want.")
        return 2
    ncross = min(args.ncross, nmax)

    print("uniform-forests-kn -- standalone verifier")
    print("NMAX = %d   NCROSS = %d   python %s"
          % (nmax, ncross, sys.version.split()[0]))
    if nmax < MIN_PROOF_NMAX:
        print("MODE  = quick (NOT PROOF-COMPLETE)")
    else:
        print("MODE  = proof-complete")

    selftest_constants()

    A, Sc, Scc, SD = build_sequences(nmax)
    Ne = [0] * (nmax + 1)
    Nadj = [0] * (nmax + 1)
    Ndis = [0] * (nmax + 1)
    for n in range(2, nmax + 1):
        e, a, d = pair_counts(n, A, Sc, Scc, SD)
        Ne[n] = e or 0
        Nadj[n] = a or 0
        Ndis[n] = d or 0

    section_A(A, Sc, Scc, SD, Ne, Nadj, Ndis)
    an, Ec, Ec2 = section_B(nmax, A, Sc, Scc, SD, Ne, Nadj, Ndis, ncross)
    section_C(A, Ec)

    print("\nSUMMARY: %d PASS, %d FAIL" % (PASS, FAIL))
    if FAIL:
        for tag, detail in FAILURES:
            print("  FAILED: %s %s" % (tag, detail))
        return 1

    if nmax < MIN_PROOF_NMAX:
        print("")
        print("*" * 72)
        print("NOT PROOF-COMPLETE.  Every analytic constant of the note was")
        print("verified (section C is independent of NMAX), but the exact seam")
        print("stops at n = %d.  The following are NOT established by this run:"
              % nmax)
        for line in skipped_blocks(nmax):
            print("  - " + line)
        print("Re-run with --nmax %d (or more) for a proof-complete check."
              % MIN_PROOF_NMAX)
        print("*" * 72)
        return 0

    print("All checks passed.  The exact seam 3..%d overlaps the analytic "
          "range n >= 651, so no case is left open." % nmax)
    return 0


if __name__ == "__main__":
    sys.exit(main())
