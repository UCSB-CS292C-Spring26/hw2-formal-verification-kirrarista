"""
CS292C Homework 2 — Problem 1: Z3 Warm-Up + EUF Puzzle (15 points)
===================================================================
Complete each function below. Run this file to check your answers.
"""

from z3 import *


# ---------------------------------------------------------------------------
# Part (a) — 3 pts
# Find integers x, y, z such that x + 2y = z, z > 10, x > 0, y > 0.
# ---------------------------------------------------------------------------
def part_a():
    x, y, z = Ints('x y z')
    s = Solver()

    s.add(x + 2 * y == z)
    s.add(z > 10)
    s.add(x > 0)
    s.add(y > 0)

    print("=== Part (a) ===")
    if s.check() == sat:
        m = s.model()
        print(f"SAT: x={m[x]}, y={m[y]}, z={m[z]}")
    else:
        print("UNSAT (unexpected!)")
    print()


# ---------------------------------------------------------------------------
# Part (b) — 3 pts
# Prove validity of: ∀x. x > 5 → x > 3
# Hint: A formula F is valid iff ¬F is unsatisfiable.
# ---------------------------------------------------------------------------
def part_b():
    x = Int('x')
    s = Solver()

    # Negate: ∃x. x > 5 ∧ ¬(x > 3)
    s.add(x > 5)
    s.add(Not(x > 3))

    print("=== Part (b) ===")
    result = s.check()
    if result == unsat:
        print("Valid! (negation is UNSAT)")
    else:
        print(f"Not valid — counterexample: {s.model()}")
    print()


# ---------------------------------------------------------------------------
# Part (c) — 5 pts: The EUF Puzzle
#
# Formula:  f(f(x)) = x  ∧  f(f(f(x))) = x  ∧  f(x) ≠ x
#
# STEP 1: Check satisfiability with Z3. (2 pts)
#
# STEP 2: Use Z3 to derive WHY the result holds. (3 pts)
#   Write a series of Z3 validity checks that demonstrate the key reasoning
#   steps. For example, from f(f(x)) = x, what can you derive about f(f(f(x)))?
#   Each check should print what it's testing and whether it holds.
#   Hint: Apply f to both sides of the first equation.
# ---------------------------------------------------------------------------
def part_c():
    S = DeclareSort('S')
    x = Const('x', S)
    f = Function('f', S, S)
    s = Solver()

    s.add(f(f(x)) == x)
    s.add(f(f(f(x))) == x)
    s.add(f(x) != x)

    print("=== Part (c) ===")
    result = s.check()
    if result == sat:
        print(f"SAT: {s.model()}")
    else:
        print("UNSAT")

    # Derivation: why is this UNSAT?
    # From f(f(x)) = x, apply f to both sides: f(f(f(x))) = f(x).
    # But we also have f(f(f(x))) = x.
    # So f(x) = x. This contradicts f(x) ≠ x.

    # Step 1: From f(f(x)) = x, prove f(f(f(x))) = f(x)
    s1 = Solver()
    s1.add(f(f(x)) == x)
    s1.add(Not(f(f(f(x))) == f(x)))
    r1 = s1.check()
    print(f"Step 1: f(f(x)) = x → f(f(f(x))) = f(x)? {'Valid' if r1 == unsat else 'INVALID'}")

    # Step 2: From f(f(f(x))) = x and f(f(f(x))) = f(x), prove f(x) = x
    s2 = Solver()
    s2.add(f(f(f(x))) == x)
    s2.add(f(f(f(x))) == f(x))
    s2.add(Not(f(x) == x))
    r2 = s2.check()
    print(f"Step 2: f(f(f(x))) = x ∧ f(f(f(x))) = f(x) → f(x) = x? {'Valid' if r2 == unsat else 'INVALID'}")

    # Step 3: f(x) = x contradicts f(x) ≠ x, so the original is UNSAT
    s3 = Solver()
    s3.add(f(x) == x)
    s3.add(f(x) != x)
    r3 = s3.check()
    print(f"Step 3: f(x) = x ∧ f(x) ≠ x is contradictory? {'Yes' if r3 == unsat else 'No'}")

    print()


# ---------------------------------------------------------------------------
# Part (d) — 4 pts: Array Axioms
#
# Prove BOTH axioms (two separate solver checks):
#   (1) Read-over-write HIT:   i = j  →  Select(Store(a, i, v), j) = v
#   (2) Read-over-write MISS:  i ≠ j  →  Select(Store(a, i, v), j) = Select(a, j)
#
# [EXPLAIN] in a comment below: Why are these two axioms together sufficient
# to fully characterize Store/Select behavior? (2–3 sentences)
# ---------------------------------------------------------------------------
def part_d():
    a = Array('a', IntSort(), IntSort())
    i, j, v = Ints('i j v')

    print("=== Part (d) ===")

    # Axiom 1: Read-over-write HIT
    s1 = Solver()
    # Negate: i = j ∧ Select(Store(a, i, v), j) ≠ v
    s1.add(i == j)
    s1.add(Select(Store(a, i, v), j) != v)
    r1 = s1.check()
    print(f"Axiom 1 (hit):  {'Valid' if r1 == unsat else 'INVALID'}")

    # Axiom 2: Read-over-write MISS
    s2 = Solver()
    # Negate: i ≠ j ∧ Select(Store(a, i, v), j) ≠ Select(a, j)
    s2.add(i != j)
    s2.add(Select(Store(a, i, v), j) != Select(a, j))
    r2 = s2.check()
    print(f"Axiom 2 (miss): {'Valid' if r2 == unsat else 'INVALID'}")

    # [EXPLAIN] For any read after a write, the index either matches the written index
    # or it doesn't - there's no third case. Axiom 1 handles the match (you get back
    # what you stored), axiom 2 handles the mismatch (array is unchanged at other indices).
    # So any Select(Store(...)) expression is fully determined by these two rules.
    print()


# ---------------------------------------------------------------------------
if __name__ == "__main__":
    part_a()
    part_b()
    part_c()
    part_d()
