"""
CS292C Homework 2 — Problem 3: Agent Permission Policy Verification (25 points)
=================================================================================
Encode a realistic agent permission policy as SMT formulas and use Z3 to
analyze it for safety properties and privilege escalation vulnerabilities.
"""

from z3 import *

# ============================================================================
# Constants
# ============================================================================

FILE_READ = 0
FILE_WRITE = 1
SHELL_EXEC = 2
NETWORK_FETCH = 3

ADMIN = 0
DEVELOPER = 1
VIEWER = 2

# ============================================================================
# Sorts and Functions
#
# You will use these to build your policy encoding.
# Do NOT modify these declarations.
# ============================================================================

User = DeclareSort('User')
Resource = DeclareSort('Resource')

role         = Function('role', User, IntSort())          # 0=admin, 1=dev, 2=viewer
is_sensitive = Function('is_sensitive', Resource, BoolSort())
in_sandbox   = Function('in_sandbox', Resource, BoolSort())
owner        = Function('owner', Resource, User)

# The core predicate: is this (user, tool, resource) triple allowed?
allowed = Function('allowed', User, IntSort(), Resource, BoolSort())


# ============================================================================
# Part (a): Encode the Policy — 10 pts
#
# Encode rules R1–R5 from the README as Z3 constraints.
#
# You must design the encoding yourself. Consider:
# - Use ForAll to make rules apply to all users/resources.
# - Encode both what IS allowed and what is NOT allowed.
# - Rule R4 overrides R3 — handle this carefully.
#
# Return a list of Z3 constraints.
# ============================================================================

def make_policy():
    """
    Return a list of Z3 constraints encoding rules R1–R5.
    """
    u = Const('u', User)
    r = Const('r', Resource)
    t = Int('t')

    constraints = []

    # allowed(u,t,r) iff some grant rule fires AND no deny rule fires
    grant = Or(
        role(u) == ADMIN,                                              # R3
        And(role(u) == VIEWER, t == FILE_READ, Not(is_sensitive(r))),  # R1
        And(role(u) == DEVELOPER, t == FILE_READ),                     # R2
        And(role(u) == DEVELOPER, t == FILE_WRITE,                     # R2
            Or(owner(r) == u, in_sandbox(r))),
    )

    deny_r4 = And(t == SHELL_EXEC, is_sensitive(r))       # R4: hard deny
    deny_r5 = And(t == NETWORK_FETCH, Not(in_sandbox(r))) # R5: sandbox only

    constraints.append(ForAll([u, t, r],
        allowed(u, t, r) == And(grant, Not(deny_r4), Not(deny_r5))
    ))

    return constraints


# ============================================================================
# Part (b): Policy Queries — 8 pts
# ============================================================================

def query(description, policy, extra):
    """Helper: check if extra constraints are SAT under the policy."""
    s = Solver()
    s.add(policy)
    s.add(extra)
    result = s.check()
    print(f"  {description}")
    print(f"  → {result}")
    if result == sat:
        m = s.model()
        print(f"    Model: {m}")
    print()
    return result


def part_b():
    """
    Answer the four queries from the README.
    For query 4, also demonstrate what becomes possible without R4.
    """
    policy = make_policy()
    print("=== Part (b): Policy Queries ===\n")

    u = Const('u', User)
    r = Const('r', Resource)

    # Q1: Can a developer write to a sensitive file they don't own, in the sandbox?
    query("Q1: Developer writes sensitive file they don't own (in sandbox)?",
          policy,
          [role(u) == DEVELOPER, is_sensitive(r) == True, in_sandbox(r) == True,
           owner(r) != u, allowed(u, FILE_WRITE, r) == True])
    # SAT - R2 lets devs write to sandbox resources, and R4 only restricts shell_exec.

    # Q2: Can an admin network_fetch a resource outside the sandbox?
    query("Q2: Admin network_fetch outside sandbox?",
          policy,
          [role(u) == ADMIN, in_sandbox(r) == False,
           allowed(u, NETWORK_FETCH, r) == True])
    # UNSAT - R5 blocks network_fetch outside sandbox even for admins.

    # Q3: Is there ANY role that can shell_exec on a sensitive resource?
    query("Q3: Any role can shell_exec on sensitive resource?",
          policy,
          [is_sensitive(r) == True, allowed(u, SHELL_EXEC, r) == True])
    # UNSAT - R4 blocks this for everyone, no exceptions.

    # Q4: Remove R4 - what dangerous action becomes possible?
    # [EXPLAIN] Without R4, admins can shell_exec on sensitive resources - the one
    # thing that was supposed to be blocked unconditionally.
    def make_policy_no_r4():
        u2 = Const('u2', User)
        r2 = Const('r2', Resource)
        t2 = Int('t2')
        grant = Or(
            role(u2) == ADMIN,
            And(role(u2) == VIEWER, t2 == FILE_READ, Not(is_sensitive(r2))),
            And(role(u2) == DEVELOPER, t2 == FILE_READ),
            And(role(u2) == DEVELOPER, t2 == FILE_WRITE,
                Or(owner(r2) == u2, in_sandbox(r2))),
        )
        deny_r5 = And(t2 == NETWORK_FETCH, Not(in_sandbox(r2)))
        return [ForAll([u2, t2, r2],
            allowed(u2, t2, r2) == And(grant, Not(deny_r5))
        )]

    policy_no_r4 = make_policy_no_r4()
    query("Q4: Without R4 - admin shell_exec on sensitive resource?",
          policy_no_r4,
          [role(u) == ADMIN, is_sensitive(r) == True,
           allowed(u, SHELL_EXEC, r) == True])


# ============================================================================
# Part (c): Privilege Escalation — 7 pts
#
# New rule R6: Developers may shell_exec on non-sensitive sandbox resources.
#
# Attack scenario: A developer uses shell_exec on a non-sensitive sandbox
# resource to change ANOTHER resource's sensitivity flag (e.g., modifying
# a config file that controls access). This makes a previously sensitive
# resource become non-sensitive, bypassing R4 on the next step.
#
# Model this as a 2-step trace where a resource's sensitivity changes
# between steps.
# ============================================================================

def part_c():
    """Model 2-step privilege escalation."""
    print("=== Part (c): Privilege Escalation ===\n")

    # Model: two time steps with separate sensitivity functions
    is_sensitive_before = Function('is_sensitive_before', Resource, BoolSort())
    is_sensitive_after = Function('is_sensitive_after', Resource, BoolSort())

    u = Const('u_esc', User)
    r1 = Const('r1', Resource)  # config resource (non-sensitive, in sandbox)
    r2 = Const('r2', Resource)  # target resource (sensitive before, non-sensitive after)

    s = Solver()

    # Developer role
    s.add(role(u) == DEVELOPER)
    # r1 and r2 are different resources
    s.add(r1 != r2)

    # Step 1 setup: r1 is non-sensitive and in sandbox
    s.add(is_sensitive_before(r1) == False)
    s.add(in_sandbox(r1) == True)

    # r2 is sensitive before the attack
    s.add(is_sensitive_before(r2) == True)
    s.add(in_sandbox(r2) == True)

    # R6: developers may shell_exec on non-sensitive sandbox resources
    # Step 1: developer calls shell_exec on r1 - allowed by R6
    step1_allowed = And(
        role(u) == DEVELOPER,
        Not(is_sensitive_before(r1)),
        in_sandbox(r1)
    )
    s.add(step1_allowed)

    # Side-effect of step 1: r2 becomes non-sensitive
    s.add(is_sensitive_after(r2) == False)
    s.add(in_sandbox(r2) == True)

    # Step 2: developer calls shell_exec on r2 using post-step1 sensitivity
    # Under R6 with the new sensitivity, this is allowed:
    step2_allowed = And(
        role(u) == DEVELOPER,
        Not(is_sensitive_after(r2)),
        in_sandbox(r2)
    )
    s.add(step2_allowed)

    # The attack: r2 was sensitive before but developer got shell_exec on it
    s.add(is_sensitive_before(r2) == True)

    result = s.check()
    print(f"Escalation possible? {result}")
    if result == sat:
        print(f"Model: {s.model()}")
        print("→ Developer bypassed R4 by flipping sensitivity via shell_exec on config!")
    print()

    # [EXPLAIN] Fix: shell_exec shouldn't be able to flip sensitivity labels. We lock
    # them down with ForAll r: is_sensitive_after(r) == is_sensitive_before(r). In a
    # real system you'd probably still let admins reclassify through a separate tool,
    # but the point is shell_exec specifically can't do it as a side-effect.

    s2 = Solver()
    s2.add(role(u) == DEVELOPER)
    s2.add(r1 != r2)
    s2.add(is_sensitive_before(r1) == False)
    s2.add(in_sandbox(r1) == True)
    s2.add(is_sensitive_before(r2) == True)
    s2.add(in_sandbox(r2) == True)
    s2.add(step1_allowed)

    # FIX: shell_exec cannot modify sensitivity labels (integrity constraint).
    # Since step 1 is shell_exec, sensitivity labels are preserved for all resources.
    r_fix = Const('r_fix', Resource)
    s2.add(ForAll([r_fix], is_sensitive_after(r_fix) == is_sensitive_before(r_fix)))

    # Now try step 2 with the fixed policy
    s2.add(is_sensitive_after(r2) == False)  # attacker wants this
    s2.add(in_sandbox(r2) == True)

    result2 = s2.check()
    if result2 == unsat:
        print("ESCALATION BLOCKED")
    else:
        print(f"Fix failed: {s2.model()}")
    print()


# ============================================================================
if __name__ == "__main__":
    part_b()
    part_c()
