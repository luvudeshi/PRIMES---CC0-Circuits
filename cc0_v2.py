from z3 import *
import random

def target_dnf(n, f, xs):
    N = 1 << n
    ones = [j for j in range(N) if f[j] == 1]
    if not ones:
        return BoolVal(False)
    if len(ones) == 1:
        j = ones[0]
        bits = [int(b) for b in format(j, '0{}b'.format(n))]
        conj = And(*[(xs[i] if bits[i] == 1 else Not(xs[i])) for i in range(n)])
        return conj
    terms = []
    for j in ones:
        bits = [int(b) for b in format(j, '0{}b'.format(n))]
        conj = And(*[(xs[i] if bits[i] == 1 else Not(xs[i])) for i in range(n)])
        terms.append(conj)
    return Or(*terms)

def constraint_temp(n, s, m, xs, g_funcs, const_conn, connections, target_on_xs):
    clauses = []

    for i in range(n):
        clauses.append(g_funcs[i](*xs) == xs[i])

    for i in range(n, n + s):
        terms = [const_conn[i]]
        for k in range(i):
            terms.append(If(g_funcs[k](*xs), connections[(i, k)], IntVal(0)))
        total = Sum(*terms)
        clauses.append(g_funcs[i](*xs) == ((total % m) == 0)) #mod gate behavior

    clauses.append(g_funcs[n + s - 1](*xs) == target_on_xs)

    return And(*clauses)

def build_circ(f, m, max_s, max_depth):
    n = (len(f) - 1).bit_length()

    for s in range(1, max_s + 1):
        total_gates = n + s
        solver = Solver()

        depth = [Int("d_" + str(i)) for i in range(total_gates)]
        for i in range(n):
            solver.add(depth[i] == 0)
        if max_depth is not None:
            for i in range(total_gates):
                solver.add(depth[i] <= max_depth)

        connections, const_conn = {}, {}
        for i in range(n, total_gates):
            c1 = Int("c1_" + str(i))
            const_conn[i] = c1
            solver.add(And(c1 >= 0, c1 < m))
            for k in range(i):
                c = Int("c_" + str(i) + "_" + str(k))
                connections[(i, k)] = c
                solver.add(And(c >= 0, c < m))

        
        for i in range(n, total_gates):
            solver.add(depth[i] >= 1)
            for k in range(i):
                solver.add(Implies(connections[(i, k)] > 0, depth[i] >= depth[k] + 1)) # acyclicity 

        g_funcs = [Function("gfun_" + str(i), *([BoolSort()] * n), BoolSort()) for i in range(total_gates)]

        xs = [Bool("x_" + str(i)) for i in range(n)]

        target_on_xs = target_dnf(n, f, xs)
        constraint_xs = constraint_temp(n, s, m, xs, g_funcs, const_conn, connections, target_on_xs)

        solver.add(ForAll(xs, constraint_xs))

        if solver.check() == sat:
            return solver.model(), s

    return None, None


# execution for specific function:

# f = [1, 0, 0, 0, 0, 0, 0, 0]
f = [0] + [1]*7
m = 3
max_s = 5
max_d = 3

model, s = build_circ(f, m, max_s, max_d)
if not model:
    print("no circuit for size<=" + str(max_s) + " and depth<=" + str(max_d))
    exit(1)

print("circuit with " + str(s) + " gates (depth<=" + str(max_d) + ")")

n = (len(f) - 1).bit_length()
total_gates = n + s

connections = {}
const_conn = {}
for i in range(n, total_gates):
    const_conn[i] = Int("c1_" + str(i))
    for k in range(i):
        connections[(i, k)] = Int("c_" + str(i) + "_" + str(k))
depth = [ Int("d_" + str(i)) for i in range(total_gates) ]

print("\ninputs:")
for i in range(n):
    print("  gate " + str(i) + ": input x" + str(i))

print("\nMOD gates:")
for i in range(n, total_gates):
    parts = []
    mult1 = model.eval(const_conn[i]).as_long()
    if mult1 > 0:
        if mult1 > 1:
            parts.append(str(mult1) + "*1")
        else:
            parts.append("1")
    for k in range(i):
        mult = model.eval(connections[(i, k)]).as_long()
        if mult > 0:
            if mult > 1:
                parts.append(str(mult) + "*g" + str(k))
            else:
                parts.append("g" + str(k))
    if len(parts) > 0:
        driver_str = ", ".join(parts)
    else:
        driver_str = "—"
    d_val = model.eval(depth[i]).as_long()
    print("  Gate " + str(i) +
          " (depth " + str(d_val) + "): MOD_" + str(m) +
          "(" + driver_str + ")")

final_depth = model.eval(Int("d_" + str(total_gates - 1)))
print("\noutput at gate " + str(total_gates - 1) + " with depth " + str(final_depth))
