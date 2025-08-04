from z3 import *
import random

def add_assignment_constraints(solver, f, m, n, s, assignments, const_conn, connections, j):
    total_gates = n + s

    for i in range(n):
        solver.add(Bool("g_" + str(i) + "_" + str(j)) == (assignments[j][i] == 1))

    for i in range(n, total_gates):
        terms = [const_conn[i]]
        for k in range(i):
            terms.append(connections[(i, k)] * If(Bool("g_" + str(k) + "_" + str(j)), 1, 0))
        total = Sum(*terms)
        solver.add(Bool("g_" + str(i) + "_" + str(j)) == ((total % m) == 0))

    
    solver.add(Bool("g_" + str(total_gates-1) + "_" + str(j)) == (f[j] == 1))


def build_circ(f, m, max_s, max_depth, initial_samples=8, max_iters=50):

    n = (len(f) - 1).bit_length()
    assignments = [list(map(int, format(i, '0' + str(n) + 'b'))) for i in range(1 << n)] #lex ordering of binary strings
    N = 1 << n
    
    for s in range(1, max_s + 1):
        solver = Solver()
        total_gates = n + s

        depth = [Int("d_" + str(i)) for i in range(total_gates)] #gate depths
        for i in range(n):
            solver.add(depth[i] == 0)
        if max_depth is not None:
            for i in range(total_gates):
                solver.add(depth[i] <= max_depth)

        connections = {}
        const_conn = {}
        for i in range(n, total_gates):
            c1 = Int("c1_" + str(i))
            const_conn[i] = c1
            solver.add(c1 >= 0, c1 < m) #constatnt 1 wires
            for k in range(i):
                c = Int("c_" + str(i) + "_" + str(k))
                connections[(i, k)] = c 
                solver.add(c >= 0, c < m)

        for i in range(n, total_gates):
            solver.add(depth[i] >= 1)
            for k in range(i):
                solver.add(Implies(connections[(i, k)] > 0, depth[i] >= depth[k] + 1)) #acyclicity

        sample = random.sample(range(N), k=min(initial_samples, N)) #choose sample
        for j in sample:
            add_assignment_constraints(solver, f, m, n, s, assignments, const_conn, connections, j)

        for _ in range(max_iters):
            if solver.check() != sat:
                break

            model = solver.model()

            mismatch = None
            for j, bits in enumerate(assignments):
                gate_vals = [bool(bits[i]) for i in range(n)]
                for i in range(n, total_gates):
                    tot = model[const_conn[i]].as_long()
                    for k in range(i):
                        if gate_vals[k]:
                            tot += model[connections[(i, k)]].as_long()
                    gate_vals.append((tot % m) == 0)
                if gate_vals[-1] != bool(f[j]):
                    mismatch = j
                    break

            if mismatch is None:
                return model, s  

            add_assignment_constraints(solver, f, m, n, s,assignments, const_conn, connections, mismatch) #add new constraint


    return None, None


# execution for specific function:

# f = [1, 0, 0, 0, 0, 0, 0, 0]
f = [0] + [1]*31
m = 15
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
