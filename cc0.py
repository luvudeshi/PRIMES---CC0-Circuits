from z3 import *

def build_circ(f, m, max_s, max_depth):
    n = (len(f) - 1).bit_length()
    assignments = [list(map(int, format(i, '0' + str(n) + 'b'))) for i in range(1 << n)]  # lex ordering of binary strings

    for s in range(1, max_s + 1):
        solver = Solver()
        total_gates = n + s

        g = [[Bool("g_" + str(i) + "_" + str(j)) for j in range(1 << n)] for i in range(total_gates)]  # pre-construct matrix

        depth = [Int("d_" + str(i)) for i in range(total_gates)]  # gate depths
        for i in range(n):  
            solver.add(depth[i] == 0)
        if max_depth is not None:
            for i in range(total_gates):
                solver.add(depth[i] <= max_depth)

        for i in range(n):
            for j, bits in enumerate(assignments):
                solver.add(g[i][j] == (bits[i] == 1))  # first n gates

        connections = {}
        for i in range(n, total_gates):
            for k in range(i):
                connections[(i, k)] = Bool("c_" + str(i) + "_" + str(k))  # rest of gates

        for i in range(n, total_gates):
            solver.add(depth[i] >= 1)
            for k in range(i):
                solver.add(Implies(connections[(i, k)], depth[i] >= depth[k] + 1))  # acyclicity

        for i in range(n, total_gates):
            for j in range(1 << n):
                terms = [If(And(connections[(i, k)], g[k][j]), 1, 0) for k in range(i)]
                solver.add(g[i][j] == (Sum(*terms) % m == 0))  # mod gate behavior

        for j, out_val in enumerate(f):
            solver.add(g[total_gates - 1][j] == (out_val == 1))
        if max_depth is not None:
            solver.add(depth[total_gates - 1] <= max_depth)

        if solver.check() == sat:
            return solver.model(), s

    return None, None


# execution for specific function:

# f = [1, 0, 0, 0, 0, 0, 0, 0]
f = [0, 1, 1, 1, 1, 1, 1, 1]
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

print("\ninputs:")
for i in range(n):
    print("  gate " + str(i) + ": input x" + str(i))

connections = {}
for i in range(n, total_gates):
    for k in range(i):
        connections[(i, k)] = Bool("c_" + str(i) + "_" + str(k))

print("\nMOD gates:")
for i in range(n, total_gates):
    drivers = [
        k for k in range(i)
        if bool(model.eval(connections[(i, k)]))
    ]
    driver_str = ", ".join("g" + str(k) for k in drivers) or "—"
    d_val = model.eval(Int("d_" + str(i)))
    print("  Gate " + str(i) +
        " (depth " + str(d_val) + "): MOD_" + str(m) +
        "(" + driver_str + ")")

final_depth = model.eval(Int("d_" + str(total_gates - 1)))
print("\noutput at gate " + str(total_gates - 1) + " with depth " + str(final_depth))
