from z3 import *
import random

def adder_bitwidth(m):
    return max(2, (2 * m - 1).bit_length())

def mod_add(a, b, m_bv, w):
    s = a + b
    return If(UGE(s, m_bv), s - m_bv, s)

def mod_wsum(const_bv, coeffs, sel_bools, m_bv, w):
    zero = BitVecVal(0, w)
    acc = const_bv
    for c, sel in zip(coeffs, sel_bools):
        term = If(sel, c, zero)
        acc = mod_add(acc, term, m_bv, w)
    return acc


def build_circ(f, m, max_s, max_depth):
    n = (len(f) - 1).bit_length()
    N = 1 << n

    assignments = [list(map(int, format(i, '0' + str(n) + 'b'))) for i in range(1 << n)] #lex ordering of binary strings

    w = adder_bitwidth(m)
    m_bv = BitVecVal(m, w)

    for s in range(1, max_s + 1):
        total = n + s

        max_d_cap = max_depth if max_depth is not None else total
        wd = max(2, (max_d_cap + 1).bit_length())
        zero_d = BitVecVal(0, wd)
        one_d  = BitVecVal(1, wd)
        max_dv = BitVecVal(max_d_cap, wd)

        solver = SolverFor("QF_BV")

        depth = [ BitVec("d_" + str(i), wd) for i in range(total) ]
        for i in range(n):
            solver.add(depth[i] == zero_d)
        if max_depth is not None:
            for i in range(total):
                solver.add(ULE(depth[i], max_dv))

        const_conn = {}
        connections = {}

        def bv_in_range(x):
            return ULT(x, m_bv)  

        for i in range(n, total):
            c1 = BitVec("c1_" + str(i), w)
            const_conn[i] = c1
            solver.add(bv_in_range(c1))

            for k in range(0, i):
                c = BitVec("c_" + str(i) + "_" + str(k), w)
                connections[(i, k)] = c
                solver.add(bv_in_range(c))

                used = (c != BitVecVal(0, w))
                solver.add(Implies(used, UGE(depth[i], depth[k] + one_d)))

            solver.add(UGE(depth[i], one_d))

        g = [[ Bool("g_" + str(i) + "_" + str(j)) for j in range(N) ] for i in range(total)]

        for j, bits in enumerate(assignments):
            for i in range(n):
                solver.add(g[i][j] == (bits[i] == 1))

        for i in range(n, total):
            coeffs_row = [connections[(i, k)] for k in range(0, i)]
            for j in range(N):
                sels = [ g[k][j] for k in range(0, i) ]
                total_mod = mod_wsum(const_conn[i], coeffs_row, sels, m_bv, w)
                solver.add(g[i][j] == (total_mod == BitVecVal(0, w)))

        for j in range(N):
            solver.add(g[total - 1][j] == (f[j] == 1))

        if solver.check() == sat:
            return solver.model(), s

    return None, None


# execution for specific function:

# f = [1, 0, 0, 0, 0, 0, 0, 0]
f = [0] + [1]*127
m = 5
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
    const_conn[i] = BitVec("c1_" + str(i), adder_bitwidth(m))
    for k in range(i):
        connections[(i, k)] = BitVec("c_" + str(i) + "_" + str(k), adder_bitwidth(m))

depth = [BitVec("d_" + str(i), max(2, (max_d + 1).bit_length())) for i in range(total_gates)]

print("\ninputs:")
for i in range(n):
    print("  gate " + str(i) + ": input x" + str(i))

print("\nMOD gates:")
for i in range(n, total_gates):
    parts = []
    mult1 = model.eval(const_conn[i]).as_long()
    if mult1 > 0:
        if mult1 == 1:
            parts.append("1")
        else:
            parts.append(str(mult1) + "*1")
    for k in range(i):
        mult = model.eval(connections[(i, k)]).as_long()
        if mult > 0:
            if mult == 1:
                parts.append("g" + str(k))
            else:
                parts.append(str(mult) + "*g" + str(k))
    if parts:
        driver_str = ", ".join(parts)
    else:
        driver_str = "—"
    d_val = model.eval(depth[i]).as_long()
    print("  Gate " + str(i) + " (depth " + str(d_val) + "): MOD_" + str(m) + "(" + driver_str + ")")

final_depth = model.eval(BitVec("d_" + str(total_gates - 1), max(2, (max_d + 1).bit_length()))).as_long()
print("\noutput at gate " + str(total_gates - 1) + " with depth " + str(final_depth))
