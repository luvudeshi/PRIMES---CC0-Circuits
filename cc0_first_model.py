import time
from z3 import *

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

def prop_div(m):
    return [d for d in range(1, m) if m % d == 0]

def build_circ(f, m, max_s, max_depth):
    n = (len(f) - 1).bit_length()
    N = 1 << n
    assignments = [list(map(int, format(i, '0' + str(n) + 'b'))) for i in range(N)]
    w = adder_bitwidth(m)
    m_bv = BitVecVal(m, w)

    allowed_first_vals = prop_div(m)

    for s in range(4, max_s + 1):

        total = n + s
        max_d_cap = max_depth if max_depth is not None else total
        wd = max(2, (max_d_cap + 1).bit_length())
        zero_d = BitVecVal(0, wd)
        one_d  = BitVecVal(1, wd)
        max_dv = BitVecVal(max_d_cap, wd)

        solver = SolverFor("QF_BV")

        depth = [BitVec("d_" + str(i), wd) for i in range(total)]
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

            for k in range(i):
                c = BitVec("c_" + str(i) + "_" + str(k), w)
                connections[(i, k)] = c
                solver.add(bv_in_range(c))

                used = (c != BitVecVal(0, w))
                solver.add(Implies(used, UGE(depth[i], depth[k] + one_d)))

            solver.add(UGE(depth[i], one_d))

        zero_w = BitVecVal(0, w)

        def row_vec(i):
            base = [const_conn[i]] + [connections[(i, k)] for k in range(i)]
            need = total - len(base)
            if need > 0:
                base += [zero_w] * need
            return base

        def lex_le(xs, ys):
            eq_so_far = BoolVal(True)
            lt_acc = BoolVal(False)
            for a, b in zip(xs, ys):
                lt_here = And(eq_so_far, ULT(a, b))
                lt_acc = Or(lt_acc, lt_here)
                eq_so_far = And(eq_so_far, a == b)
            return Or(lt_acc, eq_so_far)

        rows = {i: row_vec(i) for i in range(n, total)}
        for i in range(n, total):
            for j in range(i + 1, total):
                same_layer = (depth[i] == depth[j])
                solver.add(Implies(same_layer, lex_le(rows[i], rows[j])))

        allowed_vals_bv = [BitVecVal(v, w) for v in allowed_first_vals]
        for i in range(n, total):
            head = [const_conn[i]] + [connections[(i, k)] for k in range(i)]
            L = len(head)
            for t in range(L):
                if t == 0:
                    pre_zero = BoolVal(True)
                else:
                    pre_zero = And(*[head[p] == zero_w for p in range(t)])
                is_first_nonzero = And(pre_zero, head[t] != zero_w)
                solver.add(Implies(is_first_nonzero, Or(*[head[t] == v for v in allowed_vals_bv])))

        g = [[Bool("g_" + str(i) + "_" + str(j)) for j in range(N)] for i in range(total)]

        for j, bits in enumerate(assignments):
            for i in range(n):
                solver.add(g[i][j] == (bits[i] == 1))

        for i in range(n, total):
            coeffs_row = [connections[(i, k)] for k in range(i)]
            for j in range(N):
                sels = [g[k][j] for k in range(i)]
                total_mod = mod_wsum(const_conn[i], coeffs_row, sels, m_bv, w)
                solver.add(g[i][j] == (total_mod == BitVecVal(0, w)))

        for j in range(N):
            solver.add(g[total - 1][j] == (f[j] == 1))

        if solver.check() == sat:
            return solver.model(), s

    return None, None


# execution for specific function:
# function's truth table goes here
f = [int(bin(i).count("1") % 4 == 0) for i in range(1 << 7)] #MOD4 function on 7 bits

m = 5
max_s = 5
max_d = 2

start_time = time.time()
model, s = build_circ(f, m, max_s, max_d)
end_time = time.time()
elapsed = end_time - start_time

if not model:
    print("no circuit for size<=" + str(max_s) + " and depth<=" + str(max_d))
    exit(1)

print("circuit with " + str(s) + " gates (depth<=" + str(max_d) + ")")
print("elapsed time: {:.3f} seconds".format(elapsed))

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
        driver_str = "-"
    d_val = model.eval(depth[i]).as_long()
    print("  Gate " + str(i) + " (depth " + str(d_val) + "): MOD_" + str(m) + "(" + driver_str + ")")

final_depth = model.eval(BitVec("d_" + str(total_gates - 1), max(2, (max_d + 1).bit_length()))).as_long()
print("\noutput at gate " + str(total_gates - 1) + " with depth " + str(final_depth))
