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

def lex_le(xs, ys):
    eq_so_far = BoolVal(True)
    lt_acc = BoolVal(False)
    for a, b in zip(xs, ys):
        lt_here = And(eq_so_far, ULT(a, b))
        lt_acc = Or(lt_acc, lt_here)
        eq_so_far = And(eq_so_far, a == b)
    return Or(lt_acc, eq_so_far)

def row_vec(i, total, const_conn, connections, zero_w):
    base = [const_conn[i]] + [connections[(i, k)] for k in range(i)]
    need = total - len(base)
    if need > 0:
        base += [zero_w] * need
    return base

def canonical_forms_by_depth(model, n, total, m, max_depth):
    w  = adder_bitwidth(m)
    wd = max(2, (((max_depth if max_depth is not None else total)) + 1).bit_length())

    const_conn = {}
    connections = {}
    for i in range(n, total):
        const_conn[i] = BitVec(f"c1_{i}", w)
        for k in range(i):
            connections[(i, k)] = BitVec(f"c_{i}_{k}", w)
    depth = [BitVec(f"d_{i}", wd) for i in range(total)]

    depth_vals = [model.eval(d).as_long() for d in depth]

    max_d_in_model = max(depth_vals) if total > 0 else 0
    gates_at_depth = {d: [] for d in range(max_d_in_model + 1)}
    for i in range(n, total):
        gates_at_depth[depth_vals[i]].append(i)

    gate_cf = {}

    def coef(i, k):
        return model.eval(connections[(i, k)]).as_long()

    def const(i):
        return model.eval(const_conn[i]).as_long()

    for d in range(1, max_d_in_model + 1):

        layer_items = []
        for i in gates_at_depth.get(d, []):
            c0 = const(i)

            input_coeffs = []
            for k in range(n):
                val = coef(i, k)
                if val != 0:
                    input_coeffs.append(val)
            input_coeffs.sort()

            ref_items = []
            for k in range(n, i):
                val = coef(i, k)
                if val == 0:
                    continue
                src = k
                ref_items.append((val, gate_cf[src]))

            ref_items.sort()

            cf = (d, c0, tuple(input_coeffs), tuple(ref_items))
            layer_items.append((i, cf))

        for i, cf in layer_items:
            gate_cf[i] = cf

    return depth_vals, gate_cf

def circuit_fingerprint_perm_invariant(model, n, total, m, max_depth):
    depth_vals, gate_cf = canonical_forms_by_depth(model, n, total, m, max_depth)
    all_cfs = [gate_cf[i] for i in range(n, total)]
    all_cfs.sort()
    return tuple(all_cfs)

def enumerate_minimal_circuits(f, m, max_s, max_depth=2, max_models=None):
    n = (len(f) - 1).bit_length()
    N = 1 << n
    assignments = [list(map(int, format(i, '0' + str(n) + 'b'))) for i in range(N)]

    w = adder_bitwidth(m)
    m_bv = BitVecVal(m, w)
    allowed_first_vals = prop_div(m)

    for s in range(1, max_s + 1):
        total = n + s
        max_d_cap = max_depth if max_depth is not None else total
        wd = max(2, (max_d_cap + 1).bit_length())
        zero_d = BitVecVal(0, wd)
        one_d  = BitVecVal(1, wd)
        max_dv = BitVecVal(max_d_cap, wd)

        solver = SolverFor("QF_BV")

        depth = [BitVec(f"d_{i}", wd) for i in range(total)]
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
            c1 = BitVec(f"c1_{i}", w)
            const_conn[i] = c1
            solver.add(bv_in_range(c1))

            for k in range(i):
                c = BitVec(f"c_{i}_{k}", w)
                connections[(i, k)] = c
                solver.add(bv_in_range(c))
                used = (c != BitVecVal(0, w))
                solver.add(Implies(used, UGE(depth[i], depth[k] + one_d)))

            solver.add(UGE(depth[i], one_d))

        zero_w = BitVecVal(0, w)

        rows = {i: row_vec(i, total, const_conn, connections, zero_w) for i in range(n, total)}
        for i in range(n, total):
            for j in range(i + 1, total):
                same_layer = (depth[i] == depth[j])
                solver.add(Implies(same_layer, lex_le(rows[i], rows[j])))

        allowed_vals_bv = [BitVecVal(v, w) for v in allowed_first_vals]
        for i in range(n, total):
            head = [const_conn[i]] + [connections[(i, k)] for k in range(i)]
            L = len(head)
            for t in range(L):
                pre_zero = BoolVal(True) if t == 0 else And(*[head[p] == zero_w for p in range(t)])
                is_first_nonzero = And(pre_zero, head[t] != zero_w)
                solver.add(Implies(is_first_nonzero, Or(*[head[t] == v for v in allowed_vals_bv])))

        g = [[Bool(f"g_{i}_{j}") for j in range(N)] for i in range(total)]

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

        unique_models = []
        seen_fps = set()

        block_vars = []
        for i in range(n, total):
            block_vars.append(const_conn[i])
            for k in range(i):
                block_vars.append(connections[(i, k)])
        block_vars += [depth[i] for i in range(total)]

        while solver.check() == sat:
            model = solver.model()
            fp = circuit_fingerprint_perm_invariant(model, n, total, m, max_depth)
            if fp not in seen_fps:
                seen_fps.add(fp)
                unique_models.append(model)

            diseqs = []
            for v in block_vars:
                try:
                    val = model.eval(v, model_completion=True)
                except Z3Exception:
                    continue
                diseqs.append(v != val)
            if not diseqs:
                break
            solver.add(Or(*diseqs))

            if max_models is not None and len(unique_models) >= max_models:
                break

        if unique_models:
            return unique_models, s

    return [], None

def print_circuit_from_model(model, f, m, s, max_depth):
    n = (len(f) - 1).bit_length()
    total_gates = n + s
    w = adder_bitwidth(m)
    wd = max(2, (((max_depth if max_depth is not None else total_gates)) + 1).bit_length())

    const_conn = {}
    connections = {}
    for i in range(n, total_gates):
        const_conn[i] = BitVec(f"c1_{i}", w)
        for k in range(i):
            connections[(i, k)] = BitVec(f"c_{i}_{k}", w)
    depth = [BitVec(f"d_{i}", wd) for i in range(total_gates)]

    print("\ninputs:")
    for i in range(n):
        print(f"  gate {i}: input x{i}")

    print("\nMOD gates:")
    for i in range(n, total_gates):
        parts = []
        mult1 = model.eval(const_conn[i]).as_long()
        if mult1 > 0:
            parts.append("1" if mult1 == 1 else f"{mult1}*1")
        for k in range(i):
            mult = model.eval(connections[(i, k)]).as_long()
            if mult > 0:
                parts.append(f"g{k}" if mult == 1 else f"{mult}*g{k}")
        driver_str = ", ".join(parts) if parts else "-"
        d_val = model.eval(depth[i]).as_long()
        print(f"  Gate {i} (depth {d_val}): MOD_{m}({driver_str})")

    final_depth = model.eval(depth[total_gates - 1]).as_long()
    print(f"\noutput at gate {total_gates - 1} with depth {final_depth}")

#execution for specific function
# function's truth table goes here
f = [int(bin(i).count("1") % 4 == 0) for i in range(1 << 8)]  # MOD4 function on 8 bits

m = 5
max_s = 5
max_d = 2

start_time = time.time()
models, s = enumerate_minimal_circuits(f, m, max_s, max_depth=max_d, max_models=None)
end_time = time.time()
elapsed = end_time - start_time

if not models:
    print("no circuit for size<=" + str(max_s) + " and depth<=" + str(max_d))
    exit(1)

print("Found " + str(len(models)) + " unique circuit(s) of minimal size " + str(s) +
      " (depth<=" + str(max_d) + ")")
print("elapsed time: {:.3f} seconds".format(elapsed))

for idx, model in enumerate(models, 1):
    print("\n=== Circuit #" + str(idx) + " ===")
    print_circuit_from_model(model, f, m, s, max_d)
