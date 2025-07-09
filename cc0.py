from z3 import *

def build_circ_int_connections(f, m, max_s, max_depth=None, max_mul=1):
    """
    Synthesize a CC₀ (MOD_m) circuit for the Boolean function f,
    allowing integer‐multiplicity wires (0..max_mul) and a constant‐1 input.
    Returns (model, size) or (None, None) if no circuit ≤ max_s is found.
    """
    # Determine n so that 2^n = len(f)
    n = (len(f) - 1).bit_length()
    # Precompute all 2^n input assignments (lists of 0/1)
    assignments = [list(map(int, format(i, f'0{n}b'))) for i in range(1 << n)]

    # Try candidate circuits with s = 1..max_s MOD gates
    for s in range(1, max_s + 1):
        solver = Solver()
        total_gates = n + s

        # Boolean outputs for each gate i on each assignment j
        g = [
            [ Bool(f"g_{i}_{j}") for j in range(1 << n) ]
            for i in range(total_gates)
        ]

        # Depth variables (optional)
        depth = [ Int(f"d_{i}") for i in range(total_gates) ]
        # inputs are at depth 0
        for i in range(n):
            solver.add(depth[i] == 0)
        # depth bounds
        if max_depth is not None:
            for i in range(total_gates):
                solver.add(depth[i] <= max_depth)

        # fix input‐gate outputs to the assignment bits
        for i in range(n):
            for j, bits in enumerate(assignments):
                solver.add(g[i][j] == (bits[i] == 1))

        # integer‐multiplicity connection variables, including constant‐1
        connections = {}
        for i in range(n, total_gates):
            # wires from each previous gate
            for k in range(i):
                c = Int(f"c_{i}_{k}")
                connections[(i, k)] = c
                solver.add(c >= 0, c <= max_mul)
            # a constant‐1 source
            c0 = Int(f"c_{i}_const")
            connections[(i, 'const')] = c0
            solver.add(c0 >= 0, c0 <= max_mul)

        # acyclicity via depth (unchanged)
        for i in range(n, total_gates):
            solver.add(depth[i] >= 1)
            for k in range(i):
                # if you use any positive multiplicity from k->i, enforce depth
                solver.add(Implies(connections[(i, k)] > 0,
                                   depth[i] >= depth[k] + 1))

        # MOD_m behavior with integer‐weighted wires + constant‐1
        for i in range(n, total_gates):
            for j in range(1 << n):
                terms = []
                # each driver k contributes c_{i,k} * g[k][j]
                for k in range(i):
                    terms.append(
                        If(g[k][j], connections[(i, k)], 0)
                    )
                # constant‐1 wires contribute their multiplicity directly
                terms.append(connections[(i, 'const')])
                total = Sum(*terms)
                # gate i on input j is 1 iff total ≡ 0 (mod m)
                solver.add(g[i][j] == (total % m == 0))

        # enforce final output matches f
        for j, out_val in enumerate(f):
            solver.add(g[total_gates - 1][j] == (out_val == 1))

        # final depth bound on output gate
        if max_depth is not None:
            solver.add(depth[total_gates - 1] <= max_depth)

        # solve
        if solver.check() == sat:
            return solver.model(), s

    # no circuit found
    return None, None


if __name__ == "__main__":
    # Example usage:
    f = [0,1,1,1,1,1,1,1]   # 3-bit majority‐complement function
    m = 3
    max_s = 5
    max_d = 3
    # allow at most 1 parallel wire per connection
    model, s = build_circ_int_connections(f, m, max_s, max_d, max_mul=1)
    if model is None:
        print(f"No circuit of size ≤ {max_s} and depth ≤ {max_d}")
        exit(1)

    print(f"Found circuit with {s} MOD_{m} gates (depth ≤ {max_d})\n")

    # pretty‐print
    n = (len(f)-1).bit_length()
    total_gates = n + s

    print("Inputs:")
    for i in range(n):
        print(f"  Gate {i}: input x{i}")

    print("\nMOD gates:")
    for i in range(n, total_gates):
        # collect drivers with positive multiplicity
        drivers = []
        for k in range(i):
            if model.evaluate(connections[(i,k)]).as_long() > 0:
                drivers.append(f"{model.evaluate(connections[(i,k)]).as_long()}×g{k}")
        # constant‐1 wires
        c0 = model.evaluate(connections[(i,'const')]).as_long()
        if c0 > 0:
            drivers.append(f"{c0}×1")
        driver_str = " + ".join(drivers) or "—"
        d_val = model.evaluate(depth[i])
        print(f"  Gate {i} (depth {d_val}): MOD_{m}({driver_str})")

    final_depth = model.evaluate(depth[total_gates-1])
    print(f"\nOutput at gate {total_gates-1} with depth {final_depth}")
