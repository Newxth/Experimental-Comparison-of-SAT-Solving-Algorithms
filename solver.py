import random
import string
import time
a=input("Do you want to generate DIMACS Yes/No: ")
if a == "Yes" or a == "yes":

    nr_literals = int(input("Number of literals: "))
    nr_clauses = int(input("Number of clauses: "))
    minim_size=int(input("Minimum size of clauses: "))
    maxim_size=int(input("Max size of clauses: "))

    literals = set()
    clauses = []
    literal_string = ""

    # Generate a set of unique literals
    while nr_literals != len(literals):
        literals.add(random.randint(1, nr_literals))

    # Generate clauses
    for clause_index in range(nr_clauses):
        clause_literals = set()

        clause_size = random.randint(minim_size,maxim_size)
        while len(clause_literals) < clause_size:
            base_literal = random.choice(list(literals))
            negated = random.choice([True, False])

            # Form the literal (negated or not)
            literal = -base_literal if negated else base_literal

            # Check that its opposite is not already in the clause
            if -base_literal in clause_literals or base_literal in clause_literals:
                continue

            clause_literals.add(literal)

        if clause_literals not in clauses:
            clauses.append(clause_literals)

    # Output in DIMACS format

    print(f"p cnf {nr_literals} {nr_clauses}")
    for clause in clauses:
        print(" ".join(map(str, clause)) + " 0")

elif a=="no" or a=="No":
    file_path = "clauses.txt"
    with open(file_path, "r", encoding="utf-8") as f:
        clauses = []
        for line in f:
            # Skip comment and problem lines
            if line.startswith("c") or line.startswith("p") or not line.strip():
                continue
            clause = set(map(int, line.strip().split()))
            clause.discard(0)  # Remove the trailing 0
            clauses.append(clause)
# Resolution
print("Choose your solving method")
print("1:Resolution")
print("2:DP")
print("3:DPLL")
solving=input("Choose a number 1-3: ")

if solving == "1":

    #Resolution
    def resolve(c1, c2):
        resolvents = []
        for lit1 in c1:
            for lit2 in c2:
                if lit1 == -lit2:  # Complementary literals found
                    resolvent = (c1 | c2) - {lit1, lit2}

                    # Skip tautologies (clauses containing both x and -x)
                    is_tautology = any(-lit in resolvent for lit in resolvent)
                    if is_tautology:
                        continue

                    if not resolvent:  # Empty clause means contradiction
                        return [set()]  # Return the empty clause
                    resolvents.append(resolvent)
        return resolvents


    def resolution(clauses):

        new_clauses = [frozenset(c) for c in clauses]
        seen = set(new_clauses)

        while True:
            n = len(new_clauses)
            pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]

            for i, j in pairs:
                resolvents = resolve(new_clauses[i], new_clauses[j])
                for r in resolvents:
                    r_frozen = frozenset(r)
                    if r_frozen not in seen:
                        seen.add(r_frozen)
                        new_clauses.append(r_frozen)
                        if not r:  # Empty clause found
                            return new_clauses, False  # UNSAT

            if len(new_clauses) == n:  # Fixed point reached
                return new_clauses, True  # SAT


    start_time = time.perf_counter()
    final_clauses, is_sat = resolution(clauses)
    print("\nResolution Result:")
    print("UNSAT (contradiction found)" if not is_sat else "SAT (no contradiction)")
    print(f"Total clauses after resolution: {len(final_clauses)}")
    end_time = time.perf_counter()
    print(f"Compilation time: {end_time - start_time:.6f} seconds")

if solving == "2":
    start_time = time.perf_counter()

    def dp_1960(clauses):

        while True:
            # Rule I: One-Literal Rule (Unit Propagation)
            unit_clauses = [c for c in clauses if len(c) == 1]
            if unit_clauses:
                lit = next(iter(unit_clauses[0]))
                # Remove clauses containing lit
                clauses = [c for c in clauses if lit not in c]
                # Remove ¬lit from remaining clauses
                clauses = [c - {-lit} for c in clauses]
                # If empty clause found → UNSAT
                if any(len(c) == 0 for c in clauses):
                    return None
                continue

            # Rule II: Pure Literal Rule
            all_lits = {lit for c in clauses for lit in c}
            pure_lits = [lit for lit in all_lits if -lit not in all_lits]
            if pure_lits:
                # Remove clauses containing pure literals
                clauses = [c for c in clauses if not any(lit in c for lit in pure_lits)]
                continue


            if not clauses:
                return {}

            # Rule III: Resolution (variable elimination)
            remaining_lits = {lit for c in clauses for lit in c}
            if not remaining_lits:
                return {}
            var = next(iter(remaining_lits))  # Pick any remaining variable

            # Resolve all clauses containing var and ¬var
            pos_clauses = [c for c in clauses if var in c]
            neg_clauses = [c for c in clauses if -var in c]

            # If no resolutions possible (no var or no ¬var), pick another variable
            if not pos_clauses or not neg_clauses:
                # Just remove the variable
                clauses = [c for c in clauses if var not in c and -var not in c]
                continue

            new_clauses = []
            for p in pos_clauses:
                for n in neg_clauses:
                    resolvent = (p - {var}) | (n - {-var})
                    # Skip tautologies (clauses containing both x and -x)
                    if any(-lit in resolvent for lit in resolvent):
                        continue
                    if not resolvent:  # Empty resolvent → UNSAT
                        return None
                    new_clauses.append(resolvent)

            # Remove old clauses and add new ones
            clauses = [c for c in clauses if var not in c and -var not in c] + new_clauses


    result = dp_1960([set(clause) for clause in clauses])

    print("\nDP (1960) Result:")
    if result is not None:
        print("SAT (satisfiable)")
    else:
        print("UNSAT (unsatisfiable)")
    end_time = time.perf_counter()
    print(f"Execution time: {end_time - start_time:.6f} seconds")

if solving=="3":

    def dpll(clauses, assignment=None):
        if assignment is None:
            assignment = {}

        #Rule I: Unit Propagation
        changed = True
        while changed:
            changed = False
            unit_clauses = [c for c in clauses if len(c) == 1]
            for unit_clause in unit_clauses:
                lit = next(iter(unit_clause))
                var = abs(lit)

                # Skip if already assigned inconsistently
                if var in assignment:
                    if assignment[var] != (lit > 0):
                        return None  # UNSAT
                    continue

                assignment[var] = (lit > 0)

                # Remove satisfied clauses and simplify
                new_clauses = []
                for c in clauses:
                    if lit in c:
                        continue
                    new_c = c - {-lit}
                    if not new_c:  # Empty clause
                        return None
                    new_clauses.append(new_c)
                clauses = new_clauses
                changed = True

        # Rule II: Pure Literal Elimination
        all_lits = {lit for c in clauses for lit in c}
        pure_lits = [lit for lit in all_lits if -lit not in all_lits]
        for lit in pure_lits:
            var = abs(lit)
            assignment[var] = (lit > 0)
            clauses = [c for c in clauses if lit not in c]


        if not clauses:
            return assignment  # SAT
        if any(not c for c in clauses):
            return None  # UNSAT

        # Rule III: Splitting
        lit = next(iter(clauses[0]))  # Select first literal from first clause
        var = abs(lit)

        # Try L = True
        new_clauses_true = [c - {var} for c in clauses if -var not in c]
        result = dpll(new_clauses_true, {**assignment, var: True})
        if result is not None:
            return result

        # Try L = False
        new_clauses_false = [c - {-var} for c in clauses if var not in c]
        return dpll(new_clauses_false, {**assignment, var: False})


    start_time = time.perf_counter()
    result = dpll(clauses)
    print("\nDPLL (1962) Result:")
    if result is not None:
        print("SAT (no contradiction)")
    else:
        print("UNSAT (contradiction)")
    end_time = time.perf_counter()
    print(f"Compilation time: {end_time - start_time:.6f} seconds")