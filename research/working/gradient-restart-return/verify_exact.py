"""Exact arithmetic checks for the finite examples in main.tex.

The general asymptotic claims are proved in the manuscript. This program
verifies the identities, event timings, and two-node upper-bound certificates
reported as finite examples. It uses only the Python standard library.
"""

import argparse
import json
from fractions import Fraction
from math import factorial
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


def residuals(node, trial_limit):
    residual = [Fraction(1), node]
    for k in range(1, trial_limit):
        next_value = node * (
            (2 * k + 1) * residual[k] - (k - 1) * residual[k - 1]
        ) / (k + 2)
        residual.append(next_value)
    return residual


def residual_criterion(node, residual):
    return [
        (1 - node) * current * (current - previous) / node
        for previous, current in zip(residual, residual[1:])
    ]


def scalar_jacobi_at_root(root, step):
    """Evaluate the normalized Jacobi polynomial at an exact rational root variable."""
    y = (1 - root) / 2
    value = Fraction(1)
    product = 1
    for ell in range(1, step):
        r = ell - 1
        product *= (step - 1 - r) * (step + 2 + r)
        value += (-1) ** ell * product * y**ell / (
            factorial(ell) * factorial(ell + 1)
        )
    return value


def direct_trials(nodes, start, weights, trial_limit):
    """Run the actual first segment in diagonal coordinates, with h=1."""
    accepted = start
    extrapolated = start
    trials = []
    for k in range(1, trial_limit + 1):
        gradient = tuple((1 - s) * y for s, y in zip(nodes, extrapolated))
        trial = tuple(y - g for y, g in zip(extrapolated, gradient))
        difference = tuple(z - x for z, x in zip(trial, accepted))
        criterion = sum(
            w * difference_i * gradient_i
            for w, difference_i, gradient_i in zip(weights, difference, gradient)
        )
        trials.append({
            "k": k,
            "trial": [str(value) for value in trial],
            "criterion": str(criterion),
        })
        if not any(trial):
            return trials, "zero_trial", k, None
        if criterion > 0:
            old_gradient = tuple((1 - s) * x for s, x in zip(nodes, accepted))
            new_seed = tuple(x - g for x, g in zip(accepted, old_gradient))
            return trials, "strict_restart", k + 1, new_seed
        beta = Fraction(k - 1, k + 2)
        extrapolated = tuple(z + beta * d for z, d in zip(trial, difference))
        accepted = trial
    raise ValueError(f"No event through {trial_limit} trials")


def compare_trace(trials, start, weights, residual_by_node, c_by_node):
    for row in trials:
        k = row["k"]
        expected_trial = [
            str(value * residual[k])
            for value, residual in zip(start, residual_by_node)
        ]
        expected_criterion = sum(
            weight * initial**2 * c[k - 1]
            for weight, initial, c in zip(weights, start, c_by_node)
        )
        require(row["trial"] == expected_trial, f"Trial point mismatch at {k}")
        require(Fraction(row["criterion"]) == expected_criterion, f"Criterion mismatch at {k}")


def check_case(slow, upper_point, initial, n, dual_multiplier):
    fast = Fraction(1, 2)
    nodes = (slow, fast)
    k_max = n + 1
    residual_by_node = [residuals(node, k_max) for node in nodes]
    p_slow, _ = residual_by_node
    upper_residual = residuals(upper_point, n)
    require(all(value > 0 for value in p_slow[:n]), "Slow mode crossed before n")
    require(p_slow[n] < 0, "The slow mode must strictly cross at n")
    require(all(value > 0 for value in upper_residual), "The upper endpoint failed to bracket the root")
    c_by_node = [
        residual_criterion(node, residual)
        for node, residual in zip(nodes, residual_by_node)
    ]
    dual_margins = [values[4] + dual_multiplier * values[k_max - 1] for values in c_by_node]
    require(all(margin > 0 for margin in dual_margins), "Upper-bound coefficient is not positive")
    trial_data, reason, cost, new_seed = direct_trials(nodes, initial, (1, 1), k_max)
    compare_trace(trial_data, initial, (1, 1), residual_by_node, c_by_node)
    require(len(trial_data) == k_max and reason == "strict_restart", "Wrong active-time event")
    require(cost == k_max + 1, "Wrong gradient cost")
    require(all(Fraction(row["criterion"]) < 0 for row in trial_data[:-1]), "An early test was not strict")
    require(all(any(Fraction(value) for value in row["trial"]) for row in trial_data), "Unexpected zero trial")
    expected_seed = tuple(s * start * residual[k_max - 1] for s, start, residual in zip(nodes, initial, residual_by_node))
    require(new_seed == expected_seed, "The restart did not recompute a step from the old point")
    pure_data, pure_reason, pure_cost, _ = direct_trials((slow,), (Fraction(1),), (1,), n)
    require(len(pure_data) == n and pure_reason == "strict_restart" and pure_cost == n + 1, "Wrong pure-mode event")
    return {
        "slow_node": str(slow),
        "fast_node": str(fast),
        "hessian_diagonal": [str(1 - slow), str(1 - fast)],
        "initial_point": [str(value) for value in initial],
        "largest_slow_root_strict_bracket": [str(slow), str(upper_point)],
        "slow_mode_first_trial_event": n,
        "worst_first_trial_event": k_max,
        "witness_gradient_calls": cost,
        "dual_certificate": {
            "trial_indices": [5, k_max],
            "coefficients": [1, dual_multiplier],
            "nodewise_positive_margins": [str(value) for value in dual_margins],
        },
        "witness_first_segment": trial_data,
    }


def check_exact_tie():
    slow, fast = Fraction(7599, 10000), Fraction(1, 2)
    nodes = (slow, fast)
    residual_by_node = [residuals(node, 8) for node in nodes]
    c_by_node = [
        residual_criterion(node, residual)
        for node, residual in zip(nodes, residual_by_node)
    ]
    omega = c_by_node[0][6] / (-c_by_node[1][6])
    require(omega > 0, "The normalized fast weight must be positive")
    # Coordinate vectors are multiplied by sqrt(omega) in the second
    # physical coordinate. Keep the squared factor exact in inner products.
    start = (Fraction(1), Fraction(1))
    weights = (Fraction(1), omega)
    trials, reason, cost, _ = direct_trials(nodes, start, weights, 8)
    compare_trace(trials, start, weights, residual_by_node, c_by_node)
    tests = [Fraction(row["criterion"]) for row in trials]
    require(len(trials) == 8 and reason == "strict_restart", "The tie was not accepted")
    require(all(value < 0 for value in tests[:6]), "An early test was not negative")
    require(tests[6] == 0 and tests[7] > 0, "Incorrect strict-inequality behavior")
    require(any(Fraction(v) for v in trials[6]["trial"]), "The tie coincided with terminal zero")
    return {
        "physical_initial_point": "(1, sqrt(omega))",
        "fast_to_slow_weight_ratio": str(omega),
        "nonterminal_zero_criterion_at_trial": 7,
        "strict_restart_at_trial": 8,
        "gradient_calls": cost,
        "unnormalized_criteria": [str(value) for value in tests],
    }


def check_terminal_zero():
    s = Fraction(1, 5)
    trial_data, reason, cost, seed = direct_trials((s,), (Fraction(1),), (1,), 4)
    require(len(trial_data) == 3 and reason == "zero_trial", "Wrong zero trial")
    require(cost == 3 and seed is None, "The terminal trial must skip recomputation")
    return {"node": str(s), "trial": 3, "gradient_calls": cost, "trace": trial_data}


def check_jacobi_representation():
    roots = (Fraction(7, 8), Fraction(99, 100), Fraction(63, 64))
    count = 0
    for root in roots:
        p = residuals(root**2, 64)
        for k in range(1, 65):
            require(
                p[k] == root ** (k + 1) * scalar_jacobi_at_root(root, k),
                f"Jacobi identity failed at {root}, k={k}",
            )
            count += 1
    return {"rational_arguments": [str(value) for value in roots], "equalities": count}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="Write the JSON record to this path.")
    args = parser.parse_args()
    record = {
        "scope": "finite exact checks only",
        "case_7_8": check_case(
            Fraction(7599, 10000), Fraction(7600, 10000),
            (Fraction(1), Fraction(1)), 7, 32
        ),
        "case_36_37": check_case(
            Fraction(49450896852043, 50000000000000),
            Fraction(98901793704087, 100000000000000),
            (Fraction(2), Fraction(1)), 36, 64
        ),
        "strict_inequality_tie": check_exact_tie(),
        "terminal_zero": check_terminal_zero(),
        "jacobi_representation": check_jacobi_representation(),
    }
    result = json.dumps(record, indent=2) + "\n"
    if args.output:
        args.output.write_text(result, encoding="utf-8")
    print("PASS: 7/8 and 36/37 certificates, tie and zero events, 192 Jacobi equalities")
    if not args.output:
        print(result, end="")


if __name__ == "__main__":
    main()
