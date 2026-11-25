"""Verify the scalar quadratic example and the accepted-trajectory inequality."""
from fractions import Fraction as F


def f(x):
    return x * x / 2


def cycle(memory):
    return [F(1, 2)] + [F(2)] * (memory + 1)


def run_example(memory):
    alpha = cycle(memory)
    length = len(alpha)
    sigma = F(1, 4)
    pure = [F(1)]
    for k in range(4 * length):
        x = pure[-1]
        step = alpha[k % length]
        ref = max(f(q) for q in pure[max(0, k - memory):])
        value = f((1 - step) * x)
        if k % length == length - 1:
            assert ref == f(x) == value
            assert value > ref - sigma * step * x * x
        pure.append((1 - step) * x)
    for k in range(3 * length):
        assert abs(pure[k + length]) == abs(pure[k]) / 2

    accepted = [F(1)]
    eta = F(1, 2)
    trial_min, trial_max = min(alpha), max(alpha)
    lower = min(trial_min, 2 * eta * (1 - sigma))
    upper = 1 + trial_max ** 2
    descent = 2 * sigma * lower
    theta = upper / (upper + descent)
    for k in range(6 * length):
        x = accepted[-1]
        ref = max(f(q) for q in accepted[max(0, k - memory):])
        step = alpha[k % length]
        while f((1 - step) * x) > ref - sigma * step * x * x:
            step *= eta
        assert step >= lower
        new = (1 - step) * x
        assert f(new) <= theta * ref
        accepted.append(new)
    windows = [max(f(q) for q in accepted[max(0, k - memory):k + 1])
               for k in range(len(accepted))]
    for k in range(len(windows) - memory - 1):
        assert windows[k + memory + 1] <= theta * windows[k]


if __name__ == "__main__":
    for m in range(12):
        run_example(m)
    print("Exact periodic rejection and accepted-window bounds verified for M=0,...,11.")

def verify_actual_periodic_rejection(memory):
    history = [F(1)]
    last_steps = []
    pattern = cycle(memory)
    length = len(pattern)
    for k in range(8 * length):
        current = history[-1]
        reference = max(f(q) for q in history[max(0,k-memory):])
        step = pattern[k % length]
        contractions = 0
        while f((1-step)*current) > reference - F(1,4)*step*current**2:
            step *= F(2,5)
            contractions += 1
        last_steps.append(contractions)
        history.append((1-step)*current)
    assert last_steps == ([0]*(length-1)+[1])*8
    for start in range(0,8*length,length):
        assert abs(history[start+length]) == abs(history[start])/10
    assert history[-1] != 0


if __name__ == "__main__":
    for m in range(12):
        verify_actual_periodic_rejection(m)
    print("Exact real backtracking: one reduction per period and amplitude factor 1/10.")
