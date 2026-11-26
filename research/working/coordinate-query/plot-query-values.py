from pathlib import Path
import math
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

def axis_value(kappa):
    threshold = (3 + math.sqrt(5)) / 2
    if kappa <= threshold:
        return 1 / math.sqrt(kappa)
    low, high = 2 - 1 / kappa, kappa
    for _ in range(80):
        a = (low + high) / 2
        if 4 * a * a * (a - 1) * (kappa - 1) < (kappa * a - 1) ** 2:
            low = a
        else:
            high = a
    return 2 / (low + high)


widths = [2 ** (i / 64) for i in range(385)]
fig, ax = plt.subplots(figsize=(6.55, 2.42), layout="constrained")
ax.plot(widths, [8 * (k + 1) / (k + 3) ** 2 for k in widths],
        color="#174f76", linewidth=2, label="One balanced query")
ax.plot(widths, [axis_value(k) for k in widths], color="#a44d2b",
        linewidth=2, linestyle="--", label="One axis query")
ax.plot(widths, [1 / k for k in widths], color="#4d5761",
        linewidth=1.6, linestyle=":", label="No query")
ax.axhline(1, color="#396751", linewidth=1.35, linestyle="-.",
           label="Two independent queries")
ax.set_xscale("log", base=2)
ax.set_xticks([1, 2, 4, 8, 16, 32, 64], ["1", "2", "4", "8", "16", "32", "64"])
ax.set_ylim(0, 1.05)
ax.set_xlim(1, 64)
ax.set_xlabel(r"Spectral bound $\kappa$")
ax.set_ylabel("Guaranteed decrease ratio")
ax.yaxis.grid(alpha=.18, linewidth=.6)
ax.spines[["top", "right"]].set_visible(False)
ax.legend(loc="upper right", fontsize=8, frameon=False)
fig.savefig(Path(__file__).with_name("query-values.pdf"),
            metadata={"Title": "Deterministic coordinate-step guarantees", "Author": ""})
