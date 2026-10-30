#!/usr/bin/env python3
"""Summarize and plot experiment 7 (tanh_anatomy.py output).

Usage: anatomy_report.py RESULTS.json OUT.png
"""
import json
import sys

import numpy as np
import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402

from plot import BLUE, ORANGE, AQUA, YELLOW, INK, INK2, SURFACE, style  # noqa: E402


def main(path, out):
    res = json.load(open(path))
    configs = sorted({(x["r"], x["H"]) for x in res})
    n = res[0]["n"]
    fig, axes = plt.subplots(1, len(configs), figsize=(4 * len(configs), 3.6), sharey=True,
                             facecolor=SURFACE)
    for ax, (r, H) in zip(axes, configs):
        style(ax)
        runs = [x for x in res if x["r"] == r and x["H"] == H]
        t = np.array([p["t"] for p in runs[0]["path"]])
        def med(key):
            return np.median([[n * p[key] for p in x["path"]] for x in runs], axis=0)
        gm = np.median([n * x["G_mle"] for x in runs])
        for key, color, label in (("G", BLUE, "n·G (vs truth)"), ("Dm", ORANGE, "n·D (vs r-unit MLE)"),
                                  ("Dmerge", AQUA, "n·D_merge (off duplication line)")):
            ax.plot(t[1:], med(key)[1:], color=color, linewidth=2, label=label)
        ax.axhline(gm, color=INK2, linestyle=(0, (4, 3)), linewidth=1)
        ax.axhline(r * 4 / 2, color=INK2, linestyle=(0, (1, 2)), linewidth=1)
        ax.set_xscale("log"); ax.set_yscale("log"); ax.set_ylim(1e-3, 1e3)
        ax.set_title(f"teacher r = {r}, student H = {H}", fontsize=10, color=INK, loc="left")
        ax.set_xlabel("gradient steps", fontsize=9, color=INK2)
        # text report
        print(f"\n== r={r} H={H} (n={n}, {len(runs)} datasets); n·G(MLE_r) median {gm:.2f}, r(d+1)/2 = {2*r}")
        for x in runs:
            P = x["path"]
            iG = int(np.argmin([p["G"] for p in P])); iD = int(np.argmin([p["Dm"] for p in P]))
            end = P[-1]
            active = sum(1 for v in end["norms"] if v > 0.1)
            print(f"  seed {x['seed']}: minG {n*P[iG]['G']:.2f} @ {P[iG]['t']:>7}  minD {n*P[iD]['Dm']:.3f} @ {P[iD]['t']:>7}"
                  f"  end: G {n*end['G']:.2f} D {n*end['Dm']:.3f} Dmerge {n*end['Dmerge']:.3f}"
                  f"  active {active}/{H} spread {np.round(end['spread'], 2).tolist()}")
    axes[0].set_ylabel(f"median over datasets (n = {n})", fontsize=9, color=INK2)
    axes[0].legend(frameon=False, fontsize=8, loc="upper right", labelcolor=INK)
    fig.suptitle("Anatomy of the tanh plateau: distance to the truth, to the teacher-sized MLE, and to the "
                 "duplication line (dashed: n·G of the r-unit MLE; dotted: r(d+1)/2)", fontsize=10, color=INK,
                 x=0.01, ha="left")
    fig.tight_layout(rect=(0, 0, 1, 0.92))
    fig.savefig(out, dpi=160, facecolor=SURFACE)


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
