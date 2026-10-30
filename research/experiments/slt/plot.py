#!/usr/bin/env python3
"""Figures for the singular-learning-theory experiments.

Usage: plot.py toy1 RESULTS.json OUT.png
       plot.py rrr  RESULTS_DIR  OUT.png   (reads rrr_r*_H*.json)
       plot.py tanh RESULTS_DIR  OUT.png   (reads tanh_r*_H*_n*.json, n = 1000)
"""
import glob
import json
import sys

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402

SURFACE, INK, INK2, GRID = "#fcfcfb", "#0b0b0b", "#52514e", "#e4e3df"
BLUE, ORANGE, AQUA, YELLOW = "#2a78d6", "#eb6834", "#1baf7a", "#eda100"   # validated slots 1-4


def style(ax):
    ax.set_facecolor(SURFACE)
    for s in ("top", "right"):
        ax.spines[s].set_visible(False)
    for s in ("left", "bottom"):
        ax.spines[s].set_color(GRID)
    ax.tick_params(colors=INK2, labelsize=9)
    ax.grid(axis="y", color=GRID, linewidth=0.8)
    ax.set_axisbelow(True)


def toy1(path, out):
    d = json.load(open(path))
    ns = sorted(int(n) for n in d["results"])
    panels = [("regular", "y = w·x  (1 parameter, regular)"), ("k1", "y = a·b·x  (2 parameters)"),
              ("k2", "y = a·b²·x  (2 parameters)"), ("k3", "y = a·b³·x  (2 parameters)")]
    fig, axes = plt.subplots(1, 4, figsize=(13, 3.4), sharey=True, facecolor=SURFACE)
    for ax, (key, title) in zip(axes, panels):
        style(ax)
        lam = d["lambda"][key]
        ax.axhline(lam, color=INK2, linewidth=1.2, linestyle=(0, (4, 3)))
        ax.text(ns[0], lam + 0.015, f"λ = {lam:.3g}", color=INK2, fontsize=9, va="bottom")
        for est, color, marker, label in (("mle", ORANGE, "s", "max. likelihood = GD to convergence"),
                                          (key, BLUE, "o", "Bayes")):
            y = [d["results"][str(n)][est]["mean"] * n for n in ns]
            e = [d["results"][str(n)][est]["se"] * n for n in ns]
            ax.errorbar(ns, y, yerr=e, color=color, marker=marker, markersize=6, linewidth=2,
                        capsize=0, label=label)
        ax.set_xscale("log")
        ax.set_title(title, fontsize=10, color=INK, loc="left")
        ax.set_xlabel("training examples n", fontsize=9, color=INK2)
    axes[0].set_ylabel("n × E[generalization error]", fontsize=9, color=INK2)
    axes[0].set_ylim(0, 0.7)
    axes[0].legend(frameon=False, fontsize=8, loc="lower right", labelcolor=INK)
    fig.suptitle("Same parameter count, same (zero) Fisher information at the truth, different "
                 "generalization: Bayes follows λ/n, maximum likelihood does not",
                 fontsize=11, color=INK, x=0.01, ha="left")
    fig.tight_layout(rect=(0, 0, 1, 0.93))
    fig.savefig(out, dpi=160, facecolor=SURFACE)


def rrr(directory, out):
    rows = []
    for f in glob.glob(f"{directory}/rrr_r*_H*.json"):
        rows += json.load(open(f))["results"]
    nmax = max(x["n"] for x in rows)
    M, N = rows[0]["M"], rows[0]["N"]
    rs = [1, 2]
    fig, axes = plt.subplots(1, len(rs), figsize=(11, 4.2), sharey=True, facecolor=SURFACE)
    series = (("bayes", BLUE, "o", "Bayes"),
              ("gd_conv", ORANGE, "s", "GD to convergence"),
              ("gd_early_fair", YELLOW, "v", "GD, early stopping"),
              ("gd_plateau", AQUA, "^", "GD trajectory at plateau"))
    for ax, r in zip(axes, rs):
        style(ax)
        sel = sorted((x for x in rows if x["r"] == r and x["n"] == nmax and x["H"] >= r),
                     key=lambda x: x["H"])
        Hs = [x["H"] for x in sel]
        dr = r * (M + N - r) / 2
        ax.axhline(dr, color=INK2, linewidth=1.0, linestyle=(0, (1, 2)))
        ax.text(Hs[-1] + 0.15, dr, f"true-model\ndimension {dr:g}", color=INK2, fontsize=8, va="center")
        ax.plot(Hs, [x["lam"] for x in sel], color=INK2, linewidth=1.2, linestyle=(0, (4, 3)),
                marker="D", markersize=5)
        ax.text(Hs[-1] + 0.15, sel[-1]["lam"] + 0.25, "λ (theory)", color=INK2, fontsize=8, va="center")
        for est, color, marker, label in series:
            ys = [x[est]["mean"] for x in sel]
            ax.errorbar(Hs, ys, yerr=[x[est]["se"] for x in sel], color=color, marker=marker,
                        markersize=7, linewidth=2, capsize=0, label=label)
        ax.set_title(f"teacher needs r = {r} hidden unit{'s' if r > 1 else ''}", fontsize=10,
                     color=INK, loc="left")
        ax.set_xlabel("student hidden units H (width)", fontsize=9, color=INK2)
        ax.set_xticks(Hs)
        ax.set_xlim(Hs[0] - 0.4, Hs[-1] + 1.6)
    axes[0].set_ylabel(f"n × E[generalization error]  (n = {nmax})", fontsize=9, color=INK2)
    axes[0].set_ylim(0, 10)
    axes[0].legend(frameon=False, fontsize=8, loc="lower right", labelcolor=INK)
    fig.suptitle(f"Two-layer linear network ({M} inputs, {N} outputs): Bayes tracks λ and grows with width;\n"
                 "the gradient-descent plateau stays at the true-model dimension",
                 fontsize=11, color=INK, x=0.01, ha="left")
    fig.tight_layout(rect=(0, 0, 1, 0.93))
    fig.savefig(out, dpi=160, facecolor=SURFACE)


def overparam(directory, out):
    rows = []
    for f in glob.glob(f"{directory}/ov_*.json"):
        rows += json.load(open(f))["results"]
    ns = [20, 100, 2000]
    fig, axes = plt.subplots(1, len(ns), figsize=(13, 3.9), facecolor=SURFACE)
    series = (("bayes", BLUE, "o", "Bayes"),
              ("gd_conv", ORANGE, "s", "GD to convergence"),
              ("gd_early_fair", YELLOW, "v", "GD, early stopping"),
              ("gd_best_on_path", AQUA, "^", "GD best point on path"))
    for ax, n in zip(axes, ns):
        style(ax)
        sel = sorted((x for x in rows if x["n"] == n), key=lambda x: x["H"])
        Ps = [x["params"] for x in sel]
        for est, color, marker, label in series:
            ax.errorbar(Ps, [x[est]["mean"] for x in sel], yerr=[x[est]["se"] for x in sel],
                        color=color, marker=marker, markersize=7, linewidth=2, capsize=0, label=label)
        ax.set_title(f"n = {n} training examples", fontsize=10, color=INK, loc="left")
        ax.set_xlabel("parameters H·(M+N)", fontsize=9, color=INK2)
        ax.set_xticks(Ps)
        ax.set_ylim(bottom=0)
    axes[0].set_ylabel("E[generalization error]", fontsize=9, color=INK2)
    handles, labels = axes[0].get_legend_handles_labels()
    fig.legend(handles, labels, frameon=False, fontsize=9, loc="lower center", ncol=4, labelcolor=INK)
    fig.suptitle("More parameters than examples (10×10 linear network, teacher rank 2): "
                 "the gradient-descent path stays flat in width; Bayes grows",
                 fontsize=11, color=INK, x=0.01, ha="left")
    fig.tight_layout(rect=(0, 0.07, 1, 0.92))
    fig.savefig(out, dpi=160, facecolor=SURFACE)


def tanh(directory, out, n=1000):
    rows = []
    for f in glob.glob(f"{directory}/tanh_r*_H*_n*.json"):
        rows += json.load(open(f))["results"]
    rs = [1, 2]
    fig, axes = plt.subplots(1, len(rs), figsize=(11, 4.2), sharey=True, facecolor=SURFACE)
    series = (("bayes", BLUE, "o", "Bayes (HMC)"),
              ("gd_conv", ORANGE, "s", "GD after 60k steps (not converged for H > r)"),
              ("gd_early_fair", YELLOW, "v", "GD, early stopping (80/20 split)"),
              ("gd_best_on_path", AQUA, "^", "GD best point on path (oracle)"))
    for ax, r in zip(axes, rs):
        style(ax)
        sel = sorted((x for x in rows if x["r"] == r and x["n"] == n), key=lambda x: x["H"])
        Hs = [x["H"] for x in sel]
        dr = sel[0]["regular_half_dim"]
        ax.axhline(dr, color=INK2, linewidth=1.0, linestyle=(0, (1, 2)))
        ax.text(Hs[-1] + 0.3, dr, f"teacher\ndimension/2 = {dr:g}", color=INK2, fontsize=8, va="center")
        for est, color, marker, label in series:
            ax.errorbar(Hs, [x[est]["mean"] for x in sel], yerr=[x[est]["se"] for x in sel],
                        color=color, marker=marker, markersize=7, linewidth=2, capsize=0, label=label)
        ax.set_title(f"teacher has r = {r} tanh unit{'s' if r > 1 else ''}", fontsize=10,
                     color=INK, loc="left")
        ax.set_xlabel("student hidden units H (width)", fontsize=9, color=INK2)
        ax.set_xticks(Hs)
        ax.set_xlim(0.5, Hs[-1] + 2.5)
    axes[0].set_ylabel(f"n × E[generalization error]  (n = {n})", fontsize=9, color=INK2)
    axes[0].set_ylim(0, 25)
    axes[0].legend(frameon=False, fontsize=8, loc="upper left", labelcolor=INK)
    fig.suptitle("Nonlinear two-layer tanh network (3 inputs): Bayes grows slowly with width; "
                 "the best point on the GD path stays near the teacher dimension",
                 fontsize=11, color=INK, x=0.01, ha="left")
    fig.tight_layout(rect=(0, 0, 1, 0.93))
    fig.savefig(out, dpi=160, facecolor=SURFACE)


if __name__ == "__main__":
    {"toy1": toy1, "rrr": rrr, "overparam": overparam, "tanh": tanh}[sys.argv[1]](sys.argv[2], sys.argv[3])
