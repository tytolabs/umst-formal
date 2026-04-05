#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
"""
Generate illustrative GIF/PNG assets for the meso-scale Economic layer (Wave 6.5.2).

Reads optional CSV/JSON from:
  - UMST_VISUAL_DATA_DIR (env), or
  - visuals/fixtures/ (bundled synthetic series),

writes to visuals/out/ (created automatically).
"""
from __future__ import annotations

import json
import os
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
OUT = REPO_ROOT / "visuals" / "out"
FIXTURES = REPO_ROOT / "visuals" / "fixtures"


def _load_series() -> tuple[list[float], list[float]]:
    env = os.environ.get("UMST_VISUAL_DATA_DIR")
    if env:
        p = Path(env) / "burden_series.json"
        if p.is_file():
            data = json.loads(p.read_text())
            return list(data["t"]), list(data["b"])
    fp = FIXTURES / "burden_series.json"
    if fp.is_file():
        data = json.loads(fp.read_text())
        return list(data["t"]), list(data["b"])
    # synthetic exponential relaxation
    t = [float(i) for i in range(0, 41)]
    b = [1.0 * (0.92**i) for i in t]
    return t, b


def main() -> None:
    OUT.mkdir(parents=True, exist_ok=True)
    t, b = _load_series()
    try:
        import matplotlib.pyplot as plt
        import numpy as np
    except ImportError:
        (OUT / "VISUALS_README.txt").write_text(
            "Install optional deps: pip install -r requirements-visuals.txt\n"
            "Then re-run: python3 scripts/generate_visuals.py\n",
            encoding="utf-8",
        )
        print("Skipping figure render (matplotlib/numpy not installed); wrote visuals/out/VISUALS_README.txt")
        return

    fig, ax = plt.subplots(figsize=(6, 3.5))
    ax.plot(t, b, color="#0d47a1", lw=2, label="B(t) surrogate")
    ax.set_xlabel("step")
    ax.set_ylabel("burden (arb.)")
    ax.set_title("Exponential learning / burden decay (illustrative)")
    ax.legend()
    ax.grid(True, alpha=0.3)
    png = OUT / "b_t_decay.png"
    fig.tight_layout()
    fig.savefig(png, dpi=120)
    plt.close(fig)

    # Pie chart: productive vs waste split (static illustration)
    fig2, ax2 = plt.subplots(figsize=(4, 4))
    ax2.pie([0.72, 0.28], labels=("productive Q", "waste Q"), autopct="%1.0f%%", startangle=90)
    ax2.set_title("Entropy split (illustrative)")
    fig2.savefig(OUT / "entropy_split_pie.png", dpi=120)
    plt.close(fig2)

    # GIF from burden series (if imageio available)
    try:
        import imageio.v3 as iio
    except ImportError:
        print(f"Wrote {png} and entropy_split_pie.png (install imageio for GIF output).")
        return

    frames = []
    for k in range(2, min(len(b), 30)):
        fig, ax = plt.subplots(figsize=(5, 3))
        ax.plot(t[:k], b[:k], color="#b71c1c", lw=2)
        ax.set_ylim(0, max(b) * 1.1)
        ax.set_xlabel("step")
        ax.set_ylabel("burden")
        ax.set_title("Animated decay (preview)")
        fig.canvas.draw()
        frames.append(np.asarray(fig.canvas.buffer_rgba())[:, :, :3].copy())
        plt.close(fig)
    gif_path = OUT / "b_t_decay.gif"
    iio.imwrite(gif_path, frames, duration=0.15, loop=0)
    print(f"Wrote {gif_path}, {png}, {OUT / 'entropy_split_pie.png'}")


if __name__ == "__main__":
    main()
