#!/usr/bin/env python3
"""Render the side-by-side trace video frames from benchmarks/vanadium_trace.json.

Every plotted point is one sample of the selected runs in vanadium_trace.json, drawn at the
time (`t_ms`) it was measured and joined to the previous sample by a straight segment. Nothing
is smoothed, resampled or extrapolated, and no quantity that is absent from the trace (RAM in
particular) is drawn. The two device screens are the Speculos screenshots recorded during those
same runs (`f<microseconds>.png`), shown at the time they were captured.

Needs Pillow. Writes numbered PNG frames and a poster; encode with for example:
  ffmpeg -framerate 25 -i frames/f%05d.png -c:v libx264 -pix_fmt yuv420p -crf 30 \
         -preset veryslow -movflags +faststart vanadium_trace.mp4
"""

import argparse
import glob
import json
import os

from PIL import Image, ImageDraw, ImageFont

W, H = 960, 840
FPS = 25
HOLD_S = 2.0
SCREEN_W, SCREEN_H = 288, 360
SCREEN_Y = 92
PLOT = (118, 580, 930, 786)  # left, top, right, bottom
BG = (255, 255, 255)
INK = (28, 28, 30)
MUTED = (110, 110, 118)
GRID = (226, 226, 230)
COLORS = {"left": (196, 78, 28), "right": (24, 104, 196)}
FONT_PATHS = (
    "/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf",
    "/usr/share/fonts/dejavu/DejaVuSans.ttf",
    "/usr/share/fonts/TTF/DejaVuSans.ttf",
)


def font(size):
    for path in FONT_PATHS:
        if os.path.exists(path):
            return ImageFont.truetype(path, size)
    return ImageFont.load_default(size)


def load_screens(frames_root, run):
    pattern = os.path.join(frames_root, "run-%02d-%s" % (run["seq"], run["variant"]), "f*.png")
    screens = []
    for path in sorted(glob.glob(pattern)):
        t_ms = int(os.path.basename(path)[1:-4]) / 1000.0
        image = Image.open(path).convert("RGB").resize((SCREEN_W, SCREEN_H), Image.LANCZOS)
        screens.append((t_ms, image))
    assert screens, "no screenshots match " + pattern
    return screens


def nice_ceiling(value, step):
    return ((value + step - 1) // step) * step


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--trace", required=True)
    ap.add_argument("--frames-root", required=True, help="TRACE_OUT_DIR/frames of the recorded runs")
    ap.add_argument("--left-seq", type=int, required=True, help="seq of the reference run")
    ap.add_argument("--right-seq", type=int, required=True, help="seq of the lean_optimized run")
    ap.add_argument("--out-dir", required=True)
    ap.add_argument("--poster", required=True)
    args = ap.parse_args()

    with open(args.trace) as f:
        trace = json.load(f)
    by_seq = {run["seq"]: run for run in trace["runs"]}
    sides = {"left": by_seq[args.left_seq], "right": by_seq[args.right_seq]}
    assert sides["left"]["variant"] == "reference"
    assert sides["right"]["variant"] == "lean_optimized"
    titles = {"left": "Reference V-App", "right": "Lean-optimized V-App"}
    screens = {side: load_screens(args.frames_root, run) for side, run in sides.items()}

    x_max = nice_ceiling(max(len(run["samples"]) for run in sides.values()), 500)
    y_max = nice_ceiling(max(run["final"]["rv32_instructions"] for run in sides.values()), 50000)
    left, top, right, bottom = PLOT

    def px(apdu_index):
        return left + (right - left) * apdu_index / x_max

    def py(instructions):
        return bottom - (bottom - top) * instructions / y_max

    f_title, f_head, f_text, f_small = font(19), font(18), font(15), font(13)

    y_label = Image.new("RGB", (230, 20), BG)
    ImageDraw.Draw(y_label).text((0, 0), "executed RV32 instructions", font=f_small, fill=INK)
    y_label = y_label.rotate(90, expand=True)

    base = Image.new("RGB", (W, H), BG)
    d = ImageDraw.Draw(base)
    d.text((24, 14), "Vanadium Bitcoin V-App: one Taproot signature, reference vs Lean-optimized",
           font=f_title, fill=INK)
    d.text((24, 44), "Recorded Speculos Flex runs, real time (runs seq %d and seq %d of vanadium_trace.json)"
           % (args.left_seq, args.right_seq), font=f_small, fill=MUTED)
    d.text((left, top - 46), "Speculos, executed RV32 instructions, cumulative", font=f_head, fill=INK)
    d.text((left, top - 22), "one point per APDU exchange, straight segments between measured samples",
           font=f_small, fill=MUTED)
    for i in range(0, y_max + 1, 50000):
        d.line([(left, py(i)), (right, py(i))], fill=GRID)
        label = "%d k" % (i // 1000) if i else "0"
        d.text((left - 8, py(i)), label, font=f_small, fill=MUTED, anchor="rm")
    for i in range(0, x_max + 1, 500):
        d.line([(px(i), top), (px(i), bottom)], fill=GRID)
        d.text((px(i), bottom + 6), str(i), font=f_small, fill=MUTED, anchor="ma")
    d.line([(left, top), (left, bottom), (right, bottom)], fill=INK)
    d.text(((left + right) // 2, bottom + 26), "APDU exchange index", font=f_small, fill=INK, anchor="ma")
    base.paste(y_label, (left - 78, (top + bottom) // 2 - y_label.size[1] // 2))
    centers = {"left": W // 4, "right": 3 * W // 4}
    for side in sides:
        d.text((centers[side], SCREEN_Y - 12), titles[side], font=f_head, fill=COLORS[side], anchor="mb")
        x0 = centers[side] - SCREEN_W // 2
        d.rectangle([x0 - 2, SCREEN_Y - 2, x0 + SCREEN_W + 1, SCREEN_Y + SCREEN_H + 1], outline=INK, width=2)

    duration_ms = max(run["samples"][-1]["t_ms"] for run in sides.values())
    duration_ms = max(duration_ms, max(s[-1][0] for s in screens.values()))
    n_frames = int(duration_ms / 1000.0 * FPS) + 2 + int(HOLD_S * FPS)
    os.makedirs(args.out_dir, exist_ok=True)

    cursor = {side: 0 for side in sides}
    points = {side: [] for side in sides}
    image = None
    for n in range(n_frames):
        t_ms = n * 1000.0 / FPS
        image = base.copy()
        d = ImageDraw.Draw(image)
        d.text((W - 24, 18), "t = %.2f s" % min(t_ms / 1000.0, duration_ms / 1000.0),
               font=f_head, fill=INK, anchor="ra")
        for side, run in sides.items():
            samples = run["samples"]
            while cursor[side] < len(samples) and samples[cursor[side]]["t_ms"] <= t_ms:
                s = samples[cursor[side]]
                points[side].append((px(s["apdu_index"]), py(s["rv32_instructions"])))
                cursor[side] += 1
            shown = [img for (ts, img) in screens[side] if ts <= t_ms]
            x0 = centers[side] - SCREEN_W // 2
            if shown:
                image.paste(shown[-1], (x0, SCREEN_Y))
            if len(points[side]) > 1:
                d.line(points[side], fill=COLORS[side], width=2)
            y = SCREEN_Y + SCREEN_H + 12
            if cursor[side]:
                s = samples[cursor[side] - 1]
                d.ellipse([points[side][-1][0] - 4, points[side][-1][1] - 4,
                           points[side][-1][0] + 4, points[side][-1][1] + 4], fill=COLORS[side])
                lines = (
                    "APDU exchange %d  ·  phase %s" % (s["apdu_index"], s["phase"]),
                    "page loads %s" % format(s["vm_page_loads"], ","),
                    "instructions %s" % format(s["rv32_instructions"], ","),
                )
            else:
                lines = ("no APDU exchanged yet", "page loads 0", "instructions 0")
            d.text((centers[side], y), lines[0], font=f_small, fill=MUTED, anchor="ma")
            d.text((centers[side], y + 20), lines[1], font=f_head, fill=COLORS[side], anchor="ma")
            d.text((centers[side], y + 44), lines[2], font=f_text, fill=INK, anchor="ma")
        image.save(os.path.join(args.out_dir, "f%05d.png" % n))

    for side, run in sides.items():
        assert cursor[side] == len(run["samples"]), side
    image.save(args.poster, optimize=True)
    print("frames=%d fps=%d duration_ms=%.1f x_max=%d y_max=%d poster=%s"
          % (n_frames, FPS, duration_ms, x_max, y_max, args.poster))


if __name__ == "__main__":
    main()
