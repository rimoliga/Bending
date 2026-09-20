#!/usr/bin/env python3
"""Render the Bend engine's ii-V-I voicings as a printable practice sheet.

The premise of this project is that the calculation happens in Bend --
where it is proved -- and anything prettier happens outside it. So this
script computes nothing about music. It runs the engine once per key,
parses the minimal text the engine prints, and draws it.

    python3 tools/fretboard.py                 # 12 keys, major, 2-note shells
    python3 tools/fretboard.py --shape 3       # three-note shells
    python3 tools/fretboard.py --minor         # ii(half-dim) - V - i
    python3 tools/fretboard.py -o sheet.html   # where to write

Keys are visited in the cycle of fourths (C F Bb Eb Ab Db Gb B E A D G),
the order every jazz musician practices in -- and the order Bend's own
`cycle_of_fourths_visits_all` law proves really does reach all twelve.

Output is a self-contained HTML file with inline SVG, styled for paper:
open it and print it (or "Save as PDF" from the browser's print dialog).
No third-party packages, no network.
"""

import argparse
import html
import os
import re
import shutil
import subprocess
import sys

# the cycle of fourths, the order the sheet is laid out in
KEYS = ["C", "F", "Bb", "Eb", "Ab", "Db", "Gb", "B", "E", "A", "D", "G"]

# as the engine labels them, low to high; the diagram draws them in this
# order, left to right, the way a chord box is read
STRINGS = ["E", "A", "D", "G", "B", "e"]

FRETS_SHOWN = 5

# a token such as "A10:R", "D8:3" or "G9:7": string label, fret, role
TOKEN = re.compile(r"^([EADGBe])(\d+):(.+)$")


class EngineError(RuntimeError):
    pass


# ---------------------------------------------------------------- engine

def find_bend(explicit):
    """Locate the `bend` command, or explain how to get one."""
    if explicit:
        return explicit
    found = shutil.which("bend")
    if found:
        return found
    raise EngineError(
        "no `bend` on PATH. Bend 2 is a TypeScript program run with bun:\n"
        "  git clone --depth 1 https://github.com/bendlang/bend /tmp/bend-src\n"
        "  printf '#!/usr/bin/env bash\\nexec bun /tmp/bend-src/bend2/main.ts \"$@\"\\n' \\\n"
        "    > ~/.local/bin/bend && chmod +x ~/.local/bin/bend\n"
        "or pass --bend /path/to/bend."
    )


def run_engine(bend, repo_root, key, flags):
    """Run `bend main.bend <key> [flags]` and hand back its stdout."""
    cmd = [bend, "main.bend", key] + list(flags)
    proc = subprocess.run(
        cmd, cwd=repo_root, capture_output=True, text=True,
    )
    if proc.returncode != 0:
        raise EngineError(
            "`%s` failed (exit %d):\n%s%s"
            % (" ".join(cmd), proc.returncode, proc.stdout, proc.stderr)
        )
    return proc.stdout


# ---------------------------------------------------------------- parsing

def parse_exercise(text, key):
    """Parse one run's output into (title, [chord, chord, chord]).

    The engine's format, one chord per line:

        key F
        ii Gm7  A10:R D8:3 G10:7

    i.e. a degree label, the chord name, then one `<string><fret>:<role>`
    token per *sounding* string. Muted strings print nothing, which is why
    a two-note shell has two tokens and a three-note shell three.
    """
    lines = [ln for ln in text.splitlines() if ln.strip()]
    if not lines or not lines[0].startswith("key "):
        raise EngineError("key %s: expected a 'key ...' header, got:\n%s" % (key, text))
    title = lines[0][len("key "):].strip()

    chords = []
    for line in lines[1:]:
        parts = line.split()
        if len(parts) < 3:
            raise EngineError("key %s: cannot parse chord line %r" % (key, line))
        degree, name, tokens = parts[0], parts[1], parts[2:]
        notes = {}
        for token in tokens:
            m = TOKEN.match(token)
            if not m:
                raise EngineError("key %s: cannot parse token %r in %r" % (key, token, line))
            string, fret, role = m.group(1), int(m.group(2)), m.group(3)
            notes[string] = (fret, role)
        chords.append({"degree": degree, "name": name, "notes": notes})

    if len(chords) != 3:
        raise EngineError("key %s: expected 3 chords, got %d" % (key, len(chords)))
    return title, chords


# ---------------------------------------------------------------- drawing

def fret_window(frets):
    """The 5-fret window to draw, and whether the nut is in view.

    A voicing's frets are never more than 4 apart (Bend proves that much:
    it is one of the three conditions in `playable`), so five frets always
    suffice; the only choice is where the window starts.
    """
    pressed = [f for f in frets if f > 0]
    if not pressed:
        return 1, True
    if 0 in frets or max(pressed) <= FRETS_SHOWN:
        return 1, True
    return min(pressed), False


def svg_diagram(chord):
    """One chord box: 6 strings, 5 frets, a labelled dot per sounding note."""
    notes = chord["notes"]
    lo, at_nut = fret_window([f for f, _ in notes.values()])

    pad_x, pad_y = 22, 30            # room for the × / o marks and the fret number
    cell_w, cell_h = 20, 26
    width = pad_x * 2 + cell_w * (len(STRINGS) - 1)
    height = pad_y + cell_h * FRETS_SHOWN + 16

    def x_of(i):
        return pad_x + i * cell_w

    def y_of(row):                   # row 0 = the top line (nut or first fret)
        return pad_y + row * cell_h

    out = ['<svg viewBox="0 0 %d %d" class="box" role="img" aria-label="%s">'
           % (width, height, html.escape(chord["name"] + " chord diagram"))]

    # frets
    for row in range(FRETS_SHOWN + 1):
        thick = ' class="nut"' if row == 0 and at_nut else ""
        out.append('<line x1="%d" y1="%d" x2="%d" y2="%d"%s/>'
                   % (x_of(0), y_of(row), x_of(len(STRINGS) - 1), y_of(row), thick))
    # strings
    for i in range(len(STRINGS)):
        out.append('<line x1="%d" y1="%d" x2="%d" y2="%d"/>'
                   % (x_of(i), y_of(0), x_of(i), y_of(FRETS_SHOWN)))

    # the starting fret, when the window has moved up the neck
    if not at_nut:
        out.append('<text x="%d" y="%d" class="posn">%dfr</text>'
                   % (x_of(len(STRINGS) - 1) + 8, y_of(0) + 16, lo))

    for i, string in enumerate(STRINGS):
        if string not in notes:
            out.append('<text x="%d" y="%d" class="mute">&#215;</text>' % (x_of(i), pad_y - 8))
            continue
        fret, role = notes[string]
        if fret == 0:
            # an open string: a hollow circle above the nut, labelled the
            # same way a fretted dot is, so the two read alike
            out.append('<circle cx="%d" cy="%d" r="8" class="open"/>' % (x_of(i), pad_y - 12))
            out.append('<text x="%d" y="%d" class="openlabel">%s</text>'
                       % (x_of(i), pad_y - 8, html.escape(role)))
            continue
        row = fret - lo                       # 0-based row *below* the top line
        cy = y_of(row) + cell_h // 2
        out.append('<circle cx="%d" cy="%d" r="8" class="dot"/>' % (x_of(i), cy))
        out.append('<text x="%d" y="%d" class="dotlabel">%s</text>'
                   % (x_of(i), cy + 4, html.escape(role)))

    out.append("</svg>")
    return "".join(out)


# ---------------------------------------------------------------- the page

CSS = """
:root { color-scheme: light; }
* { box-sizing: border-box; }
body {
  margin: 0; padding: 24px 20px 40px;
  font: 14px/1.5 "Iowan Old Style", Georgia, "Times New Roman", serif;
  color: #1a1a1a; background: #fff;
}
header { max-width: 60rem; margin: 0 auto 20px; }
h1 { font-size: 22px; margin: 0 0 6px; letter-spacing: .01em; }
.sub { margin: 0; color: #555; font-size: 13px; }
.legend { margin: 10px 0 0; color: #555; font-size: 12px; }
.legend b { font-weight: 600; color: #1a1a1a; }
main { max-width: 60rem; margin: 0 auto; }
.key { break-inside: avoid; page-break-inside: avoid; margin: 0 0 14px;
       border-top: 1px solid #ddd; padding-top: 10px; }
.key h2 { font-size: 15px; margin: 0 0 6px; font-weight: 600; }
.row { display: flex; gap: 26px; flex-wrap: wrap; }
.chord { text-align: center; width: 150px; }
.chord .name { font-size: 13px; margin: 0 0 2px; font-weight: 600; }
.chord .degree { font-size: 11px; color: #666; margin: 0 0 4px;
                 text-transform: uppercase; letter-spacing: .08em; }
svg.box { width: 150px; height: auto; }
svg.box line { stroke: #444; stroke-width: 1; }
svg.box line.nut { stroke-width: 4; }
svg.box circle.dot { fill: #1a1a1a; }
svg.box circle.open { fill: #fff; stroke: #444; stroke-width: 1.5; }
svg.box text { text-anchor: middle; font-family: "Helvetica Neue", Arial, sans-serif; }
svg.box text.dotlabel { fill: #fff; font-size: 9px; font-weight: 700; }
svg.box text.openlabel { fill: #1a1a1a; font-size: 9px; font-weight: 700; }
svg.box text.mute { fill: #444; font-size: 13px; }
svg.box text.posn { fill: #444; font-size: 10px; text-anchor: start;
                    font-family: "Helvetica Neue", Arial, sans-serif; }
footer { max-width: 60rem; margin: 22px auto 0; color: #666; font-size: 11px;
         border-top: 1px solid #ddd; padding-top: 8px; }
@media print {
  body { padding: 0; font-size: 12px; }
  @page { margin: 12mm; }
  .key { border-top-color: #bbb; }
}
"""


def render_page(sheets, subtitle):
    parts = [
        "<!doctype html>",
        '<html lang="en"><head><meta charset="utf-8">',
        '<meta name="viewport" content="width=device-width, initial-scale=1">',
        "<title>ii-V-I practice sheet</title>",
        "<style>%s</style></head><body>" % CSS,
        "<header>",
        "<h1>ii-V-I shell voicings, cycle of fourths</h1>",
        '<p class="sub">%s</p>' % html.escape(subtitle),
        '<p class="legend">Each dot is labelled with the note it sounds: '
        "<b>R</b> root, <b>3</b> the third, <b>7</b> the seventh &mdash; the two "
        "guide tones are what carry the harmony. A filled dot is a fretted note, a "
        "hollow one above the nut is an open string, &#215; is a muted string. A number "
        "beside the top line is the starting fret. Every shape here was generated by "
        "the Bend engine and is playable by construction: its type carries a proof "
        "that no fret exceeds 15, no more than four fingers are needed, and the "
        "stretch is at most four frets.</p>",
        "</header><main>",
    ]
    for title, chords in sheets:
        parts.append('<section class="key"><h2>%s</h2><div class="row">' % html.escape(title))
        for chord in chords:
            parts.append(
                '<div class="chord"><p class="degree">%s</p><p class="name">%s</p>%s</div>'
                % (html.escape(chord["degree"]), html.escape(chord["name"]), svg_diagram(chord))
            )
        parts.append("</div></section>")
    parts.append("</main><footer>Generated by tools/fretboard.py from "
                 "<code>bend main.bend &lt;key&gt;</code> &mdash; the music is computed "
                 "and proved in Bend, the drawing happens here.</footer>")
    parts.append("</body></html>")
    return "\n".join(parts)


# ---------------------------------------------------------------- driver

def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("-o", "--out", default="ii-V-I-practice.html",
                    help="where to write the sheet (default: %(default)s)")
    ap.add_argument("--shape", choices=["2", "3"], default="2",
                    help="2 = guide tones only, 3 = root added on a bass string")
    ap.add_argument("--minor", action="store_true",
                    help="render the minor cadence iiø7 - V7 - im7")
    ap.add_argument("--bend", default=None, help="path to the bend executable")
    ap.add_argument("--keys", default=None,
                    help="comma-separated keys to render (default: the cycle of fourths)")
    args = ap.parse_args(argv)

    repo_root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    keys = [k.strip() for k in args.keys.split(",")] if args.keys else KEYS

    flags = []
    if args.minor:
        flags.append("minor")
    if args.shape == "3":
        flags.append("3")

    try:
        bend = find_bend(args.bend)
        sheets = []
        for key in keys:
            title, chords = parse_exercise(run_engine(bend, repo_root, key, flags), key)
            # main.bend falls back to C on a key it doesn't recognize, so
            # say so rather than quietly drawing the wrong key
            if title.split()[0] != key:
                print("warning: asked for key %r, engine answered %r" % (key, title),
                      file=sys.stderr)
            sheets.append((title, chords))
    except EngineError as exc:
        print("error: %s" % exc, file=sys.stderr)
        return 1

    subtitle = "%s cadence, %s. %d keys, %d voicings." % (
        "Minor (ii&#248;7 - V7 - im7)" if args.minor else "Major (iim7 - V7 - Imaj7)",
        "three-note shells (root, 3rd, 7th)" if args.shape == "3"
        else "two-note shells (3rd and 7th)",
        len(sheets), sum(len(c) for _, c in sheets),
    )
    # the subtitle carries one entity on purpose; everything else is escaped
    page = render_page(sheets, subtitle).replace("ii&amp;#248;7", "ii&#248;7")

    with open(args.out, "w", encoding="utf-8") as fh:
        fh.write(page)
    print("wrote %s (%d keys, %d voicings)"
          % (args.out, len(sheets), sum(len(c) for _, c in sheets)))
    return 0


if __name__ == "__main__":
    sys.exit(main())
