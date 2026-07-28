#!/bin/sh
# wacoq-pages.sh — build a set of self-contained, cross-linked waCoq pages
#
#   usage: ./wacoq-pages.sh "file.v::Menu label" ...
#
#   example:
#     ./wacoq-pages.sh \
#        "core_logic_is_not_paraconsistent.v::Additive certification" \
#        "core_logic_F_multiplicative.v::Multiplicative certification" \
#        "core_step1_fragment_F.v::Fragment F"
#
# Each FILE.v yields a FILE.html carrying the full navigation bar, with the
# current page shown in bold and unlinked.
#
# Run from the examples/ directory of the waCoq installation (the one holding
# test.html and scratchpad.html): the relative import ../jscoq.js depends on it.

set -e

[ $# -ge 1 ] || { echo "usage: $0 \"file.v::Label\" ..." >&2; exit 1; }

# --- first pass: validate everything before writing anything ---
for ARG in "$@"; do
  SRC=${ARG%%::*}
  [ -r "$SRC" ] || { echo "wacoq-pages.sh: cannot read $SRC" >&2; exit 1; }
done

# --- navigation bar ---
# $1 = argument of the page being generated; $2... = all arguments
nav_bar() {
  CURRENT="$1"
  shift
  printf '        <nav class="wacoq-nav">\n'
  for ARG in "$@"; do
    SRC=${ARG%%::*}
    LABEL=${ARG#*::}
    [ "$LABEL" = "$ARG" ] && LABEL=$(basename "$SRC" .v)
    if [ "$SRC" = "${CURRENT%%::*}" ]; then
      printf '          <span class="here">%s</span>\n' "$LABEL"
    else
      printf '          <a href="%s.html">%s</a>\n' "$(basename "$SRC" .v)" "$LABEL"
    fi
  done
  printf '        </nav>\n'
}

# --- second pass: generation ---
for ARG in "$@"; do
  SRC=${ARG%%::*}
  TITLE=${ARG#*::}
  [ "$TITLE" = "$ARG" ] && TITLE=$(basename "$SRC" .v)
  OUT="$(basename "$SRC" .v).html"

  # Minimal escaping for insertion into a <textarea>:
  # & first, then < ; > needs no escaping.
  ESCAPED=$(sed -e 's/&/\&amp;/g' -e 's/</\&lt;/g' "$SRC")
  NAV=$(nav_bar "$ARG" "$@")

  cat > "$OUT" <<HTML
<!DOCTYPE html>
<html xmlns="http://www.w3.org/1999/xhtml" lang="en">
  <head>
    <meta http-equiv="content-type" content="text/html;charset=utf-8" />
    <meta name="description" content="$TITLE" />
    <link rel="icon" href="../ui-images/favicon.png">
    <title>$TITLE</title>
    <style>
      #document { max-width: 46em; margin: 0 auto; padding: 1em 2em 4em; }
      #document h1 { font-size: 1.4em; margin-bottom: 0.3em; }
      #document .hint { color: #555; font-size: 0.9em; }
      .wacoq-nav { margin: 0.8em 0 1.2em; padding: 0.5em 0;
                   border-top: 1px solid #ddd; border-bottom: 1px solid #ddd;
                   font-size: 0.9em; }
      .wacoq-nav a, .wacoq-nav .here { margin-right: 1.2em; }
      .wacoq-nav .here { font-weight: bold; color: #333; }
      .CodeMirror-lines { padding-bottom: 60% !important; }
    </style>
  </head>

<body class="jscoq-main">
  <div id="ide-wrapper" class="toggled">
    <div id="code-wrapper">
      <div id="document">
        <h1>$TITLE</h1>
$NAV
        <p class="hint">
          Source: <code>$(basename "$SRC")</code>.
          <kbd>Alt</kbd>+<kbd>&#8595;</kbd> / <kbd>Alt</kbd>+<kbd>&#8593;</kbd>
          to step forward and back through the proof,
          <kbd>Alt</kbd>+<kbd>Enter</kbd> to run to the cursor,
          <kbd>F8</kbd> to toggle the goal panel.
        </p>
        <textarea id="coq-source">
$ESCAPED
        </textarea>
      </div>
    </div>
  </div>

  <script type="module">
    import { JsCoq } from '../jscoq.js';

    /* Backend fixed here: the page depends on no URL parameter. */
    var jscoq_ids  = ['coq-source'];
    var jscoq_opts = {
        backend:       'wa',
        prelude:       true,
        implicit_libs: true,
        focus:         false,
        editor:        { mode: { 'company-coq': true } },
        init_pkgs:     ['init'],
        all_pkgs:      ['coq']
        /* No file_dialog, no data-filename: nothing is restored from
           localStorage or IndexedDB, so there is no race to lose. */
    };

    JsCoq.start(jscoq_ids, jscoq_opts).then(res => window.coq = res);
  </script>
</body>
</html>
HTML

  echo "written: $OUT" >&2
done
