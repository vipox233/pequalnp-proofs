#!/usr/bin/env bash
# PNP_MODEL on "next" (tools/pnp.sh model_q): the model is ALWAYS sent; the cleaned value, or the word unknown when the
# variable is unset or cleans to nothing. The cleaning is done in the shell, by an explicit ASCII list, capped at 40.
# And the value appears in exactly ONE place: the query string of the desk's next call. Exit 1 on any miss.
set -u
here="$(cd "$(dirname "$0")" && pwd)"; P="$here/pnp.sh"
fn="$(sed -n '/^model_q() {/,/^}/p' "$P")"
bad=0
t() { local want="$1"; shift; local got; got="$(env "$@" bash -c "$fn"$'\n''model_q')"; [ "$got" = "$want" ] && echo "ok   [$*] -> '$got'" || { echo "FAIL [$*] -> '$got' (want '$want')"; bad=1; }; }
t '&model=unknown'                     -u PNP_MODEL
t '&model=unknown'                     PNP_MODEL=
t '&model=claude-opus-5.5'             PNP_MODEL=claude-opus-5.5
t '&model=GPT_5.1-mini'                PNP_MODEL=GPT_5.1-mini
t '&model=claudeopus5.5evilxtrue'      'PNP_MODEL=claude opus 5.5; evil=x&true'
t '&model=abcdefghijklmnopqrstuvwxyz0123456789ABCD' PNP_MODEL=abcdefghijklmnopqrstuvwxyz0123456789ABCDEFGH
t '&model=rm-rf'                       'PNP_MODEL=$(rm -rf /)&;|'
t '&model=unknown'                     'PNP_MODEL=!@#$%^&*() ;|/'
t '&model=modle'                       'PNP_MODEL=modèle'
t '&model=unknown'                     'PNP_MODEL=日本語 ＡＢＣ'
# the filter calls nothing outside the shell (no tr, sed, cut, python on the raw value)
echo "$fn" | grep -wqE '(tr|sed|cut|awk|perl|python|python3|iconv|eval|exec)' && { echo "FAIL model_q calls a program or eval on the value"; bad=1; } || echo "ok   model_q runs no outside program and no eval"
# ONE place: PNP_MODEL is read only inside model_q, and model_q is used only in the query string of a next call: the
# pnp desk's and, with --cause raredx, the raredx desk's (2026-11-26)
n_read=$(grep -vE '^\s*#' "$P" | grep -c 'PNP_MODEL'); n_use=$(grep -vE '^\s*#' "$P" | grep -c 'model_q')
in_next=$(grep -vE '^\s*#' "$P" | grep -E 'model_q\)' | grep -c 'q="handle=')
[ "$n_read" = 1 ] && [ "$n_use" = 3 ] && [ "$in_next" = 2 ] && echo "ok   the value is read once and used only in the next call's query (reads $n_read, uses $n_use incl. the definition)" || { echo "FAIL the value is read $n_read times, model_q used $n_use times, in the next query $in_next"; bad=1; }
grep -vE '^\s*#' "$P" | grep -nE 'model' | grep -vE 'model_q|PNP_MODEL' | grep -qE 'release|beat|submit|pr create|log|>>' && { echo "FAIL a model value reaches another call or a file"; bad=1; } || echo "ok   no other call, file or log line carries it"
[ $bad = 0 ] && echo "pnp model: pass"; exit $bad
