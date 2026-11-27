#!/bin/sh
# THE PARSER'S SANDBOX (27 Nov; red team 14:20Z/14:21Z, round two 14:33Z). Run as root by tools/read-parse.sh, with an
# empty environment:
#   sudo -n /usr/bin/env -i PATH=/usr/bin:/bin /bin/sh tools/read-sandbox.sh <jail> <judge blob>
# <jail> holds tools/read-decision.py, tools/outside-read.py and in/proof.lean, read only. In new network, IPC, UTS, PID
# and mount namespaces it builds a RESTRICTED ROOT on an empty tmpfs: /usr (the runtime, read only, with the usual
# bin, sbin, lib and lib64 links), /jail (the jail, read only, no exec), a fresh /proc and a small /tmp. Nothing else of
# the host is in it: no /home, /opt, /etc, /var, /run, no workspace, no runner files. It changes root into it, enters
# /jail as the working directory, then runs as nobody with no new privileges, no capabilities, limits, an environment
# of PATH and LANG only, and python3 -I -S. It prints only what the parser prints; its status is the parser's.
set -eu
[ "$#" = 2 ] && [ -d "$1" ] || exit 2
printf '%s' "$2" | grep -Eqx '[0-9a-f]{40}|none' || exit 2
NR=/pnp-read-root
mkdir -p "$NR"
exec /usr/bin/unshare --net --ipc --uts --pid --fork --mount -- /bin/sh -eu -c '
  NR=$3
  mount --make-rprivate /
  mount -t tmpfs -o size=8m,mode=0755,nosuid,nodev tmpfs "$NR"
  mkdir "$NR/usr" "$NR/jail" "$NR/proc" "$NR/tmp"
  mount --bind /usr "$NR/usr";   mount -o remount,bind,ro,nosuid,nodev "$NR/usr"
  mount --bind "$1" "$NR/jail";  mount -o remount,bind,ro,nosuid,nodev,noexec "$NR/jail"
  mount -t proc -o nosuid,nodev,noexec proc "$NR/proc"
  mount -t tmpfs -o size=8m,mode=1777,nosuid,nodev,noexec tmpfs "$NR/tmp"
  ln -s usr/bin "$NR/bin"; ln -s usr/sbin "$NR/sbin"; ln -s usr/lib "$NR/lib"
  if [ -d /usr/lib64 ]; then ln -s usr/lib64 "$NR/lib64"; fi
  mount -o remount,ro,nosuid,nodev "$NR"
  exec /usr/sbin/chroot "$NR" /usr/bin/setpriv --reuid=65534 --regid=65534 --clear-groups --no-new-privs --inh-caps=-all --bounding-set=-all -- \
    /usr/bin/prlimit --as=1073741824 --cpu=60 --fsize=65536 --nofile=64 --nproc=64 --core=0 -- \
    /usr/bin/env -i -C /jail PATH=/usr/bin LANG=C.UTF-8 \
    /usr/bin/timeout -s KILL 90 /usr/bin/python3 -I -S /jail/tools/read-decision.py /jail/in/proof.lean "$2"
' sh "$1" "$2" "$NR"
