#!/usr/bin/env python3
"""Run a GP script through cypari2 when no `gp` binary is installed.
usage: python3 run_gp.py script.gp [stack_bytes]"""
import sys, cypari2
pari = cypari2.Pari()
pari.allocatemem(int(sys.argv[2]) if len(sys.argv) > 2 else 4*10**9, silent=True)
print("PARI version", pari('version()'))
pari('read("%s")' % sys.argv[1])
