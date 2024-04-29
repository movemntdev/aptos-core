# Zero-Knowledge VM portability shims

This directory contains crates that allow reuse of aptos-core code between
regular CPU targets, where threading is permitted and desirable, and
zkVM where even independent tasks need to be executed sequentially
in deterministic matter.