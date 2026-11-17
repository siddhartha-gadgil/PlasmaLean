# Example run

A toy problem to try the framework: a list of at most five distinct natural numbers, each at most
10, with the largest sum (the optimum is `[10, 9, 8, 7, 6]`, with sum 40). The seeds are a small
valid list and a near miss whose entries repeat.

```bash
scripts/theory_server/ensure_server.sh
D=notes/reasoning/$(date +%F)-evolve-example
python3 scripts/evolve/evolve.py init $D
cp .agents/skills/plasmalean-evolve-optimize/example/problem.json .agents/skills/plasmalean-evolve-optimize/example/context.lean $D/
cp .agents/skills/plasmalean-evolve-optimize/example/seeds/*.lean $D/generations/gen-000/candidates/
python3 scripts/evolve/evolve.py evaluate $D
python3 scripts/evolve/evolve.py select $D
python3 scripts/evolve/evolve.py next $D
```

Then analyse, generate and evaluate as described in the skill.
