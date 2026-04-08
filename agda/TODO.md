# Code cleanup tasks

For each run:

1. Select exactly one item from the TODO list below that is still marked `[ ]`.
2. Change its marker to `[-]` before starting work.
3. If running in Local mode, create a branch named `codex-<slug>` and switch to it.
   If running in a Codex worktree, keep the existing git/worktree setup unless instructed otherwise.
4. Make the smallest coherent change that resolves the selected item.
5. Run the project verification command(s).
6. If verification succeeds, change the item marker from `[-]` to `[x]`.
7. If verification fails or the task cannot be completed in this run, leave the item as `[-]` and report the blocker clearly.

## Verification

Run the project verification command from the Agda project root:

`agda -i . README.agda`

## TODO list

- [ ] kind-cleanup:
      Remove `Kinds.KM` from the codebase.

      More specifically:
      - starting from module `Kinds`, eliminate `Kinds.KM` throughout the project
      - whenever `KM ≤p pk` is used as a lower-bound constraint, remove that constraint
      - in those cases, instantiate `pk` to `KT`
      - remove the corresponding variable or parameter `pk` when it becomes unnecessary
      - fix the resulting fallout

      Keep changes minimal and do not perform unrelated refactors.