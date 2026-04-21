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

- [x] refactoring:
      Refactor ExprPreservationStep2.

      Specifically:
      - identify groups of lemmas with a common theme, like dealing with context predicates like RemoveCtx, dealing with substitutions, or auxiliary results about typing derivations.
      - for each group create a new module with a fresh name derived from the group's theme.
      - move all definitions in the group to their thematic module and add the respective imports to ExprPreservationStep2.

- [x] cleanup-bindings:
      Tighten the definitions for bindings in ExprNormalTyping

      Specifically:
      - The types `Binding` and `BindingView` are isomorphic. 
      - Remove the definitions of `BindingView` and its conversion function `bindingView`. 
      - Change all uses of `BindingView` to `Binding`, fix the constructor names, and process the fallout.

- [ ] unused-postulates:
      Remove unused postulates from the codebase.

      More specifically:
      - scan all modules for postulates
      - if a postulate is neither used locally nor exported, then delete it

- [ ] unused-imports:
      Remove unused imports from the codebase.

      Specifically:
      - scan all modules for unused imports
      - remove unused imports from the import list

- [ ] kind-cleanup:
      Remove `Kinds.KM` from the codebase.

      More specifically:
      - starting from module `Kinds`, eliminate `Kinds.KM` throughout the project
      - whenever `KM ≤p pk` is used as a lower-bound constraint, remove that constraint
      - in those cases, instantiate `pk` to `KT`
      - remove the corresponding variable or parameter `pk` when it becomes unnecessary
      - fix the resulting fallout

      Keep changes minimal and do not perform unrelated refactors.
