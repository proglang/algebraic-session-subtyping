# Repository expectations

## Scope

These instructions apply to the Agda project rooted in this directory.

## global instructions for the whole project

This is an Agda proof project.

General rules about files:
- Ignore the contents of directory `Obsolete`.
- Ignore modules with names ending in `-exp`. These are experimental modules. 
  You may read these modules, but you must not edit them in any way.

Always run Agda after every nontrivial edit:
  agda -i . README.agda

Do not weaken theorem statements, do not remove constructors, do not postulate missing proofs,
do not add TERMINATING/NON_TERMINATING pragmas, do not use --type-in-type unless explicitly asked.

Prefer small local lemmas over large rewrites.

When stuck:
1. state the current goal and context,
2. explain the obstruction,
3. propose one or two lemma statements,
4. do not make speculative global refactorings.

Preserve existing naming and style.

Use holes deliberately:
- temporary holes are allowed while exploring;
- the final patch must contain no new holes unless explicitly requested.

For equality/transport problems:
- first try pattern matching and with-abstraction;
- then try rewrite/equational reasoning;
- only introduce subst/transport lemmas if the proof remains readable.

For termination problems:
- do not add pragmas;
- expose a structurally smaller argument;
- consider auxiliary functions with explicit measures.

## README.agda

`README.agda` is the maintained module index for this Agda project.

When updating `README.agda`:
- Include every project module under this directory in the maintained index.
- Observe the rules about ignored files and directories.
- For each imported module, place a two-line prose description immediately before the import.
- Place modules in subdirectory `X` directly before module `X.agda`.
- Keep the existing module order unless the user explicitly asks to reorder it.
- Preserve existing descriptions unless they are missing or no longer accurate.
- Do not touch unrelated files unless required for verification.

## Verification

After changing `README.agda`, run the following project verification command from this directory.

`agda -i . README.agda`

