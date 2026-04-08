# Repository expectations

## Scope

These instructions apply to the Agda project rooted in this directory.

## README.agda

`README.agda` is the maintained module index for this Agda project.

When updating `README.agda`:
- Include every project module under this directory that belongs in the maintained index.
- For each imported module, place a two-line prose description immediately before the import.
- Keep the existing module order unless the user explicitly asks to reorder it.
- Preserve existing descriptions unless they are missing or no longer accurate.
- Do not touch unrelated files unless required for verification.

## Verification

After changing `README.agda`, run the project verification command from this directory.

Replace the placeholder below with the exact command for this project and keep it up to date:

`agda -i . README.agda`
