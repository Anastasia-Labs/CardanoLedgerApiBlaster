# D6 FIX — Blaster `Optimize.main` dite' motive

Apply to Lean-blaster @ `59db213` (the revision `lakefile.lean` pins via
branch `beta-lambda-cache-optimization`):

```
cd .lake/packages/Blaster && git apply /path/to/d6-dite-motive.patch
```

Rationale, measurements and the soundness-direction argument:
`WSC/pr/03-blaster-d6-FIX.md`. This patch is REQUIRED to reproduce any
global-side result at wsc-poc main @ 2306678 — without it the mint-side shaped
preps and `WSC/Prep/Global1600.lean` fail with a kernel type mismatch.

It lives here because `.lake/` is gitignored, so the working patch would
otherwise vanish with the workspace.

