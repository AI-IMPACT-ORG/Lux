# Copyright Notice Templates

This file provides templates for adding copyright notices to different types of files in the repository.

## General Copyright Notice
© 2025 AI.IMPACT GmbH

## File-Specific Templates

### Racket Files (.rkt)
```racket
#lang racket
# © 2025 AI.IMPACT GmbH

; Your code here
```

### Agda Files (.agda)
```agda
-- © 2025 AI.IMPACT GmbH

module YourModule where
-- Your code here
```

### Coq Files (.v)
```coq
(* © 2025 AI.IMPACT GmbH *)

Require Import Coq.Lists.List.
(* Your code here *)
```

### Isabelle Files (.thy)
```isabelle
(* © 2025 AI.IMPACT GmbH *)

theory YourTheory
imports Main
begin
(* Your code here *)
end
```

### Shell Scripts (.sh, .bash)
```bash
#!/bin/bash
# © 2025 AI.IMPACT GmbH

# Your script here
```

### Makefiles
```makefile
# © 2025 AI.IMPACT GmbH

# Your makefile content here
```

### LaTeX Files (.tex)
```latex
% © 2025 AI.IMPACT GmbH

\documentclass{article}
% Your LaTeX content here
```

### Markdown Files (.md)
```markdown
<!-- (c) 2025 AI.IMPACT GmbH. Licensed under CC BY-NC-ND 4.0. Provided "as is" without warranties. No patent rights granted. Not for safety-critical use. -->

# Your Document Title
```

### JSON Files (.json)
```json
{
  "_copyright": "© 2025 AI.IMPACT GmbH",
  // Your JSON content here
}
```

### YAML Files (.yml, .yaml)
```yaml
# © 2025 AI.IMPACT GmbH

# Your YAML content here
```

## Notes
- The copyright notice should be placed at the top of each file
- Use the appropriate comment syntax for each file type
- The hook will check for the exact text "© 2025 AI.IMPACT GmbH"
- Some file types (images, binaries, etc.) are automatically excluded from the check
