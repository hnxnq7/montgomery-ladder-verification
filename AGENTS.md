# Code Style

- Do not hard-wrap code to meet a line-length limit. Keep expressions, equations, signatures, and individual proof steps on one line, even when long.
- Put definition bodies on an indented new line after `:=`. Keep short local `let` bindings together.
- Keep structural line breaks between proof steps, branches, local bindings, record fields, and program instructions.
- Comments may wrap. Keep new comments concise and focused on meaning.
- For formatting-only edits, preserve code tokens and comments, and run `bash check.sh` in the configured Rocq environment.
