# Code Style

- Keep short expressions together. Wrap long statements at meaningful boundaries: hypotheses, operands, equality, and argument groups. Aim for roughly 100-120 columns without forcing awkward breaks.
- Format nested functions and `let` bodies as indented blocks; do not flatten them into long lines. Keep an individual function application together when it remains readable.
- Put definition bodies on an indented new line after `:=`. Keep short local `let` bindings together.
- Keep structural line breaks between proof steps, branches, local bindings, record fields, and program instructions.
- Comments may wrap. Keep new comments concise and focused on meaning.
- For formatting-only edits, preserve code tokens and comments, and run `bash check.sh` in the configured Rocq environment.
