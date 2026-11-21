# Recording who did what

This repository records the contribution of each collaborator explicitly.

- **Commits written by Claude** end with the trailer
  `Co-Authored-By: Claude <model> <noreply@anthropic.com>`, naming the model that made the change, and say in the message body that Claude wrote them.
- **Changes made in response to a ChatGPT review** say so in the commit message, with a short summary of the review points adopted (and any that were not, with the reason).
- **Changes made directly by the author** need no trailer.
- Each new version of the paper adds a "Changes in version N" paragraph, which states the source of the changes (author decision, Claude, or ChatGPT review).
- **[CONTRIBUTIONS_LOG.md](CONTRIBUTIONS_LOG.md)** records every new idea, direction, question and decision as it arises, marked Zeta, Claude or ChatGPT, together with what became of it. Claude adds entries during the work, not only when a paper version is released.
