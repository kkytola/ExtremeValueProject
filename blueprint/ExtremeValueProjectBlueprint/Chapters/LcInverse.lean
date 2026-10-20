import Verso
import VersoManual
import VersoBlueprint
import ExtremeValueProject
import ExtremeValueProjectBlueprint.TeXPrelude

open Verso.Genre Manual Informal

#doc (Manual) "Left-continuous inverses" =>

Let $`R` and $`S` be complete linear orders, for example $`[0,1]`, $`[0,+\infty]`, or
$`[-\infty,+\infty] =: \overline{\bR}`.

:::definition "def:lc-inverse" (lean := "lcInv")
Let $`f \colon R \to S` be a function (usually assumed nondecreasing).
The left-continuous inverse of $`f` is the function $`\lcinv{f} \colon S \to R`
given by
$$`\lcinv{f}(y) := \inf \big\{ x \in R \; \big| \; f(x) \ge y \big\}
\qquad \text{ for } y \in S.`
The right-continuous inverse $`\rcinv{f} \colon S \to R` is analoguously defined by
$$`\rcinv{f}(y) := \sup \big\{ x \in R \; \big| \; f(x) \le y \big\}
\qquad \text{ for } y \in S.`
:::
