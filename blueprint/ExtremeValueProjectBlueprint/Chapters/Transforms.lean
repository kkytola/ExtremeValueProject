import Verso
import VersoManual
import VersoBlueprint
import ExtremeValueProject
import ExtremeValueProjectBlueprint.TeXPrelude

open Verso.Genre Manual Informal

#doc (Manual) "Transforms of cumulative distribution functions" =>

In this part, we introduce certain transforms and extensions of
cumulative distribution functions, which are used in the classification
calculation of the extreme value distributions.

# Extended cumulative distribution function

:::definition "def:cdf-extend" (lean := "CumulativeDistributionFunction.extend") (uses := "def:cdf")
*Extended cumulative distribution function*

The extension $`\extendcdf{F}` of a c.d.f. $`F` is the function
$$`\extendcdf{F} \colon [-\infty,+\infty] \to [0,1]`
given by
$$`\begin{aligned}
\extendcdf{F}(x) = \begin{cases}
  0 & \; \text{ if } x = -\infty \\
  F(x) & \; \text{ if } -\infty < x < +\infty \\
  1 & \; \text{ if } x = +\infty .
  \end{cases}
\end{aligned}`
:::

:::lemma_ "lem:cdf-extend-continuity-pts" (lean := "CumulativeDistributionFunction.extend_continuousAt, CumulativeDistributionFunction.extend_continuousAt_top, CumulativeDistributionFunction.extend_continuousAt_bot") (uses := "def:cdf-extend")
*Continuity points of extended c.d.f.*

The extension $`\extendcdf{F}` of a c.d.f. $`F` is continuous
at $`x = -\infty`, $`x = + \infty`, and at any
$`x \in (-\infty,+\infty)` where $`F` is continuous.
:::

:::proof "lem:cdf-extend-continuity-pts"
Since $`\lim_{x \to +\infty} F(x) = 1` by properties of c.d.f.s
and $`\extendcdf{F}(+\infty) = 1` by definition of the extension,
continuity at $`x = + \infty` follows. Continuity at $`x=-\infty`
is similar.

Suppose $`F` is continuous at $`x \in \bR`.
Then since $`\extendcdf{F}` coincides with $`F`
in a neighborhood of $`x`
(indeed on the open set $`\bR \subsetneq [-\infty,+\infty]`),
the continuity of $`F` at $`x \in \bR` implies
continuity of $`\extendcdf{F}` at $`x`.

```tex
%Let $\iota \colon \bR \to [-\infty,+\infty]$ be the inclusion
%of the real line into the extended real line.
```
:::

# One over one minus cumulative distribution function

:::definition "def:one-div-one-sub-cdf" (lean := "CumulativeDistributionFunction.oneDivOneSub") (uses := "def:cdf-extend")
*One over one minus cumulative distribution function*

The transform $`\oneDivOneSub{F}` of a c.d.f. $`F` is the function
$$`\oneDivOneSub{F} \colon [-\infty,+\infty] \to [1,+\infty]`
given by
$$`\begin{aligned}
\oneDivOneSub{F}(x) = \begin{cases}
  1 & \; \text{ if } \extendcdf{F}(x) = 0 \\
  \frac{1}{1-\extendcdf{F}(x)} & \; \text{ if } 0 < \extendcdf{F}(x) < 1 \\
  +\infty & \; \text{ if } \extendcdf{F}(x) = 1 ,
  \end{cases}
\end{aligned}`
where $`\extendcdf{F} \colon [-\infty,+\infty] \to [0,1]` is the extension of the c.d.f. $`F`.
:::

:::lemma_ "lem:one-div-one-sub-cdf-continuity-pts" (lean := "CumulativeDistributionFunction.oneDivOneSub_continuousAt, CumulativeDistributionFunction.oneDivOneSub_continuousAt_top, CumulativeDistributionFunction.oneDivOneSub_continuousAt_bot") (uses := "def:one-div-one-sub-cdf")
*Continuity points of one over one minus c.d.f.*

The transform $`\oneDivOneSub{F}` of a c.d.f. $`F` is continuous
at $`x = -\infty`, $`x = + \infty`, and at any
$`x \in (-\infty,+\infty)` where $`F` is continuous.
:::

:::proof "lem:one-div-one-sub-cdf-continuity-pts" (uses := "lem:cdf-extend-continuity-pts")
Since $`\lim_{x \to +\infty} \extendcdf{F}(x) = \extendcdf{F}(+\infty) = 1`
by {bpref "lem:cdf-extend-continuity-pts"}[] and the continuous extension
of $`p \mapsto \frac{1}{1-p}` to a function $`[0,1] \to [0,+\infty]`
tends to $`+\infty` as $`p \to 1`, we have
$$`\lim_{x \to +\infty} \oneDivOneSub{F}(x)
\; = \; +\infty \; = \; \oneDivOneSub{F}(+\infty) .`
Therefore $`\oneDivOneSub{F}` is continuous at $`+\infty`.
Continuity at $`-\infty` similarly follows from
$`\lim_{x \to -\infty} \extendcdf{F}(x) = \extendcdf{F}(-\infty) = 0`
and $`\frac{1}{1-p}` tending to $`1`
as $`p \to 0`, which give
$$`\lim_{x \to -\infty} \oneDivOneSub{F}(x)
\; = \; 1 \; = \; \oneDivOneSub{F}(-\infty) .`

Suppose $`F` is continuous at $`x \in \bR`,
and recall from {bpref "lem:cdf-extend-continuity-pts"}[] that
$`\extendcdf{F}` is then also continuous at $`x`.
Now $`\oneDivOneSub{F}` is a composition of the continuous function
$`p \mapsto \frac{1}{1-p} \colon [0,1] \to [0,+\infty]` with
$`\extendcdf{F}`, and as such also becomes continuous at $`x`.
:::

# One over negative logarithm cumulative distribution function

:::definition "def:one-div-neg-log-cdf" (lean := "CumulativeDistributionFunction.oneDivNegLog") (uses := "def:cdf-extend")
*One over negative logarithm cumulative distribution function*

The transform $`\oneDivNegLog{F}` of a c.d.f. $`F` is the function
$$`\oneDivNegLog{F} \colon [-\infty,+\infty] \to [0,+\infty]`
given by
$$`\begin{aligned}
\oneDivNegLog{F}(x) = \begin{cases}
  0 & \; \text{ if } \extendcdf{F}(x) = 0 \\
  \frac{1}{\log \big( 1/\extendcdf{F}(x) \big)} & \; \text{ if } 0 < \extendcdf{F}(x) < 1 \\
  +\infty & \; \text{ if } \extendcdf{F}(x) = 1 ,
  \end{cases}
\end{aligned}`
where $`\extendcdf{F} \colon [-\infty,+\infty] \to [0,1]` is the extension of the c.d.f. $`F`.
:::

:::lemma_ "lem:one-div-neg-log-cdf-continuity-pts" (lean := "CumulativeDistributionFunction.oneDivNegLog_continuousAt, CumulativeDistributionFunction.oneDivNegLog_continuousAt_top, CumulativeDistributionFunction.oneDivNegLog_continuousAt_bot") (uses := "def:one-div-neg-log-cdf")
*Continuity points of one over negative logarithm c.d.f.*

The transform $`\oneDivNegLog{F}` of a c.d.f. $`F` is continuous
at $`x = -\infty`, $`x = + \infty`, and at any
$`x \in (-\infty,+\infty)` where $`F` is continuous.
:::

:::proof "lem:one-div-neg-log-cdf-continuity-pts" (uses := "lem:cdf-extend-continuity-pts")
Since $`\lim_{x \to +\infty} \extendcdf{F}(x) = \extendcdf{F}(+\infty) = 1`
by {bpref "lem:cdf-extend-continuity-pts"}[] and the continuous extension
of $`p \mapsto \frac{1}{\log(1/p)}` to a function $`[0,1] \to [0,+\infty]`
tends to $`+\infty` as $`p \to 1`, we have
$$`\lim_{x \to +\infty} \oneDivNegLog{F}(x)
\; = \; +\infty \; = \; \oneDivNegLog{F}(+\infty) .`
Therefore $`\oneDivNegLog{F}` is continuous at $`+\infty`.
Continuity at $`-\infty` similarly follows from
$`\lim_{x \to -\infty} \extendcdf{F}(x) = \extendcdf{F}(-\infty) = 0`
and $`\frac{1}{\log(1/p)}` tending to $`0`
as $`p \to 0`, which give
$$`\lim_{x \to -\infty} \oneDivNegLog{F}(x)
\; = \; 0 \; = \; \oneDivNegLog{F}(-\infty) .`

Suppose $`F` is continuous at $`x \in \bR`,
and recall from {bpref "lem:cdf-extend-continuity-pts"}[] that
$`\extendcdf{F}` is then also continuous at $`x`.
Now $`\oneDivNegLog{F}` is a composition of the continuous function
$`p \mapsto \frac{1}{\log(1/p)} \colon [0,1] \to [0,+\infty]` with
$`\extendcdf{F}`, and as such also becomes continuous at $`x`.
:::
