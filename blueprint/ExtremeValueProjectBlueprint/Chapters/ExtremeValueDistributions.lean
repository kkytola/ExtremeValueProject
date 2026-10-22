import Verso
import VersoManual
import VersoBlueprint
import ExtremeValueProject
import ExtremeValueProjectBlueprint.TeXPrelude

open Verso.Genre Manual Informal

#doc (Manual) "Extreme value distributions" =>

# Definition of extreme value distributions

{bpref "lem:cdf-of-affine-max-many"}[] motivates the following definition.

:::definition "def:extr-val-distr" (lean := "CumulativeDistributionFunction.IsExtremeValueDistr") (uses := "lem:oriented-affine-action-on-cdf")
A c.d.f. $`G` is said to be an _extreme value distribution_ if
$`G` is nondegenerate and
there exists a c.d.f. $`F` and a sequence $`(A_n)_{n \in \N}` of orientation
preserving affine isomorphisms $`A_n \in \OriAffR`, such that
for every continuity point $`x \in \R` of $`G` we have
$$`\lim_{n \to \infty} \big( (A_n.F)(x) \big)^n \; = \; G(x) .`
:::

:::lemma_ "lem:extr-val-distr-transform" (lean := "CumulativeDistributionFunction.IsExtremeValueDistr.affineTransform") (uses := "lem:oriented-affine-action-on-cdf, def:extr-val-distr")
Let $`G` be an extreme value distribution and
and $`A \in \OriAffR` an orientation preserving affine isomorphism.
Then also $`A.G` is an extreme value distribution.
:::

:::proof "lem:extr-val-distr-transform" (uses := "lem:cdf-continuity-pt-transform, lem:degenerate-cdf-transform")
Straightforward using {bpref "lem:cdf-continuity-pt-transform"}[]
and {bpref "lem:degenerate-cdf-transform"}[].
:::

# Three types of extreme value distributions

:::definition "def:std-Gumbel-cdf" (lean := "standardGumbelCDF") (uses := "def:cdf")
_The standard Gumbel distribution_ is the c.d.f. $`\GumbelCDF` given by
$$`\GumbelCDF (x) = \exp\big(-\exp(-x)\big) .`

(In the parametrization of extreme value distribution types by one
index $`\gamma \in \bR`, this case corresponds to $`\gamma = 0`.)
:::

:::definition "def:std-Weibull-cdf" (lean := "standardWeibullCDF") (uses := "def:cdf")
_The standard (reverse) Weibull distribution_ of parameter
$`\alpha > 0` is the c.d.f. $`\WeibullCDF{\alpha}` given by
$$`\begin{aligned}
\WeibullCDF{\alpha} (x) = \begin{cases}
    \exp \big( - (-x)^\alpha \big) \quad & \text{ for } x < 0 \\
    1 \quad & \text{ for } x \ge 0 .
  \end{cases}
\end{aligned}`

(In the parametrization of extreme value distribution types by one
index $`\gamma \in \bR`, this case corresponds to $`\gamma < 0`
via $`\gamma = -1/\alpha`.)
:::

:::definition "def:std-Frechet-cdf" (lean := "standardFrechetCDF") (uses := "def:cdf")
_The standard Fréchet distribution_ of parameter $`\alpha > 0`
is the c.d.f. $`\FrechetCDF{\alpha}` given by
$$`\begin{aligned}
\FrechetCDF{\alpha} (x) = \begin{cases}
  0 \quad & \text{ for } x \le 0 \\
  \exp \big( - x^{-\alpha} \big) \quad & \text{ for } x > 0 .
  \end{cases}
\end{aligned}`

(In the parametrization of extreme value distribution types by one
index $`\gamma \in \bR`, this case corresponds to $`\gamma > 0`
via $`\gamma = 1/\alpha`.)
:::

:::theorem "thm:Gumbel-is-extr-val-distr" (lean := "isExtremeValueDistr_standardGumbelCDF") (uses := "def:std-Gumbel-cdf, def:extr-val-distr")
The standard Gumbel distribution $`\GumbelCDF` is an extreme value
distribution.
:::

:::proof "thm:Gumbel-is-extr-val-distr"
Set $`A_n(x) = x - \log(n)` for $`n \in \bN`. Then
$`A_n^{-1}(x) = x + \log(n)` and for any $`n \ge 1` and $`x \in \bR` we get
$$`\begin{aligned}
\big( (A_n . \GumbelCDF)(x) \big)^n
= \; & \big( \GumbelCDF(x + \log(n)) \big)^n \\
= \; & \Big( \exp \big( - \exp(-(x + \log n)) \big) \Big)^n \\
= \; & \exp \big( - n \exp(-x - \log n) \big) \\
= \; & \exp \big( - n \, e^{-x} \, e^{-\log n}  \big) \\
%= \; & \exp \big( - n \, e^{-x} \, n^{-1} \big) \\
= \; & \exp \big( - e^{-x} \big) \\
= \; & \GumbelCDF(x) .
\end{aligned}`
Since the above is true for each $`n`, we in particular have
$$`\lim_{n \to \infty} \big( (A_n . \GumbelCDF)(x) \big)^n
= \GumbelCDF(x)`
for all $`x \in \bR`. Since $`\GumbelCDF` is also nondegenerate,
this shows that it is an extreme value distribution.
:::

:::theorem "thm:Weibull-is-extr-val-distr" (lean := "isExtremeValueDistr_standardWeibullCDF") (uses := "def:std-Weibull-cdf, def:extr-val-distr")
For any $`\alpha > 0`, the standard Weibull distribution $`\WeibullCDF{\alpha}`
is an extreme value distribution.
:::

:::proof "thm:Weibull-is-extr-val-distr"
…
:::

:::theorem "thm:Frechet-is-extr-val-distr" (lean := "isExtremeValueDistr_standardFrechetCDF") (uses := "def:std-Frechet-cdf, def:extr-val-distr")
For any $`\alpha > 0`, the standard Fréchet distribution $`\FrechetCDF{\alpha}`
is an extreme value distribution.
:::

:::proof "thm:Frechet-is-extr-val-distr"
…
:::

# Equivalent formulations of the limit relation

:::lemma_ "lem:log-ev-limit" (lean := "ev_limit_iff_log_ev_limit") (uses := "def:cdf, lem:oriented-affine-action-on-cdf")
*Logarithmic version of the limit relation*

Let $`F` and $`G` be c.d.f.s, and $`(A_n)_{n \in \N}` a sequence of orientation
preserving affine isomorphisms $`A_n \in \OriAffR`. Then for any $`x \in \bR`
such that $`0 < G(x) < 1`, the two conditions
$$`\begin{aligned}
\text{(i)} & & \lim_{n \to \infty} \big( (A_n.F)(x) \big)^n \, = \; & G(x) \\
\text{(ii)} & & \lim_{n \to \infty} n \, \log F (A_n^{-1}(x)) \, = \; & \log G(x)
\end{aligned}`
are equivalent.
:::

:::proof "lem:log-ev-limit"
Recall that $`(A_n.F)(x) = F (A_n^{-1}(x))`.
Then just take logarithms (and use continuity) to get from (i) to (ii),
and take exponentials (and use continuity) to get from (ii) to (i).
:::

:::lemma_ "lem:ev-limit-cdf-affine-tendsto-one" (lean := "tendsto_one_of_ev_limit") (uses := "def:cdf, lem:oriented-affine-action-on-cdf")
*Relation implies $`F` tending to one*

Let $`F` and $`G` be c.d.f.s, and $`(A_n)_{n \in \N}` a sequence of orientation
preserving affine isomorphisms $`A_n \in \OriAffR`. Then for any $`x \in \bR`
such that $`0 < G(x) < 1`, if
$$`\begin{aligned}
\text{(i)} & & \lim_{n \to \infty} \big( (A_n.F)(x) \big)^n \, = \; & G(x)
\end{aligned}`
holds, then necessarily
$$`\lim_{n \to \infty} F (A_n^{-1}(x)) \; = \; 1 .`
:::

:::proof "lem:ev-limit-cdf-affine-tendsto-one"
Otherwise $`\big( F (A_n^{-1}(x)) \big)^n` would have $`0 \ne G(x)`
as an accumulation point, contradicting the assumed limit (i).

To wit, if for some $`\delta > 0` we would have
$`F (A_n^{-1}(x)) \le 1 - \delta` for infinitely many $`n`, then
$`0 \le \big( F (A_n^{-1}(x)) \big)^n \le (1 - \delta)^n`
for those $`n`, and since $`(1 - \delta)^n \to 0`, we would
get $`\big( F (A_n^{-1}(x)) \big)^n \to 0 \ne G(x)` along the
subsequence of those $`n`; a contradiction.
:::

:::lemma_ "lem:modify-limit-taylor" (lean := "tendsto_smul_apply_smul_deriv_of_tendsto_atTop_of_tendsto_smul_apply_smul_deriv, tendsto_zero_of_tendsto_atTop_of_tendsto_smul")
*Taylor expansion limit modification*

Let $`S \subset \bR` be a subset with $`0 \in S`, and let $`f_1, f_2 \colon S \to \bR` be
functions. Let also $`(t_n)_{n \in \bN}` be a sequence in $`S`,
and let $`(m_n)_{n \in \bR}` be a sequence of real numbers tending to infinity,
$`\lim_{n \to \infty} m_n = +\infty`.
Assume that for $`j = 1,2`

* $`f_j(0)=0`;
* the derivative $`f_j'(0)` exists (derivative taken within the set $`S`)

Assume further about $`j = 1` that

* $`f_1'(0) \ne 0`;
* the limit $`\lim_{n \to \infty} \big( m_n \, f_1 (t_n) \big)` exists;
* for any $`\delta > 0` there exists an $`\eps > 0` such that
  if $`|f_1(t)| < \eps` (with $`t \in S`) then $`|t| < \delta`.

Denote $`c = \frac{1}{f_1'(0)} \, \lim_{n \to \infty} \big( m_n \, f_1 (t_n) \big)`.
Then we have $`\lim_{n \to 0} t_n = 0` and
$$`\begin{aligned}
\lim_{n \to \infty} \Big( m_n \, f_2 (t_n) \Big) \; = \; & c \, f_2'(0) .
\end{aligned}`
:::

:::proof "lem:modify-limit-taylor"
This is in principle straightforward:
the assumptions are first checked to imply that $`\lim_{n \to 0} t_n = 0`,
and then one can just consider the first order Taylor expansions of the
functions $`f_j` at $`0` given by the assumed existence of the derivatives
(the key is $`t_n \, = \, \frac{c}{m_n} + \oo \big(\frac{1}{m_n}\big)`).
:::

:::lemma_ "lem:taylored-ev-limit" (lean := "log_ev_limit_iff_taylored_ev_limit") (uses := "def:cdf, lem:oriented-affine-action-on-cdf")
*Taylored version of the limit relation*

Let $`F` and $`G` be c.d.f.s, and $`(A_n)_{n \in \N}` a sequence of orientation
preserving affine isomorphisms $`A_n \in \OriAffR`. Then for any $`x \in \bR`
such that $`0 < G(x) < 1`, the two conditions
$$`\begin{aligned}
\text{(ii)} & & \lim_{n \to \infty} n \, \log F (A_n^{-1}(x)) \, = \; & \log G(x) \\
\text{(iii)} & & \lim_{n \to \infty} \Big( n \, \big(1 - F (A_n^{-1}(x)) \big) \Big)
  \, = \; & - \log G(x)
\end{aligned}`
are equivalent.
:::

:::proof "lem:taylored-ev-limit" (uses := "lem:modify-limit-taylor")
Both implications (ii) $`\, \Rightarrow \,` (iii) and (iii) $`\, \Rightarrow \,` (ii)
are proven similarly using {bpref "lem:modify-limit-taylor"}[].

Assume (ii). Let $`f_1(t) = - \log (1-t)` and $`f_2(t) = t` and
$`S = [0,1) \subset \bR`, and $`m_n = n` and $`t_n = 1 - F (A_n^{-1}(x))`.
It is straightforward to check the assumptions of {bpref "lem:modify-limit-taylor"}[],
with
$$`\begin{aligned}
f_1'(0) \; = \; & \der{t} \Big|_{t=0} \Big( - \log (1 - t) \Big) \; = \; 1
\end{aligned}`
and $`f_2'(0) = \mathrm{id}'(0) = 1`.
The key assumption about the existence of
the limit $`\lim_{n \to \infty} \big( m_n \, f_1(t_n) \big)` is given by (ii),
and the conclusion is (iii).

Similarly assuming (iii) we derive (ii) with {bpref "lem:modify-limit-taylor"}[]
just interchanging the roles of the two functions, i.e., now using
$`f_1(t) = t` and $`f_2(t) = - \log (1-t)` instead.
:::

:::lemma_ "lem:inv-taylored-ev-limit" (lean := "taylored_ev_limit_iff_oneDivOneSub_limit") (uses := "def:cdf, lem:oriented-affine-action-on-cdf")
*Inverted Taylored version of the limit relation*

Let $`F` and $`G` be c.d.f.s, and $`(A_n)_{n \in \N}` a sequence of orientation
preserving affine isomorphisms $`A_n \in \OriAffR`. Then for any $`x \in \bR`
such that $`0 < G(x) < 1`, the two conditions
$$`\begin{aligned}
\text{(iii)} & & \lim_{n \to \infty} \Big( n \, \big(1 - F (A_n^{-1}(x)) \big) \Big)
  \, = \; & - \log G(x) \\
\text{(iv)} & & \lim_{n \to \infty} \frac{1}{n \, \big(1 - F (A_n^{-1}(x)) \big)}
  \, = \; & \frac{1}{-\log G(x)}
\end{aligned}`
are equivalent.
:::

:::proof "lem:inv-taylored-ev-limit"
By assumption $`G(x) \in (0,1)` we have $`-\log G(x) > 0`.

The implication (iii) $`\,\Rightarrow \,` (iv)
can therefore be seen by applying $`t \mapsto \frac{1}{t}`
and using its continuity at $`t = -\log G(x)`, and the
converse implication (iv) $`\,\Rightarrow \,` (iii) similarly by using continuity of
$`t \mapsto \frac{1}{t}` at $`t = \frac{1}{-\log G(x)}`.
:::

:::lemma_ "lem:transformed-ev-limit" (lean := "oneDivSub_limit_iff") (uses := "def:one-div-one-sub-cdf, def:one-div-neg-log-cdf, lem:oriented-affine-action-on-cdf")
*Transformed version of the limit relation*

Let $`F` and $`G` be c.d.f.s, and $`(A_n)_{n \in \N}` a sequence of orientation
preserving affine isomorphisms $`A_n \in \OriAffR`. Then for any $`x \in \bR`
such that $`0 < G(x) < 1`, the two conditions
$$`\begin{aligned}
\text{(iv)} & & \lim_{n \to \infty} \frac{1}{n \, \big(1 - F (A_n^{-1}(x)) \big)}
  \, = \; & \frac{1}{-\log G(x)} \\
\text{(v)} & & \lim_{n \to \infty} \frac{1}{n} \oneDivOneSub{A_n . F} (x)
  \, = \; & \oneDivNegLog{G} (x)
\end{aligned}`
are equivalent.

(See {bpref "def:one-div-one-sub-cdf"}[]
and {bpref "def:one-div-neg-log-cdf"}[] for the transforms involved in condition (v)).
:::

:::proof "lem:transformed-ev-limit"
This is in principle straightforward, although certain cases need to be checked
separately and the continuity of various natural extensions need to addressed.
:::

```tex
% def:one-div-neg-log-cdf
```

:::theorem "thm:tfae-ev-limit" (lean := "tfae_ev_limit_relation") (uses := "def:one-div-one-sub-cdf, def:one-div-neg-log-cdf, lem:oriented-affine-action-on-cdf")
*Equivalent versions of the limit relation*

Let $`F` and $`G` be c.d.f.s, and $`(A_n)_{n \in \N}` a sequence of orientation
preserving affine isomorphisms $`A_n \in \OriAffR`. Then for any $`x \in \bR`
such that $`0 < G(x) < 1`, the conditions
$$`\begin{aligned}
\text{(i)} & & \lim_{n \to \infty} \big( (A_n.F)(x) \big)^n \, = \; & G(x) \\
\text{(ii)} & & \lim_{n \to \infty} n \, \log F (A_n^{-1}(x)) \, = \; & \log G(x) \\
\text{(iii)} & & \lim_{n \to \infty} \Big( n \, \big(1 - F (A_n^{-1}(x)) \big) \Big)
  \, = \; & - \log G(x) \\
\text{(iv)} & & \lim_{n \to \infty} \frac{1}{n \, \big(1 - F (A_n^{-1}(x)) \big)}
  \, = \; & \frac{1}{-\log G(x)} \\
\text{(v)} & & \lim_{n \to \infty} \frac{1}{n} \oneDivOneSub{A_n . F} (x)
  \, = \; & \oneDivNegLog{G} (x)
\end{aligned}`
are equivalent.

(See {bpref "def:one-div-one-sub-cdf"}[]
and {bpref "def:one-div-neg-log-cdf"}[] for the transforms involved in condition (v)).

_(More equivalent conditions are to be added; this is just a theorem to collect
various equivalent phrasings.)_
:::

:::proof "thm:tfae-ev-limit" (uses := "lem:taylored-ev-limit, lem:log-ev-limit, lem:inv-taylored-ev-limit, lem:transformed-ev-limit")
This is just a combination of earlier results.
:::
