import Verso
import VersoManual
import VersoBlueprint
import ExtremeValueProject
import ExtremeValueProjectBlueprint.TeXPrelude

open Verso.Genre Manual Informal

#doc (Manual) "Convergence in distribution with cdfs" =>

This chapter provides a standard characterization of convergence in distribution
(weak convergence of probability measures) on the real line in terms of
cumulative distribution functions.

# Convergence in distribution

Convergence in distribution for random variables can be defined when the random variables
take values in a topological space, and it amounts to the weak convergence of the
probability measures that are the laws of those random variables. In the special case
of real-valued random variables, or probability measures on the real line, the definition
reads:

:::definition "def:convergence-in-distribution" (lean := "MeasureTheory.ProbabilityMeasure.instTopologicalSpace, MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto")
*Weak convergence of probability measures*

A sequence $`(\PRmeas_n)_{n \in \bN}` of Borel probability measures on $`\bR` converges
weakly to a Borel probability measure $`\PRmeas` on $`\bR` if for all bounded continuous
functions $`f \colon \bR \to [0,+\infty)` we have
$$`\lim_{n \to \infty} \int_{\bR} f(x) \, \ud \PRmeas_n(x)
= \int_{\bR} f(x) \, \ud \PRmeas(x) .`
:::

# Auxiliary results

:::lemma_ "lem:monotone-discontinuities-countable" (lean := "Set.Countable.dense_compl, Monotone.countable_not_continuousAt")
*Monotone real functions have only countably many points of discontinuity*

A monotone function $`f \colon \bR \to \bR` can have at most countably
many points of discontinuity. In particular the set $`D \subset \bR`
of continuity points of $`f` is dense in $`\bR`.
:::

:::proof "lem:monotone-discontinuities-countable"
(The proof should already be in Mathlib.)
:::

:::lemma_ "lem:cdf-tight" (lean := "CumulativeDistributionFunction.forall_pos_exists_lt_gt_continuousAt") (uses := "def:cdf")
*Tightness of a cumulative distribution function*

Let $`F` be a cumulative distribution function. Then for any
$`\eps > 0` there exists points $`a,b \in \bR` with $`a < b` such that
$`F(b) - F(a) > 1 - \eps` and $`F` is continuous at the points $`a` and $`b`.
:::

:::proof "lem:cdf-tight" (uses := "def:cdf, lem:monotone-discontinuities-countable")
Cumulative distribution functions satisfy
$`F(x) \downarrow 0` as $`x \downarrow - \infty` and
$`F(x) \uparrow 1` as $`x \uparrow + \infty`. The
required large difference $`F(b) - F(a)` is
obtained by choosing $`a` small enough so that $`F(a) < \frac{\eps}{2}`
and $`b` large enough so that $`F(b) > 1 - \frac{\eps}{2}`.
In order to guarantee that $`a < b` and
that $`a` and $`b` are continuity points of $`F`, we
recall that continuity points of the monotone function $`F` are dense
by {bpref "lem:monotone-discontinuities-countable"}[], so we
may decrease $`a` and increase $`b` as appropriate.
:::

:::lemma_ "lem:subdivision-dense" (lean := "forall_exists_subdivision_diff_lt_of_dense")
*Subdivision with small mesh and within dense set*

Let $`D \subset \bR` be a dense set and $`a,b \in D` with $`a < b`.
Then for any $`\delta > 0` there exists a $`k \in \bN`
and $`a = c_0, c_1, \ldots, c_{k-1}, c_k = b \in D` such that
$`|c_j - c_{j-1}| < \delta` for all $`j=1,\ldots,k`.
:::

:::proof "lem:subdivision-dense"
…
:::

:::lemma_ "lem:continuous-function-approximation-subdivision" (lean := "forall_exists_subdivision_dist_apply_lt_of_dense_of_continuous")
*Subdivision for continuous function approximation*

Let $`D \subset \bR` be a dense set, let $`f \colon \bR \to \bR` be continuous,
let $`a, b \in D` with $`a < b`, and let $`\eps > 0`.
Then there exists a $`k \in \bN` and points
$`a=c_0 < c_1 < \cdots < c_{k-1} < c_k = b` such that for
each $`j = 1, \ldots, k` we have $`c_j \in D` and
$$`\big| f(x) - f(c_j) \big| < \eps
\qquad \text{ for } \qquad x \in [c_{j-1} , c_j] .`
:::

:::proof "lem:continuous-function-approximation-subdivision" (uses := "lem:subdivision-dense")
On the compact interval
$`[a,b] \subset \bR`, the continuous function $`f` is uniformly continuous, so for some
$`\delta > 0` we have $`|f(x)-f(y)|<\eps` whenever $`|x-y|<\delta` and $`x,y \in
[a,b]`.
Now apply {bpref "lem:subdivision-dense"}[] to choose $`k` and points
$`a=c_0 < c_1 < \cdots < c_{k-1} < c_k` such that $`c_j - c_{j-1} < \delta`
and $`c_j \in D` for all $`j = 1 , \ldots , k`.
Now for any $`j = 1 , \ldots , k`, since for $`x \in [c_{j-1} , c_j]` we have
$`|x - c_j| < \delta`, we get
$$`\big| f(x) - f(c_j) \big| < \eps`
as desired.
:::

:::lemma_ "lem:simple-integral-cdf-difference" (lean := "CumulativeDistributionFunction.integral_sum_indicator_eq") (uses := "def:cdf")
*Simple function integral as linear combination of cdf differences*

Let $`a = c_0 < c_1 < \cdots < c_k = b` and consider the
linear combination of indicator functions
$$`h(x) = \sum_{j=1}^k \alpha_j \; \indof{(c_{j-1},c_j]}(x) .`
Then the integral of $`h` with respect to a Borel probability measure $`\PRmeas` on $`\bR` whose
can be written as
$$`\int_{\bR} h(x) \, \ud \PRmeas (x) = \sum_{j=1}^k \alpha_j \, \big( F(c_j) - F(c_{j-1}) \big) ,`
where $`F` is the c.d.f. of $`\PRmeas`.
:::

:::proof "lem:simple-integral-cdf-difference"
$$`\begin{aligned}
\int_{\bR} h \, \ud \PRmeas
 = \; & \int_{\bR}
        \Big( \sum_{j=1}^k \alpha_j \, \indof{(c_{j-1},c_j]}(x) \Big) \, \ud \PRmeas(x) \\
 = \; & \sum_{j=1}^k \alpha_j \; \int_{\bR} \indof{(c_{j-1},c_j]}(x) \, \ud \PRmeas(x) \\
 = \; & \sum_{j=1}^k \alpha_j \; \PRmeas \big[ (c_{j-1},c_j] \big] \\
 = \; & \sum_{j=1}^k \alpha_j \, \big( F_n(c_j) - F_n(c_{j-1}) \big)
\end{aligned}`
:::

:::lemma_ "lem:portmanteau-convergence-for-borel" (lean := "MeasureTheory.ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto', MeasureTheory.ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto") (uses := "def:convergence-in-distribution")
*One of the portmanteau implications*

Weak convergence of probability measures implies that if the boundary of a Borel set carries
no probability mass under the limit measure, then the limit of the measures of the set equals
the measure of the set under the limit probability measure.

In other words, if $`\lim_{n \to \infty} \PRmeas_n = \PRmeas` in the sense of weak convergence
of measures, {bpref "def:convergence-in-distribution"}[], and if $`A \subset \bR`
is a Borel set such that $`\PRmeas[\partial A] = 0`, then
$$`\lim_{n \to \infty} \PRmeas_n [ A ] = \PRmeas [ A ] .`
:::

:::proof "lem:portmanteau-convergence-for-borel"
(The proof is in Mathlib.)
:::

# Convergence in distribution from pointwise convergence of cdfs

:::theorem "thm:convergence-in-distribution-with-cdf" (lean := "tendsto_of_forall_continuousAt_tendsto_cdf") (uses := "def:convergence-in-distribution, def:cdf")
*Sufficient condition for convergence in distribution with cdfs*

Let $`F` and $`F_n`, $`n \in \bN`, be cumulative distribution functions of
probability measures $`\PRmeas` and $`\PRmeas_n`, $`n \in \bN`, respectively, i.e.,
$$`\begin{aligned}
F(x) = \; & \PRmeas \big[(-\infty,x]\big] & & \text{for $x \in \bR$} \\
F_n(x) = \; & \PRmeas_n \big[(-\infty,x]\big] & & \text{for $x \in \bR$ and $n \in \bN$.}
\end{aligned}`
If $`\lim_{n \to \infty} F_n(x) = F(x)` for all continuity points $`x` of $`F`,
then $`\lim_{n \to \infty} \PRmeas_n = \PRmeas` in the sense of weak convergence
of measures, {bpref "def:convergence-in-distribution"}[].
:::

:::proof "thm:convergence-in-distribution-with-cdf" (uses := "lem:monotone-discontinuities-countable, lem:cdf-tight, lem:continuous-function-approximation-subdivision, lem:simple-integral-cdf-difference")
Let $`D \subset \bR` denote the set of continuity points of $`F`. By
{bpref "lem:monotone-discontinuities-countable"}[], $`D` is dense in $`\bR`.
Assume that $`\lim_{n \to \infty} F_n(x) = F(x)` for all $`x \in D`.

Let $`\eps > 0`. Choose, by {bpref "lem:cdf-tight"}[], points
$`a,b \in D`, $`a<b`, such that $`F(b) - F(a) > 1 - \eps`.

Observe also that since $`\lim_{n \to \infty} F_n(a) = F(a)`
and $`\lim_{n \to \infty} F_n(b) = F(b)`, there exists some $`N_1` such that
we have
$$`F_n(b) - F_n(a) > 1 - 2\eps \qquad \text{ for all } n \geq N_1 .`

Let $`f \colon \bR \to \bR` be bounded and continuous.
By {bpref "lem:continuous-function-approximation-subdivision"}[]
we can choose points
$`a=c_0 < c_1 < \cdots < c_{k-1} < c_k = b` such that
for all $`j = 1 , \ldots , k` we have $`c_j \in D` and
$$`\big| f(x) - f(c_j) \big| < \eps
\qquad \text{ for } \qquad x \in [c_{j-1} , c_j] .`
Define the simple function $`h \colon \bR \to \bR` by
$$`h(x) = \sum_{j=1}^k f(c_j) \; \indof{(c_{j-1},c_j]}(x)`
The above estimate shows that $`|f(x) - h(x)| < \eps` for all $`x \in [a,b]`.
By boundedness of $`f`, there exists a constant $`K>0` such that $`|f(x)| \leq K`
for all $`x \in \bR`. Since $`h` vanishes outside $`(a,b]`,
the triangle inequality for integral with respect to $`\PRmeas_n` gives
$$`\begin{aligned}
\Big| \int_{\bR} f \, \ud \PRmeas_n - \int_{\bR} h \, \ud \PRmeas_n \Big|
\, \leq \; & \, \underbrace{\int_{(a,b]} |f-h| \, \ud \PRmeas_n}_{\leq \eps}
    + \underbrace{\int_{\bR \setminus (a,b]} |f| \, \ud \PRmeas_n}_{%
    \leq K \, \PRmeas_n\big[ \bR \setminus (a,b] \big]} .
\end{aligned}`
When $`n \geq N_1`, we have
$`\PRmeas_n\big[ \bR \setminus (a,b] \big]
= 1 - \PRmeas_n\big[ (a,b] \big] = 1 - (F_n(b) - F_n(a)) < 2 \eps`,
and thus the triangle inequality implies
$$`\begin{aligned}
\Big| \int_{\bR} f \, \ud \PRmeas_n - \int_{\bR} h \, \ud \PRmeas_n \Big|
\, \leq \; & \eps + K \, 2 \eps = (1 + 2K) \, \eps .
\end{aligned}`
Similarly, integrating now with respect to $`\PRmeas` instead, one shows that
$$`\begin{aligned}
\Big| \int_{\bR} f \, \ud \PRmeas - \int_{\bR} h \, \ud \PRmeas \Big|
\, \leq \; & (1 + K) \, \eps .
\end{aligned}`
It remains to consider the integrals of the function $`h` with respect to both
$`\PRmeas_n` and $`\PRmeas`. By {bpref "lem:simple-integral-cdf-difference"}[],
these integrals are expressible in terms of the cumulative distribution functions,
$$`\begin{aligned}
\int_{\bR} h \, \ud \PRmeas_n
= \; & \sum_{j=1}^k f(c_j) \, \big( F_n(c_j) - F_n(c_{j-1}) \big)
\end{aligned}`
and
$$`\begin{aligned}
\int_{\bR} h \, \ud \PRmeas
% = \; & \sum_{j=1}^k f(c_j) \; \PRmeas_n \big[ (c_{j-1},c_j] \big]
%      \\
= \; & \sum_{j=1}^k f(c_j) \, \big( F(c_j) - F(c_{j-1}) \big) .
\end{aligned}`
The difference of the integrals of $`h` with respect to these two can
therefore be estimated as
$$`\begin{aligned}
\Big| \int_{\bR} h \, \ud \PRmeas - \int_{\bR} h \, \ud \PRmeas_n \Big|
\, = \; & \, \Big| \sum_{j=1}^k f(c_j) \,
    \big( F(c_j) - F_n(c_j) - F(c_{j-1}) +  F_n (c_{j-1}) \big) \Big| \\
\leq \; & \, \sum_{j=1}^k |f(c_j)| \; \Big(
    \big| F(c_j) - F_n(c_j) \big| + \big| F(c_{j-1}) +  F_n (c_{j-1}) \big|
    \Big) \\
\leq \; & \, 2 k K \max_{j = 0 , \ldots , k} \big| F(c_j) - F_n(c_j) \big| .
\end{aligned}`
By our assumption (ii), we have
$`\lim_{n \to \infty} F_n(c_j) = F(c_j)` for each $`j = 1 , \ldots, k`, so
there exists $`N_2` such that for $`n \geq N_2` we have
$`\max_{j = 1 , \ldots , k} | F(c_j) - F_n(c_j) | < \frac{\eps}{k}`, and
thus
$$`\begin{aligned}
\Big| \int_{\bR} h \, \ud \PRmeas - \int_{\bR} h \, \ud \PRmeas_n \Big|
\leq \; & \, 2 K \eps .
\end{aligned}`
Combining the estimates we have obtained, for $`n \geq \max(N_1 , N_2)`, we have
$$`\begin{aligned}
& \Big| \int_{\bR} f \, \ud \PRmeas - \int_{\bR} f \, \ud \PRmeas_n \Big| \\
\leq \; \, &
    \underbrace{
    \Big| \int_{\bR} f \, \ud \PRmeas - \int_{\bR} h \, \ud \PRmeas \Big|}_{
        \leq (1+K) \eps}
    + \underbrace{
    \Big| \int_{\bR} h \, \ud \PRmeas - \int_{\bR} h \, \ud \PRmeas_n \Big|}_{
        \leq 2 K \eps}
    + \underbrace{
    \Big| \int_{\bR} h \, \ud \PRmeas_n - \int_{\bR} f \, \ud \PRmeas_n	\Big|}_{
        \leq (1+2K) \eps } \\
\leq \; \, & (2 + 5 K) \eps .
\end{aligned}`
Since $`\eps > 0` was arbitrary, this shows that
$`\int f \, \ud \PRmeas_n \to \int f \, \ud \PRmeas` as $`n \to \infty`, so we
have established the weak convergence $`\PRmeas_n \to \PRmeas`
according to {bpref "def:convergence-in-distribution"}[].
:::

:::lemma_ "lem:cdf-convergence-from-convergence-in-distribution" (lean := "CumulativeDistributionFunction.tendsto_apply_of_tendsto_of_continuousAt") (uses := "def:convergence-in-distribution, def:cdf")
*Necessary condition for convergence in distribution with cdfs*

Let $`\PRmeas` and $`\PRmeas_n`, $`n \in \bN`, be Borel
probability measures on $`\bR`, and let $`F` and $`F_n`, $`n \in \bN`,
be their cumulative distribution functions, respectively, i.e.,
$$`\begin{aligned}
F(x) = \; & \PRmeas \big[(-\infty,x]\big] & & \text{for $x \in \bR$} \\
F_n(x) = \; & \PRmeas_n \big[(-\infty,x]\big] & & \text{for $x \in \bR$ and $n \in \bN$.}
\end{aligned}`
If $`\lim_{n \to \infty} \PRmeas_n = \PRmeas` in the sense of weak convergence
of measures, {bpref "def:convergence-in-distribution"}[], then
for all continuity points $`x` of $`F` we have
$`\lim_{n \to \infty} F_n(x) = F(x)`.
:::

:::proof "lem:cdf-convergence-from-convergence-in-distribution" (uses := "lem:cdf-continuity-pt-iff-measure-singleton, lem:portmanteau-convergence-for-borel")
Let $`x \in \bR` be a continuity point of $`F`. Then we have $`\mu [\set{x}] = 0`,
by {bpref "lem:cdf-continuity-pt-iff-measure-singleton"}[].
Note that the boundary of the Borel set $`(-\infty,x] \subset \bR` is
the singleton $`\partial (-\infty,x] = \set{x}`.
Therefore the assumption $`\lim_{n \to \infty} \PRmeas_n = \PRmeas` implies that
$$`\PRmeas_n \big[ (-\infty,x] \big] \to \PRmeas \big[ (-\infty,x] \big] ,`
by a general fact ({bpref "lem:portmanteau-convergence-for-borel"}[])
about weakly converging sequences of measures
that a for Borel sets whose boundary carries no mass in the limit measure.
In terms of the c.d.f.s, the above reads
$$`F_n(x) \to F(x)`
as asserted.
:::
