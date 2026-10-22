import Verso
import VersoManual
import VersoBlueprint
import ExtremeValueProject
import ExtremeValueProjectBlueprint.TeXPrelude

open Verso.Genre Manual Informal

#doc (Manual) "Cauchy-Hamel functional equation" =>

# Positive measure additive subgroups of the reals

:::lemma_ "lem:countably-many-connected-components-of-open" (lean := "IsOpen.countable_setOf_connectedComponentIn")
*Countably many connected components for an open set*

Let $`X` be a locally connected separable space. Then any open subset $`U \subseteq X` has at
most countably many connected components.
:::

:::proof "lem:countably-many-connected-components-of-open"
(The proof is already formalized, see:
`IsOpen.countable-setOf-connectedComponentIn`.)
:::

For subsets $`A, B \subseteq \bR`, we use the following notation for pointwise
sum sets and difference sets:
$$`\begin{aligned}
A + B & = \set{ a + b \; \big| \; a \in A, \, b \in B } , \\
A - B & = \set{ a - b \; \big| \; a \in A, \, b \in B } .
\end{aligned}`

We denote by $`\Leb` the Lebesgue measure on $`\bR`.

:::lemma_ "lem:exists-high-overlap-interval" (lean := "exists_interval_measure_inter_gt_mul_measure")
*Finding an interval with high overlap*

Let $`A \subset \bR` be a measurable set such that $`0 < \Leb[A] < +\infty`.
Then for any $`r \in [0,1)`, there exists a nontrivial interval $`J \subset \bR`
(a subset of the real line which is connected and has nonempty interior)
such that
$$`\Leb[A \cap J] \; > \; r \, \Leb[J] .`
:::

:::proof "lem:exists-high-overlap-interval"
Assume, without loss of generality, $`0 < r < 1`.
Since the Lebesgue measure is outer regular, we can find an open set $`U \subset \bR`
such that $`A \subseteq U` and $`\Leb[U] < r^{-1} \, \Leb[A]`.

The open set $`U` has at most countably many connected components
(which are in fact open intervals); denote
by $`(U_i)_{i \in I}` the indexed collection of them.

Note that for at least one index $`j \in I` we
have $`\Leb[A \cap U_j] > r \Leb[U_j]`,
because otherwise we get
$$`\begin{aligned}
\Leb[A] = \Leb[A \cap U]
= \, & \sum_{i \in I} \Leb[A \cap U_i] \\
\le \, & r \sum_{i \in I} \Leb[U_i] \\
= \, & r \Leb[U],
\end{aligned}`
contradicting the choice of $`U`.

Now $`J = U_j` has the desired properties.
:::

:::lemma_ "lem:shift-interval-contained-in-larger"
*Shifts of a smaller interval contained in a larger interval*

```tex
%
%
%  % needs also `isPreconnected_of_Ioo_subset_of_subset_Icc` etc. before really done
```

Let $`I, J` be nontrivial intervals, whose length satisfy
$$`0 \; < \; \Leb[J] \; < \; \Leb[I] \; < \, +\infty .`
Then there exists an open interval $`\Delta` of length
$`\Leb[\Delta] = \Leb[I] - \Leb[J] > 0` such that
$$`t + J \; \subset \; I
\qquad \text{ for any $t \in \Delta$.}`
:::

:::proof "lem:shift-interval-contained-in-larger"
…
:::

:::lemma_ "lem:overlapping-union-interval-copies" (lean := "volume_union_add_self_ge_of_Ioo_subset, volume_union_add_self_le_of_subset_Icc, isConnected_of_Ioo_subset_of_subset_Icc")
*Overlapping union of copies of an interval*

```tex
%  % needs also `isPreconnected_of_Ioo_subset_of_subset_Icc` etc. before really done
```

Let $`J` be a nontrivial interval of finite length ($`0 \, < \, \Leb[J] \, < +\infty`).
Let $`c < 1` and denote $`\delta = c \Leb[J] \, < \, \Leb[J]`.
Then for any $`t \in (-\delta,\delta)`, the set
$`J' = (t+J) \cup J` is an interval (connected set with nonempty interior)
whose length satisfies the bound $`\Leb[J'] \, < \, (1+c) \, \Leb[J]`.
:::

:::proof "lem:overlapping-union-interval-copies" (uses := "lem:shift-interval-contained-in-larger")
Denote $`a = \inf J` and $`b = \sup J`. We have $`-\infty < a < b < +\infty` and
$$`(a,b) \; \subseteq \; J \; \subseteq \; [a,b]`
and we have $`\Leb[J] = b - a`.

Let $`t \in (+\delta,\delta)`, with $`\delta = c \, \Leb[J] = c(b-a)`.
Then we have the containments
$$`\big( \min \{a,a+t\} , \max \{b,b+t\} \big)
  \; \subseteq \; (t+J) \cup J
  \; \subseteq \; \big[ \min \{a,a+t\} , \max \{b,b+t\} \big] .`
It in particular follows that $`J' := (t+J) \cup J` is an interval.

If $`t \ge 0`, then $`J'` is contained in
$`[a,b+t]` which has length $`b+t-a = (b-a) + t < \Leb[J] + c \, \Leb[J] = (1+c) \Leb[J]`.
If $`t < 0`, then $`J'` is contained in $`[a+t,b]` and one similarly gets a length bound.
:::

:::lemma_ "lem:difference-set-contains-interval" (lean := "exists_Ioo_subset_diff_self_of_measure_pos")
*Difference set of positive measure set contains an interval*

Let $`A \subset \bR` be a measurable set of positive Lebesgue measure.
Then there exists a $`\delta > 0` such that
$$`(-\delta,\delta) \, \subseteq \, A - A .`
:::

:::proof "lem:difference-set-contains-interval" (uses := "lem:countably-many-connected-components-of-open, lem:exists-high-overlap-interval, lem:overlapping-union-interval-copies")
Pick a measurable subset $`A_0 \subseteq A` such that
$`0 < \Leb[A_0] < +\infty`.

By {bpref "lem:exists-high-overlap-interval"}[], we can find a nontrivial interval $`J`
such that $`\Leb[A_0 \cap J] > \frac{3}{4} \Leb[J]`.
Let $`\delta = \frac{1}{2} \Leb[J]`.
We claim that $`(-\delta,\delta) \subseteq A_0 - A_0` (which then
clearly implies the assertion of the lemma).
Indeed, suppose $`t \in (-\delta,\delta)`.
Then by {bpref "lem:overlapping-union-interval-copies"}[],
$`(t+J) \cup J` is an interval of length less than $`\frac{3}{2} \Leb[J]`.
Moreover, we have $`A_0 \cap J \subseteq (t+J) \cup J` and
$`t+(A_0 \cap J) \subseteq (t+J) \cup J`. Now note that
$$`\Leb[t + (A_0 \cap J)] = \Leb[A_0 \cap J] > \frac{3}{4} \Leb[J] .`
If the sets $`t + (A_0 \cap J)` and $`(A_0 \cap J)` were disjoint, then
the measure of $`(A_0 \cap J) \cup (t+(A_0 \cap J))` would thus be
greater than $`\frac{3}{2} \Leb[J]`, which is impossible given the length
of the interval $`(t+J) \cup J` is less than $`\frac{3}{2} \Leb[J]`.
Therefore there exists a point $`a \in (t + (A_0 \cap J)) \cap (A_0 \cap J)`.
Denoting $`a' = a - t`, we have $`a, a' \in A_0 \cap J \subseteq A_0`
and $`t = a - a' \in A_0 - A_0 \subseteq A - A`. Since $`t \in (-\delta,\delta)`
was arbitrary, this proves the assertion.
:::

:::lemma_ "lem:dividing-high-operlap-interval"
*Dividing a high overlap interval*

Let $`A` be a measurable. Suppose that for some $`a < b`,
the interval $`J = (a,b)` satisfies
$`\Leb[A \cap J] \; > \;  r \, \Leb[J]`.
Let $`m \in \Npos`, and consider the subintervals
$$`J_i = \Big( a + \frac{i}{(b-a)m} , \; a + \frac{i+1}{(b-a)m} \Big)
\qquad \text{ for $i = 0, \ldots, m-1$.}`
Then for some $`i` we have $`\Leb[A \cap J_i] \; > \;  r \, \Leb[J_i]`.
:::

:::proof "lem:dividing-high-operlap-interval"

:::

:::lemma_ "lem:different-difference-set-contains-interval"
*Difference of two positive measure sets contains an interval*

Let $`A, B \subset \bR` be two measurable sets of positive Lebesgue measure.
Then the difference set $`A - B` contains a nontrivial open interval.

```tex
%\begin{align*}
%  (-\delta,\delta) \, \subseteq \, A - B .
%\end{align*}
```
:::

:::proof "lem:different-difference-set-contains-interval" (uses := "lem:dividing-high-operlap-interval")
Pick measurable subsets $`A_0 \subseteq A` and $`B_0 \subseteq B` such that
$`0 < \Leb[A_0] < +\infty` and $`0 < \Leb[B_0] < +\infty`.

By {bpref "lem:exists-high-overlap-interval"}[], we can find nontrivial intervals $`J, I`
such that $`\Leb[A_0 \cap J] > \frac{3}{4} \Leb[J]`
and $`\Leb[B_0 \cap I] > \frac{3}{4} \Leb[I]`.

By {bpref "lem:dividing-high-operlap-interval"}[]
for any $`n,m \in \bN` we can find intervals
$`I' \subset I` and $`J' \subset J`
with $`\Leb[I'] = \frac{1}{n} \Leb[I]` and $`\Leb[J'] = \frac{1}{m} \Leb[J]`
and such that $`\Leb[A_0 \cap J'] > \frac{3}{4} \Leb[J']`
and $`\Leb[B_0 \cap I'] > \frac{3}{4} \Leb[I']`.
By choosing $`n` and $`m` suitably, we can ensure that
$$`\frac{1}{2} \Leb[I'] \; \le \; \Leb[J'] \; < \; \Leb[I'] .`

```tex
% we may divide
% $I$ and $J$ to equal length subintervals, at least one of which inherits
% this property, i.e.,
```

Then by {bpref "lem:shift-interval-contained-in-larger"}[]
there exists an open interval $`\Delta` of length
$`\Leb[\Delta] \, > \, \Leb[I'] - \Leb[J']` such that
for all $`t \in \Delta` we have $`t + J' \subset I'`.

Consider a fixed $`t \in \Delta`.
Observe that $`t + (B_0 \cap J) \subset I'` and
$$`\Leb[t + (B_0 \cap J')] \; = \; \Leb[B_0 \cap J']
  \; > \; \frac{3}{4} \Leb[J'] \; \ge \; \frac{3}{8} \Leb[I'] .`
We now claim that $`A_0 \cap I'` and $`t + (B_0 \cap J')` intersect.
Their measures add up to at least
$$`\begin{aligned}
\Leb[A_0 \cap I'] + \Leb[t + (B_0 \cap J')]
\; = \; & \Leb[A_0 \cap I'] + \Leb[B_0 \cap J'] \\
\; > \; & \frac{3}{4} \Leb[I'] + \frac{3}{4} \Leb[J'] \\
\; \ge \; & \frac{3}{4} \Leb[I'] + \frac{3}{8} \Leb[I']
\; = \; & \frac{9}{8} \Leb[I'] .
\end{aligned}`
and both have been shown to be subsets of $`I'`; therefore they
cannot be disjoint.
In particular there is a point $`z \in (A_0 \cap I') \cap (t + B_0 \cap J')`,
which means that
$$`a = z = t + b`
for some $`a \in A_0 \cap I'` and $`b \in B_0 \cap J'`. We solve
$`t = a - b \in A_0 - B_0 \subseteq A - B`. Since $`t \in \Delta`
was arbitrary, we have shown that the nontrivial open interval $`\Delta`
is contained in $`A - B`.
:::
