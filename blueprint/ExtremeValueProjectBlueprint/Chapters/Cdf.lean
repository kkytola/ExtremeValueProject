import Verso
import VersoManual
import VersoBlueprint
import ExtremeValueProject
import ExtremeValueProjectBlueprint.TeXPrelude

open Verso.Genre Manual Informal

#doc (Manual) "Cumulative distribution functions" =>

:::definition "def:cdf" (lean := "CumulativeDistributionFunction")
A function $`F \colon \R \to \R` is a
_cumulative distribution function_ (c.d.f.) if

* (i) $`x \mapsto F(x)` is increasing;
* (ii) $`x \mapsto F(x)` is right-continuous;
* (iii) $`\lim_{x \to -\infty} F(x) = 0` and $`\lim_{x \to +\infty} F(x) = 1`.
:::

:::lemma_ "lem:cdf-of-random-var" (lean := "MeasureTheory.ProbabilityMeasure.cdf") (uses := "def:cdf")
If $`X` is a real-valued random variable, then the function
$`F \colon \R \to \R` given by $`F(x) = \PR \big[ X \le x \big]` is a c.d.f.
:::

:::proof "lem:cdf-of-random-var"
Property (1.) in {bpref "def:cdf"}[] is obvious (by monotonicity of measures)
and properties (2.) and (3.) are simple consequences of monotone convergence
theorems for probability measures.
:::

# Degenerate distributions

:::definition "def:degenerate-cdf" (lean := "CumulativeDistributionFunction.IsDegenerate") (uses := "def:cdf")
A c.d.f. $`F` is said to be
_degenerate_ if for every $`x \in \R` we have either $`F(x) = 0` or $`F(x) = 1`.
Otherwise $`F` is said to be _nondegenerate_.
:::

:::lemma_ "lem:degenerate-cdf-iff-exists-jump" (lean := "CumulativeDistributionFunction.isDegenerate_iff") (uses := "def:degenerate-cdf")
$`F` is a degenerate c.d.f. if and only if there exists a $`x_0 \in \R` such that
$$`\begin{aligned}
F(x) = \begin{cases}
        0 & \text{ for } x < x_0 \\
        1 & \text{ for } x \ge x_0 .
       \end{cases}
\end{aligned}`
:::

:::proof "lem:degenerate-cdf-iff-exists-jump"
The “if” direction is clear. To prove the “only if” direction, assume that
$`F` is a degenerated c.d.f., and let $`x_0 = \inf \set{ x \in \R \; \big| \; F(x) = 1}`.
Then it is straightforward to show by properties of a c.d.f. that $`F` has the asserted form.
:::

:::lemma_ "lem:delta-has-degenerate-cdf" (lean := "CumulativeDistributionFunction.diracProba_is_degenerate") (uses := "def:degenerate-cdf")
The c.d.f. of Dirac delta mass $`\delta_{x_0}` at $`x_0 \in \R` is degenerate.
:::

:::proof "lem:delta-has-degenerate-cdf" (uses := "lem:degenerate-cdf-iff-exists-jump")
…
:::

:::lemma_ "lem:degenerate-cdf-is-delta" (lean := "CumulativeDistributionFunction.eq_diracProba_of_isDegenerate") (uses := "def:degenerate-cdf")
If a c.d.f. $`F` is degenerate, then it is the c.d.f. of a Dirac delta mass $`\delta_{x_0}`
at some point $`x_0 \in \R`.
:::

:::proof "lem:degenerate-cdf-is-delta" (uses := "lem:degenerate-cdf-iff-exists-jump")
…
:::

# Distributions of maxima of independent random variables

```tex
% \begin{lemma}
% \label{lem:random-var-of-cdf}
% \uses{def:cdf}
% If $F \colon \R \to \R$ is a c.d.f., then there exists a probability
% space $(\Omega, \mathcal{F}, \PR)$ and a real-valued random variable
% $X \colon \Omega \to \R$ such that for every $x \in \R$
% we have $F(x) = \PR \big[ X \le x \big]$.
% \end{lemma}
% \begin{proof}
% Abstract nonsense (take $\Omega = [0,1]$ and $X = \idOf{\R}$ ).
% \end{proof}
```

:::lemma_ "lem:cdf-of-max-two" (uses := "def:cdf")
Let $`X` and $`Y` be two independent real-valued random variables with respective
cumulative distribution functions $`F` and $`G`,
i.e. $`F(x) = \PR \big[ X \le x \big]` and $`G(x) = \PR \big[ Y \le x \big]`.
Then the c.d.f. of $`M = \max (X, Y)` is $`x \mapsto F(x) \, G(x)`.
:::

:::proof "lem:cdf-of-max-two"
Fix $`x \in \R`. Note that $`\max (X, Y) \le x` if and only if both $`X \le x` and $`Y \le x`.
Calculate, using independence,
$$`\PR\big[ \max (X, Y) \le x \big]
\; = \; \PR\big[ X \le x \, \; Y \le x \big]
\; = \; \PR\big[ X \le x \big] \; \PR\big[ Y \le x \big]
\; = \; F(x) \, G(x) .`
:::

:::lemma_ "lem:cdf-of-max-many" (uses := "def:cdf")
Let $`X_0, X_1, \ldots, X_{n-1}` be independent identically distributed real-valued random variables
with cumulative distribution functions $`F`,
i.e. $`F(x) = \PR \big[ X_j \le x \big]` for every $`j`.
Then the c.d.f. of $$`M_n = \max_{0 \le j < n} X_j` is the function $`x \mapsto \big(F(x)\big)^n`.
:::

:::proof "lem:cdf-of-max-many" (uses := "lem:cdf-of-max-two")
Induction on $`n` using {bpref "lem:cdf-of-max-two"}[].
:::

:::lemma_ "lem:cdf-of-affine-max-many" (uses := "def:cdf")
Let $`X_0, X_1, \ldots, X_{n-1}` be independent identically distributed real-valued random variables
with cumulative distribution functions $`F`,
i.e. $`F(x) = \PR \big[ X_j \le x \big]` for every $`j`,
and let $`a > 0` and $`b \in \R`.
Then the c.d.f. of
$$`\hat{M}_n = \frac{\max_{0 \le j < n} X_j - b}{a}`
is the function $`x \mapsto \big(F(a x + b)\big)^n`.
:::

:::proof "lem:cdf-of-affine-max-many" (uses := "lem:cdf-of-max-many")
Use {bpref "lem:cdf-of-max-many"}[] and do a change of variables.
:::

# Distributions of minima of independent random variables

# Equivalence classes modulo affine transformations

:::definition "def:oriented-affine-isomorphism" (lean := "AffineIncrEquiv")
The collection of all transformations $`\R \to \R` of the form
$`x \mapsto a x + b`, where $`a>0`, $`b \in \R`, forms a group.
We call this the _orientation preserving affine isomorphism group_
and denote it by $`\OriAffR`.
:::

:::definition "def:oriented-affine-transform-of-cdf" (lean := "CumulativeDistributionFunction.affineTransform") (uses := "def:oriented-affine-isomorphism, def:cdf")
The action of an orientation preserving affine isomorphism $`A \in \OriAffR`
on a cumulative distribution function $`F` is defined so
that $`A.F \colon \R \to \R` is given by $`(A.F)(x) = F(A^{-1}(x))`.
Then $`A.F` is also a c.d.f.
:::

:::lemma_ "lem:oriented-affine-action-on-cdf" (lean := "CumulativeDistributionFunction.instMulActionAffineIncrEquiv") (uses := "def:oriented-affine-transform-of-cdf")
The actions of orientation preserving affine isomorphisms
on a cumulative distribution functions is a group action, i.e.,
$`1.F = F` and $`(AB).F = A.(B.F)` for any c.d.f. $`F` and any $`A,B \in \OriAffR`.
:::

:::proof "lem:oriented-affine-action-on-cdf"
Direct calculations.
:::

:::lemma_ "lem:degenerate-cdf-transform" (lean := "CumulativeDistributionFunction.affine_isDegenerate_iff") (uses := "lem:oriented-affine-action-on-cdf, def:degenerate-cdf")
Let $`F` be a cumulative distribution function
and $`A \in \OriAffR` an orientation preserving affine isomorphism.
Then $`A.F` is degenerate if and only if $`F` is degenerate.
:::

:::proof "lem:degenerate-cdf-transform"
Straightforward from the definitions.
:::

:::lemma_ "lem:cdf-continuity-pt-transform" (lean := "CumulativeDistributionFunction.affine_continuousAt_of_continuousAt") (uses := "lem:oriented-affine-action-on-cdf")
Let $`F` be a cumulative distribution function,
and $`A \in \OriAffR` an orientation preserving affine isomorphism.
If a point $`x \in \R` is a continuity point of $`F`, then
the point $`A(x) \in \R` is a continuity point of $`A.F`.
:::

:::proof "lem:cdf-continuity-pt-transform"
Straightforward.
:::

```tex
% \begin{lemma}
% \label{lem:cdf-affine-group-action}
% \uses{def:cdf}
% Suppose $a > 0$ and $b \in \R$. Then for any c.d.f. $F$, also
% the function $x \mapsto F(a x + b)$ is a c.d.f.
% \end{lemma}
% \begin{proof}
% \ldots
% \end{proof}
%
% \begin{definition}
% \label{def:cdf}
% %\lean{CumulativeDistributionFunction}
% %\uses{def:degenerate-cdf}
% \uses{def:cdf}
% A function $F \colon \R \to \R$ is a
% \emph{cumulative distribution function} (c.d.f.) if
% \begin{enumerate}
% \item[(i)] $x \mapsto F(x)$ is increasing;
% \item[(ii)] $x \mapsto F(x)$ is right-continuous;
% \item[(iii)] $\lim_{x \to -\infty} F(x) = 0$ and $\lim_{x \to +\infty} F(x) = 1$.
% \end{enumerate}
% \end{definition}
%
```

# Miscellaneous results on cumulative distribution functions

:::lemma_ "lem:cdf-continuity-pt-iff-measure-singleton" (lean := "CumulativeDistributionFunction.continuousAt_iff") (uses := "def:cdf")
*Continuity points of c.d.f.s are those which carry no point mass*

Let $`F` be cumulative distribution function of a
probability measure $`\PRmeas` on $`\bR`. A point $`x \in \bR` is
a continuity point of $`F` if and only if $`\PRmeas[\set{x}] = 0`.
:::

:::proof "lem:cdf-continuity-pt-iff-measure-singleton"
A c.d.f. is always continuous from the right.

Continuity of $`F` from the left at $`x` means that for any
sequence $`(x_n)_{n \in \bN}` increasing to $`x`
(i.e., $`x_n \le x_{n+1} < x` for all $`n \in \bN`)
$$`F(x_n) \to F(x) ,`
or equivalently in terms of measures
$$`\PRmeas \big[ (-\infty,x_n] \big] \to \PRmeas \big[ (-\infty,x] \big] .`
But by monotone convergence of measures, we always have
$$`\begin{aligned}
\PRmeas \big[ (-\infty,x_n] \big]
\to \; & \PRmeas \big[ (-\infty,x) \big] \\
= \; & \PRmeas \big[ (-\infty,x] \big] - \PRmeas[\set{x}] .
\end{aligned}`
A comparison of these conditions shows that $`F` is also continuous from the left
at $`x` if and only if $`\PRmeas[\set{x}] = 0`.
:::

:::lemma_ "lem:exists-two-nontrivial-continuity-pts-cdf" (lean := "CumulativeDistributionFunction.exists₂_continuousAt_of_not_isDegenerate") (uses := "def:degenerate-cdf")
*A pair of nontrivial continuity points of nondegenerate c.d.f.*

Let $`G` be a nondegenerate c.d.f. Then there exists
continuity points $`x_1 < x_2` of $`G` such that
$`0 < G(x_1) \le G(x_2) < 1`.
:::

:::proof "lem:exists-two-nontrivial-continuity-pts-cdf"
Since $`G` is nondegenerate, there exists some $`x_0 \in \bR` such that
$`0 < G(x_0) < 1`. Since $`G` is continuous from the right, for some
small $`\delta > 0` we have that $`0 < G(x) < 1` for
all $`x \in [x_0,x_0+\delta)`. Since the continuity points of $`G`
are dense, from any nonempty open interval we may pick a continuity point.
First pick a continuity point $`x_1 \in (x_0,x_0+\delta)`,
and then pick another continuity point $`x_2 \in (x_1,x_0+\delta)`.
:::

:::lemma_ "lem:cdf-equal-on-dense" (lean := "CumulativeDistributionFunction.eq_of_forall_dense_eq") (uses := "def:cdf")
*Equality of c.d.f.s on a dense set suffices*

Suppose that $`F,G` are two c.d.f.s and $`S \subseteq \bR` is a dense
subset of the real line. If $`F(\xi) = G(\xi)` for all $`\xi \in S`,
then we have $`F = G`.
:::

:::proof "lem:cdf-equal-on-dense"
We must prove that for any $`x \in \bR` we have $`F(x) = G(x)`.
But by right-continuity of c.d.f.s, density of $`S`, and coincidence of
$`F` and $`G` on $`S`, we have
$$`\begin{aligned}
  F(x)
= \; & \lim_{\xi \to x^+ \text{ along $S$}} F(\xi) \\
= \; & \lim_{\xi \to x^+ \text{ along $S$}} G(\xi)
= \, G(x) .
\end{aligned}`
:::

# Topology on orientation-preserving affine isomorphisms

:::definition "def:affine-transform-topology" (lean := "instTopologicalSpaceAffineIncrEquiv") (uses := "def:oriented-affine-isomorphism")
We equip the space $`\OriAffR` of orientation-preserving affine isomorphisms
with the topology of pointwise convergence, i.e., with the
coarsest topology which makes the evaluations $`A \mapsto A(x)` continuous
for all $`x \in \bR`.
:::

:::lemma_ "lem:affine-coefficients-continuous" (lean := "AffineIncrEquiv.continuous_coefs_fst, AffineIncrEquiv.continuous_coefs_snd") (uses := "def:oriented-affine-isomorphism")
*The coefficients of affine map depend continuously on the map*

The coefficients $`a` and $`b` of an orientation-preserving affine isomorphism
$`A(x) = a x + b` depend continuously on $`A`.
:::

:::proof "lem:affine-coefficients-continuous"
We may first write $`a = A(1) - A(0)` and $`b = A(0)`.
These depend continuously on $`A`,
since the evaluations $`A(1)` and $`A(0)` do.
:::

:::lemma_ "lem:affine-metrizable" (lean := "AffineIncrEquiv.homeomorph_prod, AffineIncrEquiv.metrizableSpace") (uses := "def:affine-transform-topology")
*Metrizability of the topology on oriented affine isomorphisms*

The topology of pointwise convergence makes $`\OriAffR`
homeomorphic to $`\bR^2`, and in particular
metrizable.
:::

:::proof "lem:affine-metrizable" (uses := "lem:affine-coefficients-continuous")
The essential claim is that the function
$$`\mathrm{cfs} \colon \OriAffR \to (0,+\infty) \times \bR`
obtained by mapping $`A(x) = a x + b` to its coefficients $`(a,b)` is a homeomorphism.
(The homeomorphism to $`\bR^2 = \bR \times \bR` follows by combining with the
homeomorphism $`(a,b) \mapsto (\log a, b)`.)

The continuity of $`\mathrm{cfs}` follows from {bpref "lem:affine-coefficients-continuous"}[].
For the continuity of the inverse, we must only check that for any $`x \in \bR`,
its composition with the point evaluation at $`x` is continuous. But the composition
is $`(a,b) \mapsto a x + b`, and the continuity is clear.
:::

:::lemma_ "lem:affine-inversion-continuous" (lean := "AffineIncrEquiv.continuous_inv, AffineIncrEquiv.invHomeomorph") (uses := "def:oriented-affine-isomorphism")
*Inversion of orientation preserving affine isomorphisms is continuous*

The map $`A \mapsto A^{-1}` is continuous on $`\OriAffR`.
In particular, inversion defines a homeomorphism of $`\OriAffR` to itself.
:::

:::proof "lem:affine-inversion-continuous" (uses := "lem:affine-coefficients-continuous")
Calculate and use {bpref "lem:affine-coefficients-continuous"}[].
:::

:::lemma_ "lem:action-on-cdf-continuous" (lean := "CumulativeDistributionFunction.continuous_mulAction") (uses := "lem:oriented-affine-action-on-cdf")
*The action of oriented affine transforms on c.d.f.s is continuous*

The action $`A . F` of $`A \in \OriAffR` on a c.d.f $`F` depends
jointly continuously on $`A` and $`F`.

_(The topology on c.d.f.s is the topology of convergence in distribution, i.e.,
convergence at all continuity points of the limit cdf.)_
:::

:::proof "lem:action-on-cdf-continuous" (uses := "lem:affine-metrizable, lem:affine-inversion-continuous")
The spaces are metrizable, so it suffices to check sequential continuity.

Suppose that $`A_n \to B` (oriented affine isomophisms)
and $`F_n \tendsinlaw G` (c.d.f.s) as $`n \to \infty`.
Let $`x \in \bR` be a continuity point of $`B.G`.
Let $`\eps > 0`. Note that $`B^{-1}(x)` is a continuity point of $`G`.
Then there exists a $`\delta > 0` such that $`|G(y) - G\big(B^{-1}(x)\big)| < \frac{\eps}{2}`
when $`|y-B^{-1}(x)|<\delta`.

By density of continuity points of $`G`, pick continuity points
$`y_-,y_+` such that
$$`B^{-1}(x)-\delta \; < \; y_- \; < \; B^{-1}(x) \; < \; y_+ \; < \; B^{-1}(x)+\delta .`
Since $`F_n \tendsinlaw G`, we have that
$`F_n(y_\pm) \to G(y_\pm)` as $`n \to \infty`,
and in particular there exists some $`N` such that for $`n \ge N`
we have $`\big| F_n(y_\pm) - G(y_\pm) \big| < \frac{\eps}{4}` for both $`y_\pm`.

By {bpref "lem:affine-inversion-continuous"}[]
and $`A_n \to B`, we get that $`A_n^{-1} \to B^{-1}`, and in particular
there exists some $`N'` such that for $`n \ge N'` we have
$$`y_- < A_n^{-1}(x) < y_+ .`

For $`n \ge \max \set{N,N'}`, we then have
$$`\begin{aligned}
(A_n.F_n)(x) \;
= \; & F_n \big( A_n^{-1}(x) \big) \\
\le \; & F_n (y_+) \\
< \; & G(y_+) + \frac{\eps}{4} \\
\le \; & G \big( B^{-1}(x) \big) + \frac{\eps}{2} + \frac{\eps}{4} \\
= \; & (B.G) (x) + \frac{3\eps}{4} \\
< \; & (B.G) (x) + \eps
\end{aligned}`
and similarly
$$`\begin{aligned}
(A_n.F_n)(x) \;
= \; & F_n \big( A_n^{-1}(x) \big) \\
\ge \; & F_n (y_-) \\
> \; & G(y_-) - \frac{\eps}{4} \\
\ge \; & G \big( B^{-1}(x) \big) - \frac{\eps}{2} - \frac{\eps}{4} \\
= \; & (B.G) (x) - \frac{3\eps}{4} \\
> \; & (B.G) (x) + \eps ,
\end{aligned}`
which together yield $`\big| (A_n.F_n)(x) - (B.G)(x) \big| < \eps`.

Since $`x` was an arbitrary continuity point of $`B.G` and
$`\eps > 0` was arbitrary, this proves that $`A_n.F \tendsinlaw B.G`.
:::

```tex
% lem:oriented-affine-action-on-cdf
```
