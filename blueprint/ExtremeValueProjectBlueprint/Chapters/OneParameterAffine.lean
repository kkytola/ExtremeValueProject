import Verso
import VersoManual
import VersoBlueprint
import ExtremeValueProject
import ExtremeValueProjectBlueprint.TeXPrelude

open Verso.Genre Manual Informal

#doc (Manual) "One-parameter subgroups of affine isomorphisms" =>

```tex
%The group $\OriAffR$ is isomorphic to the matrix group
%\begin{align*}
%  \left\{ \left[ \begin{array}{cc} a & b \\ 0 & 1 \end{array} \right] \; \Bigg|
%    \; a>0, b \in \bR \right\} .
%\end{align*}
%This is a 2-dimensional Lie group with Lie algebra\ldots
```

:::lemma_ "lem:affine-one-parameter-subgroup-functional-eqn" (uses := "def:oriented-affine-isomorphism")
*Functional equation in one parameter subgroups of affine isomorphisms*

Suppose that $`t \mapsto A_t` is a homomorphism of multiplicative groups
$`(0,+\infty) \to \OriAffR`, i.e., for any $`s, t > 0` we have
$$`A_{s t} = A_s \circ A_t .`
Write $`A_t(x) = a_t x + b_t`, with $`a_t > 0` and $`b_t \in \bR`.
Then we have, for any $`s, t > 0`,
$$`\begin{aligned}
a_{t s} = \; & a_t \, a_s
  \qquad \text{ and } \\
b_{t s} = \; & a_t \, b_s + b_t .
\end{aligned}`
(Also by symmetry $`b_{t s} = a_s \, b_t + b_s`.)
:::

:::proof "lem:affine-one-parameter-subgroup-functional-eqn"

:::

:::lemma_ "lem:solution-functional-eqn-scaling" (lean := "eq_exp_const_mul_of_multiplicative_of_measurable")
*Functional equation scaling coefficient solution*

Suppose that $`a \colon (0,+\infty) \to (0,+\infty)` is a
measurable function satisfying, for any $`s, t > 0`,
$$`\begin{aligned}
a(t s) = \; & a(t) \, a(s) .
\end{aligned}`
Then there exists a $`\rho \in \bR` such that for all $`t > 0`,
$$`a(t) = t^{\rho} .`
:::

:::proof "lem:solution-functional-eqn-scaling" (uses := "lem:different-difference-set-contains-interval")

:::

:::lemma_ "lem:solution-functional-eqn-translation-no-scaling" (lean := "eq_const_mul_of_additive_of_measurable, eq_exp_const_mul_of_multiplicative_of_measurable")
*Functional equation translation coefficient solution with $`\rho = 0`*

Suppose that
$`b \colon (0,+\infty) \to \bR` is a measurable function
satisfying, for any $`s, t > 0`,
$$`\begin{aligned}
b(t s) = \; & b(s) + b(t) .
\end{aligned}`
Then there exists a constant $`c` such that for $`t \in (0,+\infty)`
we have
$$`\begin{aligned}
b(t) = \; & -c \, \log (t) .
\end{aligned}`
:::

:::proof "lem:solution-functional-eqn-translation-no-scaling" (uses := "lem:solution-functional-eqn-scaling")

:::

:::lemma_ "lem:solution-functional-eqn-translation-with-scaling" (lean := "eq_const_mul_one_sub_exp_of_multiplicative_with_scaling_of_measurable")
*Functional equation translation coefficient solution with $`\rho \ne 0`*

Suppose that $`\rho \in \bR \setminus \set{0}` and
$`b \colon (0,+\infty) \to \bR` is a measurable function
satisfying, for any $`s, t > 0`,
$$`\begin{aligned}
b(t s) = \; & t^{\rho} \, b(s) + b(t) .
\end{aligned}`
Then there exists a constant $`c` such that for $`t \in (0,+\infty) \setminus \set{1}`
we have
$$`\begin{aligned}
b(t) = \; & c (1 - t^{-\rho}) .
\end{aligned}`
:::

:::proof "lem:solution-functional-eqn-translation-with-scaling" (uses := "lem:solution-functional-eqn-scaling")

:::

The above solutions to functional equations can be used to classify all
one-parameter subgroups of the group of oriented affine isomorphisms of $`\bR`.
Such a subgroup can be given in a parametrized form as a group homomorphism
$`\bR \to \OriAffR` (from the additive group $`\bR`) or alternatively
as group homomorphisms $`(0,+\infty) \to \OriAffR` (from the multiplicative
group $`(0,+\infty)`). The additive and multiplicative versions are
related by the change of variable
$`\bR \ni t \leftrightarrow \lambda := e^t \in (0,+\infty)`
(conversely, $`t = \log(\lambda)`).
_(In Lean the type $`\bR` is more convenient than the type $`(0,+\infty)`,
so in formal statements we prefer the former choice.)_

:::theorem "thm:one-parameter-subgroups-of-affine-isomorphisms" (lean := "AffineIncrEquiv.homomorphism_from_Real_characterization, AffineIncrEquiv.homomorphism_from_Real_characterization_of_nontrivial") (uses := "def:oriented-affine-isomorphism, def:translation-subgroup, def:fixing-subgroup")
*One-parameter subgroups of affine isomorphisms of $`\bR`*

_\[TODO: Switch to additive notation and $`\bR` rather than multiplicative
notation and $`(0,+\infty)`, to match the most convenient formalized statements.\]_

Suppose that $`t \mapsto A_t` is a measurable homomorphism of multiplicative groups
$`(0,+\infty) \to \OriAffR`, i.e., for any $`s, t > 0` we have
$$`A_{s t} = A_s \circ A_t`
and $`A_t(x) = a_t x + b_t`, with $`t \mapsto a_t` and $`t \mapsto b_t`
measurable functions.
Then either

* (0) there exists a $`\beta \in \bR` such that for all $`t > 0` and $`x \in \bR`
  $$`A_t(x) = x + \beta \, \log(t) ;`
  or
* (1) there exists a $`\rho \ne 0` and $`c \in \bR` such that
  for all $`t > 0` and $`x \in \bR`
  $$`A_t(x) = t^{\rho} (x - c) + c .`
:::

:::proof "thm:one-parameter-subgroups-of-affine-isomorphisms" (uses := "lem:affine-one-parameter-subgroup-functional-eqn, lem:solution-functional-eqn-scaling, lem:solution-functional-eqn-translation-no-scaling, lem:solution-functional-eqn-translation-with-scaling")

:::
