import Verso
import VersoManual
import VersoBlueprint
import ExtremeValueProject
import ExtremeValueProjectBlueprint.TeXPrelude

open Verso.Genre Manual Informal

#doc (Manual) "Classification of extreme value distributions" =>

# Auxiliary classification I

:::lemma_ "lem:ode-of-order-two-for-Q" (lean := "ExtremeValueProject.ode_of_order_two_for_Q")
*Second order differential equation for Q*

Suppose that
$$`Q \colon \bR \to \bR`
is differentiable and satisfies
$$`Q(0) = 0 \qquad \text{ and } \qquad Q'(0) = 1`
and
$$`Q(h+s) = Q(h) \alpha(s) + Q(s)`
for some $`\alpha \colon \bR \to \bR` and every $`s,h \in \bR`.
Then $`Q` is twice continuously differentiable and satisfies
$$`Q''(s) = Q'(s) \, Q''(0) \qquad \text{ for every } s \in \bR . \tag{3.1}`
:::

:::proof "lem:ode-of-order-two-for-Q"
Note first that the equation implies (rearranging and dividing by $`h`),
for any $`s` and $`h \ne 0`,
$$`\frac{Q(h+s) - Q(s)}{h} = \frac{Q(h)}{h} \alpha(s) .`
Taking the limit as $`h \to 0` and using $`Q(0)=0` yields
$`Q'(s) = Q'(0) \, \alpha(s) = \alpha(s)`, where we also
took into account $`Q'(0) = 1`. Therefore necessarily
$`\alpha = Q'`, and the equation can be rewritten in the form
$$`Q(h+s) = Q(h) \, Q'(s) + Q(s) \qquad \text{ for } s,h \in \bR .`

Rearranging the equation, we find
$$`Q(h+s) - Q(s) = Q(h) \, Q'(s)`
and interchanging the role of $`s` and $`h` also
$$`Q(h+s) - Q(h) = Q(s) \, Q'(h) .`
Subtracting the last two equations yields
$$`Q(s) - Q(h) = Q(s) \, Q'(h) - Q(h) \, Q'(s) ,`
which by rearranging and dividing by $`h \ne 0` yields
$$`\frac{Q(h)}{h} \big( Q'(s) - 1 \big) = Q(s) \frac{Q'(h) - 1}{h} .`
Taking the limit $`h \to 0`, recalling $`Q(0)=1` and $`Q'(0)=1`,
gives the existence of the second derivative $`Q''(0)` and the equation
$$`Q'(s) - 1 = Q(s) Q''(0) .`
Solving $`Q'(s) = 1 + Q''(0) \, Q(s)` and recalling that $`Q`
is differentiable shows that $`Q'` is also differentiable, so
$`Q` is indeed twice differentiable. Differentiating, we get
the asserted equation
$$`Q''(s) = Q'(s) \, Q''(0) .`
Since $`Q'` is differentiable and in particular continuous, this also shows
that $`Q''` is continuous, i.e., that $`Q` is twice continuously differentiable.
:::

:::lemma_ "lem:solve-Q" (lean := "ExtremeValueProject.solve_Q")
*Solution for Q*

Suppose that $`Q \colon \bR \to \bR` is twice continuously differentiable
and $`Q'` is positive and $`Q`
and satisfies $`Q(0)=0`, $`Q'(0) = 1`, and the equation concluded in
{bpref "lem:ode-of-order-two-for-Q"}[] with $`\gamma = Q''(0)`, i.e.,
$$`Q''(s) = \gamma \, Q'(s) \qquad \text{ for every } s \in \bR . \tag{3.2}`
Then $`Q` is given by
$$`\begin{aligned}
Q(s) = \begin{cases}
  \frac{e^{\gamma s} - 1}{\gamma} & \; \text{ if $\gamma \ne 0$} \\
  \;\; s & \; \text{ if $\gamma = 0$}
  \end{cases}
  \qquad \text{for $s \in \bR$.}
\end{aligned}`

```tex
%  if $\gamma \ne 0$ and
%  \begin{align*}
%  Q(s) = s
%  \end{align*}
%  if $\gamma = 0$.
```
:::

:::proof "lem:solve-Q"
Since $`Q` is differentiable and $`Q'(s)>0` for any $`s \in \bR`,
we can write (3.2) as
$$`\der{s} \log Q'(s)
  = \frac{Q''(s)}{Q'(s)}
  = \gamma .`
Integrating and noting $`\log Q'(0) = \log 1 = 0`, this
yields $`\log Q'(s) = \gamma s` for all $`s \in \bR`, or equivalently
$`Q'(s) = e^{\gamma s}`. Integrating a second time
and noting $`Q(0) = 0`, this yields the desired formulas
in the two cases $`\gamma \ne 0` and $`\gamma = 0`, respectively, as follows.

If $`\gamma \ne 0`, then we get
$$`Q(s) = \int_0^s e^{\gamma u} \, \ud u = \frac{e^{\gamma s} - 1}{\gamma} .`

If $`\gamma = 0`, then we get
$$`Q(s) = \int_0^s e^0 \, \ud u = s .`
:::

```tex
% TODO: Move to a different file.
```

:::theorem "thm:monotone-ae-differentiable" (lean := "Monotone.ae_differentiableAt")
*Monotone functions are a.e. differentiable*

If $`f : \bR \to \bR` is nondecreasing, then the derivative
$`f'(x)` exists at almost every $`x \in \bR`.
In particular there exists points $`x` where $`f'(x)` exists.
:::

:::proof "thm:monotone-ae-differentiable"
(The proof is already in Mathlib.)
:::

:::lemma_ "lem:solve-E" (lean := "ExtremeValueProject.solve_E")
*Solution for E*

Suppose that $`E \colon (0,\infty) \to \bR`
is nondecreasing and nonconstant function which satisfies $`E(1) = 0` and
$$`E(\lambda \sigma) = E(\lambda) A(\sigma) + E(\sigma)`
for some $`A \colon (0,\infty) \to (0,\infty)` and all $`\lambda, \sigma > 0`.
Then, denoting $`c = E'(1)` and $`\gamma = \frac{1}{E'(1)} \dder{s} E(e^s) \big|_{s=0}`,
for all $`\lambda \in \bR` we have
$$`\begin{aligned}
E(\lambda) = \begin{cases}
  c \big( \lambda^\gamma - 1 \big) & \;\;\text{ if $\gamma \ne 0$.} \\
  c \, \log (\lambda) & \;\;\text{ if $\gamma = 0$.}
  \end{cases}
\end{aligned}`
:::

:::proof "lem:solve-E" (uses := "lem:ode-of-order-two-for-Q, lem:solve-Q, thm:monotone-ae-differentiable")
Denote $`H(s) = E(e^s)` for $`s \in \bR`. Then $`H(0) = E(1) = 0` and
$`H` is also nondecreasing and nonconstant.
By {bpref "thm:monotone-ae-differentiable"}[], there
exists some $`s_0 \in \bR` such that the derivative $`H'(s_0)` exists.

The equation for $`E` yields an equation for $`H`,
$$`H(h+s) = H(h) A(e^{s}) + H(s) \qquad \text{ for any } s, h \in \bR.`
We can rearrange this equation and divide by $`h`,
and we get for any $`s, h \in \bR`, $`h \ne 0`,
$$`\frac{H(h+s) - H(s)}{h} = \frac{H(h)}{h} A(e^{s}) .`
If $`s = s_0`, then the LHS tends to $`H'(s_0)` as $`h \to 0`.
The RHS must therefore also have a limit as $`s \to 0`, and
observing that $`\frac{H(h)}{h} = \frac{H(h) - H(0)}{h}`,
that limit is $`H'(0) A(e^{s_0})`, which shows that the derivative $`H'(0)` exists.
Then applying the same equation at general $`s \in \bR` shows that
$`H'(s) = H'(0) A(e^{s})` must exist, so $`H \colon \bR \to \bR` is
in fact everywhere differentiable.

Note that we must have $`H'(0) > 0`, because if $`H'(0) = 0`
then by the above equation $`H'(s) = 0` for every $`s` and then
$`H` is a constant function, which is a contradiction.
Denote $`c = H'(0) = \der{s} E(e^s) \big|_{s=0} = E'(1)`.

Also the equation and positivity of the function $`A` give $`H'(s)>0`
for all $`s`.

Now consider $`Q(s) = \frac{H(s)}{c}`. This $`H` is
obviously also differentiable, since $`H` is. The equation
for $`H` yields the following equation for $`Q`,
$$`Q(h+s) = Q(h) \alpha(s) + Q(s) \qquad \text{ for any } s,h \in \bR ,`
where $`\alpha(s) = A(e^{s})`.
By {bpref "lem:ode-of-order-two-for-Q"}[] $`Q` is then twice
continuously differentiable and satisfies
$$`Q'(s) Q'' (0) = Q'' (s) \qquad \text{ for all } s \in \bR . \tag{3.3}`
By {bpref "lem:solve-Q"}[] we then get
a formula for $`Q`, which involves
$$`\gamma = Q''(0) = \frac{H''(0)}{c}
  = \frac{1}{c} \dder{s} E(e^s) \big|_{s = 0} .`

If $`\gamma \ne 0` then the formula reads
$`Q(s) = \frac{e^{\gamma s} - 1}{\gamma}`.
Now just tracing the definitions, we get the asserted formula
$$`E(\lambda) = H(\log \lambda)
  = c \, Q(\log \lambda) = c \, \big( e^{\gamma \, \log(\lambda)} - 1 \big)
  = c \, \big( \lambda^{\gamma} - 1 \big) .`

If $`\gamma = 0` then the formula reads $`Q(s) = s`.
Now just tracing the definitions, we get instead
$$`E(\lambda) = H(\log \lambda)
  = c \, Q(\log \lambda) = c \, \log(\lambda) ,`
and the proof is complete.
:::

# Inverting to recover a cumulative distribution function

```tex
%\begin{lemma}[Classification of cdfs of evds]
%  \label{lem:cdf-of-evd-classification}
%  %\uses{}
%  %\lean{}
%  % \leanok
%  Suppose that $G \colon \bR \to [0,1]$ is a c.d.f.
%  whose right-continuous inverse is given by $G^\leftarrow = \cdots$
%\end{lemma}
```
