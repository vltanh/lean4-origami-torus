# Forced profiles inside the endpoint virtual-edge cones

This is a separate refinement of the frozen
[virtual12 cover](solver_remaining_virtual12.md). It retains the same
331 primary sign completions, macro profile `(c,d,e)`, and weak actual
bracket semantics. It does not exclude the endpoint.

For direction `(-1,aY,0)`, all 15 surviving generic completions share one
linear cone. Exact nonnegative combinations of its necessary rows give

\[
c-e\ge0,\quad e-c\ge0,\quad d\ge0,\quad-d\ge0,
\quad a_Y\ge0,\quad-a_Y\ge0,\quad c\ge0.
\]

Thus `c=e>=0`, `d=aY=0`. Since the first-width profile is normalized by
`max(abs(c),abs(d),abs(e))=1`, its unique normalized profile is

\[
(c,d,e,a_Y)=(1,0,1,0).
\]

For direction `(0,aY,2)`, the 172 surviving generic completions occupy
five linear cones. In each cone, two exact nonnegative row combinations
prove `aY>=0` and `-aY>=0`. Therefore **`aY=0`** throughout this family.
The other macro coordinates remain free within their necessary cones.

The seventeen certificates are rational Farkas implication identities,
not optimization results. For each target linear form `L`, replay checks

\[
\sum_i\lambda_i\bigl(A_i x+b_i\bigr)=L(x),\qquad\lambda_i\ge0
\]

coefficient by coefficient. Since every source row is nonnegative, so is
`L`. No normalization face is needed in these implication identities;
normalization is used only to turn `c=e>=0,d=0` into `c=e=1`.

Replay first re-enumerates the source 331 primary completions and checks
all 426 certificates in the original virtual12 packet. The refinement
packet binds that frozen source file by SHA-256 and binds each group by
its complete list of 70-character sign strings. All six surviving groups
in the two selected direction families are covered.

```sh
python research/type7_completion/solver_remaining_virtual12_consequences.py
python research/type7_completion/solver_remaining_virtual12_consequences.py \
  --produce /tmp/virtual12-consequences.json
```

The optional producer uses an LP to find small supports, then solves the
supported identities exactly. Replay uses exact rational arithmetic and
does not import SciPy. The endpoint source completeness CNF must also
have an independently accepted proof, as for the original virtual12
package. These forced profiles supply hypotheses for further metric
analysis; they do not constitute that analysis.
