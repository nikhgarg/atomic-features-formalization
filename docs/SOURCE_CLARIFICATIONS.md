# Mathematical notes for A Testable Theory of Atomic Features

These notes concern the September 25, 2026 manuscript. They make the intended
conventions from the proof appendix explicit and explain
alternative proof arguments.

## Recovery conventions

- **What becomes explicit in the main statements:** source columns have unit
  norm and recovered targets have positive prevalence. Both conditions are
  already stated at the start of the recovery proof appendix. Normalization
  makes the inner product a cosine score; positive prevalence excludes absent
  features when the tail is zero. An absent target has zero feature-presence
  F1 under the convention used here, even though $0\ge C\cdot0$.
- **Local notation:** $\operatorname{supp}(z(x))=K$ means support
  cardinality $K$. The separation condition concerns distinct features and
  positive-probability conditioning events. In the matching definition the two
  sides are columns of $U$ and $V$. An empty guaranteed prefix has
  length zero. In hierarchical recovery the tail argument is
  $n=\lfloor m/3\rfloor$, as in its proof.

These are not a Zipf assumption or an independence assumption. The constants
may depend on fixed sparsity, the stability margin, density and separation
bounds, approximation quality, and requested confidence, but not on either
dictionary width. The hierarchical law allows correlated child choices and
jointly distributed active coefficients under the stated conditional bounds.

The supporting uniform recovery theorem supplies the same learned coordinate
for direction and activation, with one positive activation threshold for all
qualifying features and widths. The source-facing statement projects to the
separate direction and activation witnesses in the paper. Hierarchical recovery
similarly has a supporting theorem with a common positive threshold. These
constructions are listed separately in the [theorem index](THEOREMS.md#supporting-uniform-constructions).
The constants also do not depend on ambient dimension, and recovery includes
the full-width endpoint $m=M$.

## Proof routes

**Local support recovery (Lemma 5).** The source constructs a sequence of balls
on which the learned sparse support becomes fixed. The checked proof instead
uses a uniform sparse-incidence estimate on the coefficient cube. The conditional
lower density bound transfers a small population error to small cube error;
sparse stability prevents arbitrarily many unrelated learned spans from
approximating the source cube without one learned support span being close.
The resulting cutoff depends only on sparsity, stability, the lower density
bound and requested accuracy, as stated in the lemma. No upper density bound,
pairwise support separation or width bound is added to this lemma.

**Hierarchical recovery (Theorem 3).** The checked proof uses the finite patterns
of parent/child presence, together with sparse stability and a uniform upper
bound on the joint coefficient density. A family of support spans with small
reconstruction error yields learned coordinates with the required presence
patterns; coefficient anti-concentration controls threshold classification
errors. Keeping all three atoms in each of the first $\lfloor m/3\rfloor$
families gives the tail-loss comparator. Conditional child probabilities bounded
below transfer the parent cutoff to both children. The argument accommodates
the source's arbitrary correlated child law. It proves the stated activation
conclusion; it does not turn that conclusion into direction recovery of every
child.

**Generic rigidity (Theorem 4).** The source parameterizes sparse factorizations
and invokes Sard's theorem. The checked argument works in projective charts and
uses the zero measure of lower-dimensional smooth images, followed by the
corresponding intrinsic surface measure on the product of unit spheres. The
parameter count and exceptional-set conclusion are the same. One null set works
simultaneously for all competing widths and sparsity budgets. The supporting
bound $K'\ge1+(d-1)(M-M')/M$ holds for every competing sparse factorization,
without stability or a restriction on its width, under the same generic-source
and richness conditions. This is a proved strengthening of the dimension
inequality; the manuscript's full theorem retains its stated assumptions.

**Local-to-global Hall (Lemma 4).** For finite left subsets, the minimal-deficit
and tree argument yields Hall's inequality. The local upper-neighborhood bound
also gives finite neighborhoods of individual vertices. The locally finite
infinite Hall theorem therefore supplies one matching on an arbitrary left set.
The dictionary application is finite; this step establishes the lemma's broader
standalone graph statement without changing that application.
