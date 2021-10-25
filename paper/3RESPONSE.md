We are thankful to reviewers for their work.

First, let us address one of the main concerns of referees A and C:

## Coq formalization

  Since submission we have formalized this work in Coq.  This development is
  available for referees at https://fpl.cs.depaul.edu/jriely/PwT.zip
  (approximately 11,000 lines of code).  In particular, we have formally
  verified lemma 4.5, which states that SEQ is associative (SeqAssoc.v) and
  that SKIP is left and right unit (SeqSkipId.v).

## Overall comments

We reiterate the broader context of our work: Thin air is a problem
with the semantics of all optimized concurrent languages.  There are only a
handful of solutions and all have deficiencies.  We focus on denotations with
semantic dependency (SDEP) and sequential composition for the following
reasons:
- Using an SDEP relation is the only approach compatible with the existing
  C++ concurrency definition.
- Sequential composition is necessary for scalable reasoning about big chunks
  of code.  No existing model captures it.
- Existing models do not get at the essence of the problem.  By analogy: one
  can use Landin's SECD machine to understand iteration, but Hoare logic and
  Scott–Strachey semantics provide much more insight.

## Reviewers A and C. Why is a denotational semantics for sequential composition challenging and worthwhile?

Both referees asked about the motivation for a compositional model of
sequential composition, why not consider S1 and S2 equal if, for every
continuation S0, we have [[ S1 ; S0 ]] = [[ S2 ; S0 ]]?  The problem
is that this requires a quantification over all continuations S0. This
quantification is problematic, both from a theoretical point of view
(the syntax of programs is now mentioned in the definition of the
semantics) and in practice (tools cannot quantify over infinite
sets. This is a related problem to contextual equivalence, full
abstraction and the CIU theorem.

In addition, referee C asks: _My worry is: is this a big enough "win"
to be worth all this effort?_ We would argue yes, that having a model
behind peephole compiler optimizations is worth it, and that this
requires a compositional treatment of sequential composition.

To determine whether a dependency is present in some fragment of code, MRD
and PwP require that all of following code is evaluated.  Suppose that you
are writing system call code and you wish to know if you can reorder a couple
of statements.  Using MRD or PwP, you cannot tell whether this is possible
without having the calling code.  This is what we mean when we say that MRD
and PwP require perfect knowledge of the future.

We have attempted to capture semantic dependencies in a meaningful way that
admits sequential composition.  PwP/MRD only got halfway there: No one would
have ever been happy with Hoare logic if it failed to capture the meaning of
sequential composition.

With PwT, the presence or absence of a dependency can be understood in
isolation.  In practice, this enables future applications where PwT can be
used to modularly validate assumptions about program dependencies in larger
blocks of code incrementally -- rather than the approach of MRD/PwP where
evaluation must be done totally.

Further, PwT-C11 is only the second semantics to interoperate with C++
through a semantic dependency relation, and the first one to be fully
compositional.  Semantic dependency is a worthwhile goal: a restriction of
$acyclic(SDEP \cup RF)$ is a statement which is compatible with the existing
C++ standard, subject to a good definition of SDEP.  With the exception of
MRD, other thin-air free programming language memory models do not distill
dependencies down to a relation compatible with the existing C++ standard.

## Reviewers A and C. Correctness of the model, relating models.

As noted above, the work has been formalized in Coq.

We agree that a new memory model needs to be positioned against existing
models.  The usual result here is a compilation correctness to hardware
memory models.  For PwT-MCA, we address this by showing compilation result
for Armv8 model (§5).

Comparing software models, however, is unsatisfying: they are all
incomparable, i.e., there are examples which are allowed by one/disallowed by
the other and vice versa.

Morally, our model sits between the strong models (exemplified by RC11
[Lahav-al:PLDI17]) and the speculative models (exemplified by the promising
semantics [Kang-al:POPL17]).  As we argue in §1:

- The strong models require too much synchronization.

- The speculative models allow thin air behaviors.

Looking at the details, however, PwT-MCA is incomparable to both RC11 and
promising semantics.  RC11 allows non-MCA behaviors that PwT-MCA disallows.
PwT-MCA has a weaker notion of coherence than the promising semantics.

Some differences reflect an attempt to fix a bug.  For example, Weakestmo
[Chakraborty-Vafeiadis:POPL19] purposefully disallows _thin-air-like_
behaviors of the promising semantics.

Other differences reflect a different balance between allowed optimizations
and reasoning principles.  There are fundamental conflicts, for example:

- between Common Subexpression Elimination (CSE) and read-read coherence
  (§D.1)

- between if-introduction (aka, case analysis, if-closure) and java-style
  final-field semantics.  (If-introduction requires that address dependencies
  and control dependencies are the same.  Final-fields require that they be
  different.)

## Reviewer B. Syntactic vs. semantic dependencies and their usage in compilers

Yes, tracking semantic dependencies is intrinsically harder than syntactic
ones, and hardware memory models stick with syntax.  However, we cannot
settle with syntactic dependencies for models of programming languages since
common compiler optimizations used in almost all real compilers (including
GCC and Clang) may remove syntactic dependencies (unlike semantic ones).
That is, a programming language memory model which supports compiler
optimizations and disallows OOTA (unlike the C/C++ memory model) has to track
semantic dependencies in one way or another. All other proposed solutions to
this problem do that (Promising [Kang-al:POPL17], Weakestmo
[Chakraborty-Vafeiadis:POPL19], MRD [Paviotti-al:ESOP20], PwP
[Jagadeesan-al:OOPSLA20]).

A compiler does not have to use the proposed semantics
directly, i.e., for calculating dependencies.  Instead, the semantics is
meant to be a wrapper that validates some reasonable set of compiler
optimizations. A compiler may make more conservative assumptions about
dependencies than the semantics. This is explicitly allowed by Lemma 4.8
(augment closure).

## Reviewer B. Does the model scale?

> Promising-ARM/RISC-V [Pulte et al. 2019] is evaluated on a concurrent queue
> implemented in 215 lines of C++ code. Does PwT-C11 work at this scale?

We have not attempted to run PwTer on programs as large as the Michael-Scott
queue.  In the theory itself, there is no issue, but as [Pulte et al. 2019]
point out, exploring such a large combinatorial state space is challenging.
The task is simplified in a hardware model, such as Promising-ARM/RISC-V.  In
a software model such as PwT-C11 or PwT-MCA, the state space is larger, and
therefore the task is that much more difficult.

## Reviewers A and B: Presentation

We have tried to make §§1-4 readable, as these communicate the basic idea.
It is true that §§5-9 are mostly definitions and results, but this seems
inevitable given the space constraints.
