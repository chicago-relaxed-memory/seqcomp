We are thankful to reviewers for their work.

# Reviewer A and C. Why is a denotational semantics for sequential composition challenging and worthwhile?
TODO
[MB -- This question is mapping to the questions of motivation from Reviewers A and C. We should reiterate the broader motivation here:
1. thin air is a problem with the semantics of all optimised concurrent languages
2. there are only a handful of solutions out there and many of those are flawed
3. a solution framed as an SDEP relation is the only approach compatible with the existing C++ concurrency definition
4. sequential composition is necessary (but not sufficient) for scalable reasoning about big chunks of code, and no one else has that.
]

Both referees asked about the motivation for a compositional model of
sequential composition, why not consider S1 and S2 equal if, for every
continuation S0, we have [[ S1 ; S0 ]] = [[ S2 ; S0 ]]?  The problem
is that this requires a quantification over all continuations S0. This
quantification is problematic, both from a theoretical point of view
(the syntax of programs is now mentioned in the definition of the
semantics) and in practice (tools cannot quantify over infinite
sets. This is a related problem to contextual equivalence, full
abstraction and the CIU theorem.

In addition, referee C asks "My worry is: is this a big enough "win"
to be worth all this effort?" We would argue yes, that having a model
behind peephole compiler optimizations is worth it, and that this
requires a compositional treatment of sequential composition.

# Reviewers A and C. Correctness of the model, mechanization, relation to other models
We agree that the model is complicated and requires formal results to be sure in its correctness,
that is why we have been working on its mechanization.
Currently, we have mechanized in Coq Lemma 4.5 from the paper
(associativity of sequential composition and SKIP being left and right ids for sequential composition).
Associativity supports the automatic evaluation tool -- PwTer chooses one order for evaluation and yet is complete by associativity.

We also agree that a new memory model needs to be positioned against existing models.
The usual result here is a compilation correctness to hardware memory models.
We address this by showing compilation result for Armv8 model (§5)
(it could be easily extended to the x86-TSO model since x86-TSO has a stronger model than Armv8).
Developing a version of the semantics which could cover compilation to non-MCA models like IBM Power
is our immediate future work, which we decided not to include in this submission since it would require to put even
more to this (quite dense in our opinion) paper.

Direct comparing of behaviors allowed by other memory models for programming languages solving the OOTA problem
(Promising [Kang-al:POPL17], Weakestmo [Chakraborty-Vafeiadis:POPL19], MRD [Paviotti-al:ESOP20], PwP [Jagadeesan-al:OOPSLA20])
is not as interesting since all of them are incomparable, i.e., there are examples which are allowed by one/disallowed by another
and vice versa.
TODO: say something good about properties of our model comparing to these models.


# Reviewer B. Promising-ARM/RISC-V [Pulte et al. 2019] is evaluated on a concurrent queue implemented in 215 lines of C++ code. Does PwT-C11 work at this scale?
Promising-ARM/RISC-V is a hardware memory model, that is, it is supposed to allow less behaviors comparing to programming language-level models like PwT-C11.
TODO: more on testing in our model.

# Reviewer B. Syntactic vs. semantic dependencies and their usage in compilers
Yes, tracking semantic dependencies is intrinsically harder than syntactic ones, and hardware memory models stick with syntax.
However, we cannot settle with syntactic dependencies for models of programming languages since common compiler optimizations
used in almost all real compilers (including GCC and Clang) may remove syntactic dependencies (unlike semantic ones).
That is, a programming language memory model which supports compiler optimizations and disallows OOTA (unlike the C/C++ memory model)
has to track semantic dependencies in one way or another. All other proposed solutions to this problem do that
(Promising [Kang-al:POPL17], Weakestmo [Chakraborty-Vafeiadis:POPL19], MRD [Paviotti-al:ESOP20], PwP [Jagadeesan-al:OOPSLA20]).
The point of the submission is to make the idea of tracking dependencies with logic, proposed by Jagadeesan et. al [2020],
to be compositional on the SEQ operator.
[MB -- the last sentence casts the motivation of the paper in a minimising way.]

Also, a compiler does not have to use the proposed semantics directly, i.e., for calculating dependencies.
Instead, the semantics has to be a wrapper over a reasonable set of compiler optimizations. That is, the optimizations
could make more conservative assumptions about dependencies than the semantics. This is what we are trying to achieve.

TODO: more here
