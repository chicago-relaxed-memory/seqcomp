We are thankful to reviewers for their work.

# Reviewer A. Why is it challenging to give a denotational semantics to sequential composition?
TODO

# Reviewers A and C. Correctness of the model, mechanization, relation to other models
We agree that the model is complicated and requires formal results to be sure in its correctness,
that is why we have been working on its mechanization.
Currently, we have mechanized in Coq Lemma 4.5 from the paper
(associativity of sequential composition and SKIP being left and right ids for sequential composition).

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
