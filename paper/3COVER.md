> 1. Please add a claim about your Coq formalisation to your paper, and make
> your Coq proof scripts accessible. We noticed a couple of `Admitted' lemmas
> in your Coq proof scripts; these must be discharged before the paper can be
> accepted.

Admitted lemmas are removed.  We reference the Coq formalization at the end
of §1 and before Lemma 3.5.

> 2. Add more explanation about the broader context of your work,
> particularly with regard to semantic dependencies, along the lines given at
> the beginning of your response.

We have integrated this into §1.

> 3. Add more explanation about why a denotational semantics for weak
> sequential composition is challenging and worthwhile, along the lines given
> in your response about why the continuation S_0 is problematic both
> theoretically and practically, and why it causes problems for things like
> reasoning about system calls, etc.

We have integrated this into §1.

> 4. Bring more comparisons with PwP and promising semantics from the
> appendices (and from your response) into the main body of the paper. (I'm
> assuming the authors are in a position to buy a couple more pages as
> necessary.) It may not be worth bringing in all the details, but we expect
> at least a high-level summary of the material in those appendices.

We have added this to related work, now §9.

> 5. Clarify how the model can be used in compiler development, along the
> lines of the argument given in the response about how compiler-writers need
> not engage directly with this semantics, but can use more conservative
> models instead.

We have integrated this into §1.
We also added a comment after Lemma 3.7

> 6. Discuss the scalability challenges of your model, along the lines given
> at the end of your response.

We have integrated this into §7.

> 7. Fix/clarify the issues raised in Review A's "Presentation issues and
> typos", Review B's "Detailed comments", and Review C's line-by-line
> remarks, as appropriate. In particular, we strongly urge you not to
> abbreviate \tau^E as \tau, as it has confused multiple reviewers.

We have adopted all of your suggestions, with only one exception: We continue
to use "termination condition" rather than "completion condition", as
suggested.  Termination is necessary for completion, not sufficient, as the
change of terminology might imply.

