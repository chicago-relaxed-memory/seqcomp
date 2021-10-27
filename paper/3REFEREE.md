POPL 2022 Paper #459 Reviews and Comments
===========================================================================
Paper #459 The Leaky Semicolon: Compositional Semantic Dependencies for
Relaxed-Memory Concurrency


Review #459A
===========================================================================

Overall merit
-------------
C. Weak Reject

Reviewer expertise
------------------
Y. Knowledgeable

Paper summary
-------------

This paper proposes pomsets with predicate transformers (PwT), a new
denotational model for relaxed-memory concurrency. PwT is built on pomsets
with preconditions (PwP) proposed by Jagadeesan et al [OOPSLA 2020]. The key
feature of PwT is that the denotation of sequential composition (S_1; S_2) is
computed from the denotations of S_1 and S_2. The paper presents two versions
of PwT for multicopy-atomic (MCA) architectures such as Arm8, and a version
for C11. There is also a tool to automatically check whether an outcome is
allowed for a litmus test.

Strengths
---------

1) In PwT, the denotational semantics of sequential composition is
compositional and associative. This looks beautiful as a denotational model.

2) PwT has been applied to both MCA and C11 models.

Weaknesses
----------

1) The technical challenge is not clearly explained.  Why is it challenging
to give a denotational semantics to sequential composition?

2) It is unclear how to know the "correctness" of PwT.  Appendix A.2 mentions
that PwP has some errors. I'm wondering how the authors ensure that PwT does
not have errors.

3) The paper is a bit dense. It lists a lot of definitions, but does not give
much explanation on the intuition.

Comments for author
-------------------

1) It is difficult for me to understand the challenges in giving a proper
denotational semantics to sequential composition. The paper says that in
earlier works [Paviotti et al 2020, Jagadeesan et al 2020], "adding an event
requires perfect knowledge of the future" (l63), but it is unclear to me why
they *require* knowledge of the future. In other words, if they do not have
perfect knowledge of the future, what will be wrong?

    Sec 2.3 explains the reasons why [Jagadeesan et al 2020] requires
    knowledge of the future as folows:

    > their model uses prefixing, which requires that the model is built from
      right to left

    But it is still unclear to me why it is challenging to drop the
    requirement of "prefixing".

    Sec 2.3 also shows an example: 

    > For example, Jagadeesan et al. state the equivalence allowing
    > reordering independent writes as follows, [[x := M; y := N; S]] = [[y
    > := N; x := M; S]] if x <> y

    But it is unclear to me why S cannot be removed. Apparently, S can be
    arbitrary in this equivalence (since there are no constraints on S), and
    hence removing S should not affect the equivalence.

    Sec 3 says that [Paviotti et al 2020] gives the semantics of sequential
    composition in continuation passing style. Why is it challenging to turn
    the semantics to a "direct style"?

    Besides, I'm wondering why adding predicate transformers to PwP is
    crucial for addressing the challenges. Is the idea of predicate
    transformers also necessary for defining prefixing in PwP? If not, what
    makes the idea of predicate transformers necessary for general sequential
    composition? Why can the approach of predicate transformers address the
    challenges?
	
    Due to the above issues, I am not convinced that this work makes a strong
    theoretical contribution.

2) To enhance the confidence in the correctness of a new model, in addition
to testing, one may also want to formally prove the equivalence between the
new model and the existing ones. Appendix A.2 says that PwP has some errors,
so it seems that PwT is not a conservative extension of PwP.  That is,
[[S]]_PwT may not be equivalent to [[S]]_PwP for some program S written in
the language of PwP. However, I am still wondering about a formal
relationship between PwT and PwP. It is even unclear to me whether the set of
events and the preconditions in [[S]]_PwT are the same as those in
[[S]]_PwP. Is there any theorem formally showing the relationship between PwT
and PwP?

    From Fig 1, I see that the precondition of an event in S_2 might be
    changed when S_2 is sequentially after some S_1 (see (s3b)). In order to
    know the precondition of an event e, one has to know the predicate
    transformer for the events "before" e. Does this mean that the
    precondition of an event cannot be locally determined? Then, what is the
    meaning of the precondition of an event in PwT? Is its meaning the same
    as in PwP?

    Besides, I am also wondering how PwT-C11 is related to MRD-C11 [Paviotti
    et al 2020]. Is there any theorem formally showing the equivalence
    between PwT-C11 and MRD-C11?

3) Presentation issues and typos: 

- l377. It seems that \tau^{\downarrow e} has the type \Phi -> \Phi, the same
  as \tau in Definition 4.2. This is a bit confusing, since the type of the
  symbol \tau in \tau^{\downarrow e} is no longer \Phi -> \Phi. Please
  clarify. In addition, what is d < e?

- Fig 1. Please explain why (R4b) is defined in this way. In addition, why
  can the set E of events be empty for read and write operations?

- l534. Should (W5) be (W4)?

- l685. Why should associativity hold for incomplete pomsets? 

- It is difficult to understand the last paragraph of Sec 4. The paragraph
  says that the attempt to define predicate transformers using substitution
  fails because (\forall r)\psi does not distribute through disjunction. I
  don't understand how substitution is related to (\forall r)\psi.

- l702. What does "optimal lowering" mean? 

- It is difficult to understand Definition 7.1. In particular, please explain
  the intuition of \pi, e.g. what it represents, why it is necessary, and why
  it is defined in this way.

- l952. I didn't see the definition of PwT-C11. How is it related to PwT-PO?

- l1223. is ubiquitous is -> is ubiquitous in



Review #459B
===========================================================================

Overall merit
-------------
C. Weak Reject

Reviewer expertise
------------------
X. Expert

Paper summary
-------------

This paper proposes a relaxed memory model that supports sequential
composition while flexible enough for hardware design. It combines Pomsets
with families of predicate transformers. The authors demonstrate how their
methods can be used on various MCA hardware models and C11. The authors
develop a prototype tool to evaluate litmus tests.

Strengths
---------

* The roadmap of this work, Pomsets with Preconditions + predicate
  transformer sets, separates itself from most existing relaxed memory models
  and can have a big impact if proved useful.

* This work contributes to the important discussion of fixing OOTA behavior
  in the C11 memory model.

Weaknesses
----------

* The paper is difficult to approach due to relatively poor presentation.

* I am doubtful whether the proposed memory model can work beyond simple
  litmus tests and whether it is practical in real hardware and compiler
  design.

Comments for author
-------------------

This work is built on the idea that, according to Jagadeesan et al. [2020],
“logic is better than syntax to capture dependencies”. This is a very
interesting direction. My major concern is that syntactic dependencies are
easier to analyze for compilers and easier to implement for processors. On
the other hand, to analyze logical/arithmetic dependencies, more information
has to be tracked along execution paths, and operators like remainder can
pose a challenge. By proposing predicate transformers tuned for relaxed
memory, this work alleviates the problem but still does not solve it.

I would be more convinced if the authors can test their model on slightly
larger pieces of code beyond litmus tests. For example, Promising-ARM/RISC-V
[Pulte et al. 2019] is evaluated on a concurrent queue implemented in 215
lines of C++ code. Does PwT-c11 work at this scale?

In terms of paper writing, Section 4 and 5 are too dense with definitions and
proofs. I get lost multiple times. I would suggest in Section 2 you give one
example concurrent program, one valid behavior, and one invalid
behavior. Then use your methods to run through the example and show why they
are valid/invalid.

If the problems can be solved, I think this can be good work. I skipped some
definitions and all proofs, but they look reasonable. PwT-C11 looks like a
better solution than RC11 for OOTA behaviors. This can potentially make a
real impact.

Detailed comments:

* Section 2.2, the authors should point out all memory locations are
  initialized with zero. Otherwise, the examples (especially out-of-thin-air)
  do not hold.

* Page 3 bottom, the blue arrow is not defined. Same with the dashed line on
  Page 5.

* Please define “pomsets” in the Overview.

* The links in Sections 4 and 5 pose a lot of pain. For example, at Line 552,
  one has to scroll back and forth twice. This makes hard-to-understand texts
  even harder. Eventually, I gave up on the formal model and read exclusively
  the later examples, which, thanks to the authors, are mostly
  understandable.

* Page 11, “In a complete pomset, c3 requires that every precondition k(e) is
  a tautology.” This is crucial in understanding how your model works and
  should be stated much earlier.

* Section 4.6, the authors should emphasize that example separates your
  semantic dependency model from the syntactic dependency models widely used
  today.

* What is $\pi^{-1}$ in Lemma 5.3?

* Section 8 is extremely short. Have the authors tested PwTer on any
  benchmarks? How many programs have been tested? I would like to see some
  runtime numbers here, especially for larger code. I think the authors would
  agree their memory model is more complicated than most existing ones. So
  some experiments are needed to ensure the overhead is acceptable.

* In the Conclusion, “efficiently compiled to modern CPUs” is not
  demonstrated in the paper.



Review #459C
===========================================================================

Overall merit
-------------
B. Weak Accept

Reviewer expertise
------------------
X. Expert

Paper summary
-------------

This paper presents a denotational semantics for weak-memory concurrency that
supports _both_ of the following things for the first time:
(1) semantic dependencies (rather than just syntactic overapproximations), and
(2) sequential composition (where previous works that supported (1) only
managed "prefixing").

The semantics is based on "pomsets with predicate transformers". Executions
are represented as pomsets, whose vertices represent events. Each vertex is
associated with a precondition; these preconditions are discharged by earlier
read events as the executions are "built up"; an execution for a complete
program should have "true" for all of its preconditions. Each vertex is also
associated with a set of predicate transformers. When executions are
sequentially composed, the appropriate predicate transformer is picked
according to which events are causal precedents.

The semantics is instantiated to two versions of Armv8 with slightly
different tradeoffs in terms of which compiler optimisations are validated,
and also a version for C11. A prototype tool for exploring the model will be
open-sourced upon publication.

Strengths
---------

- Skillfully and engagingly written paper. Barely any typos.

- The model is quite complicated but also kinda makes sense. It's not obvious
  to me that it could be much simpler.

- Very much on topic for POPL -- this is very much a paper that engages with
  _principles_ of programming languages.

Weaknesses
----------

- The key motivator for the work is to extend "pomsets with preconditions"
  (Jagadeesan et al. OOPSLA 2020) from "prefixing" to general sequential
  composition. The advantage of sequential composition is that equivalences
  like `[x:=M;y:=N;S] = [y:=N;x:=M;S]` can become `[x:=M;y:=N] =
  [y:=N;x:=M]`. My worry is: is this a big enough "win" to be worth all this
  effort?

- I felt that there were a few gaps in the explanations, which I've tried to
  point out below. These are easily fixed though.

- Not mechanised in a theorem prover, which isn't a disaster on its
  own... but I did notice that the appendix refers to an error made in a
  similar recent paper that also wasn't mechanised (Jagadeesan et al. OOPSLA
  2020) where a stated result doesn't actually hold. So I think it's fair to
  say that confidence in the results would be increased if the model were
  mechanised.

Comments for author
-------------------

This is a very appealing paper and I enjoyed reading it. Here are some
remarks...

1: The title is quite amusing, with the play on "leaky colon".

85: "Introductory programmers" doesn't make sense. (Perhaps you are thinking
of "introductory programming courses"?) I suggest "Novice".

126: I think "extends naturally" would read slightly better.

132: I think it would be worth clarifying that this execution is just one of
many possible executions. (This is in contrast to the program on line 123
which only has one execution.)

145: The blue arrow hasn't been explained.

169: The parentheses are italicised but their contents aren't -- looks odd.

170: Around here I think it would be good to have a couple of sentences
giving the intuition about how these preconditions work. I mean, the reader
may be trying to imagine "executing" one of your pomsets -- so, what do I do
when I meet a precondition? If the precondition is false do I come back to
that event later or just throw it away?

171: You mention data dependencies and control dependencies here; am I to
understand that the example on line 174 has both a data dependency (r*s = 0)
_and_ a control dependency (s < 1)? If so, would be good to clarify.

179: There's a case for making the vertical bar fill the entire height of the
TikZ node. It would help clarify the precedence between `==>` and `|`, for
instance.

203: "pomset" -> "vertex in the pomset" ?

240: "sanity check" is a slightly old-fashioned term these days.

244: Would help if this graph used the same layout as the one on line 238.

284: "thin-air free" -> "thin-air-free"

316: You want a `\citet` here. (And in a few other places too.)

319: "syntax sugar" -> "syntactic sugar"

327: I suggest dropping the $=\{...\}$ here because it's really weird until
you read the appendix and realise that you're mapping events to
registers. Just say that there's a set of registers that do not appear in
programs.

380: I wasn't sure why it's $D \subseteq \mathcal E$ here not $D \subseteq
E$.

381: I think abbreviating $\tau^E$ as $\tau$ is a bad idea. Yes you save a
bit of ink but the confusion is a high price to pay -- see how (M4) gives the
type of $\tau$ and then (M5a) immediately seems to violate that type because
it uses the abbreviation.

402: Remind the reader here that you're not including parallel composition
and fences.

407: I struggled with the concept of a "termination condition". Can you add a
sentence or two of intuition here? I wonder: what if you renamed it to
"completion condition"? Once it's met, the pomset is deemed "complete". That
would unify your terminology a bit, right? By the way, I note that PwP
doesn't use these termination conditions, and there's no explanation in the
paper of why this part of the model has changed, even in the appendix --
could you add it?

423: Item (c) has been lost. And items (i) and (j) could be combined into a
single line if you want.

Fig 1: I reckon you could probably merge (S3a) and (S3b) and (S3c)
together. If I read it right, the only reason for splitting them up is to
make sure that you don't call $\kappa_1$ or $\kappa_2$ outside of their
domains of definition. But if you just arrange that $\kappa(e)$ is $false$ if
$e$ is not in $E$, then everything should just work, no? Then you can just
have (S3): $\kappa(e) = \kappa_1(e) \vee \kappa_2(e)$, I think?

494: This seems wrong: you're saying that [x:=1] is not a non-strict superset
of [if(M){x:=1}]. But they're surely equal if M is true?

500: "be become" -> "become"

515: "true" -> "taken" ("true branch" connotes "then branch" for me)

547: "example" -> "example,"

614: "CPU" doesn't really need small-caps.

620: Notation suggestion: how about ${<}e$ instead of $\downarrow e$? That
would be consistent with line 354.

670: Dodgy kerning around the bang.

700: Not sure you defined the "MCA" acronym.

701: You might clarify what "lowering" means.

705: This could be clearer about how the models are different. _How_ exactly
are the models different when a thread reads its own write?

722: (P4) looks weird to me. Why doesn't $\tau_2$ feature here?

817: Should $c'$ be $c$?

852: "It's" -> "Its"

1163: I'm not too sure what "If-closure" means exactly. Could you clarify?



Shepard
===========================================================================

Dear authors, congratulations on the conditional acceptance of your
paper. Please find below the revisions that the reviewers require.

1. Please add a claim about your Coq formalisation to your paper, and make
your Coq proof scripts accessible. We noticed a couple of `Admitted' lemmas
in your Coq proof scripts; these must be discharged before the paper can be
accepted.

2. Add more explanation about the broader context of your work, particularly
with regard to semantic dependencies, along the lines given at the beginning
of your response.

3. Add more explanation about why a denotational semantics for weak
sequential composition is challenging and worthwhile, along the lines given
in your response about why the continuation S_0 is problematic both
theoretically and practically, and why it causes problems for things like
reasoning about system calls, etc.

4. Bring more comparisons with PwP and promising semantics from the
appendices (and from your response) into the main body of the paper. (I'm
assuming the authors are in a position to buy a couple more pages as
necessary.) It may not be worth bringing in all the details, but we expect at
least a high-level summary of the material in those appendices.

5. Clarify how the model can be used in compiler development, along the lines
of the argument given in the response about how compiler-writers need not
engage directly with this semantics, but can use more conservative models
instead.

6. Discuss the scalability challenges of your model, along the lines given at
the end of your response.

7. Fix/clarify the issues raised in Review A's "Presentation issues and
typos", Review B's "Detailed comments", and Review C's line-by-line remarks,
as appropriate. In particular, we strongly urge you not to abbreviate
\tau^E as \tau, as it has confused multiple reviewers.