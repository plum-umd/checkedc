# Overview

We have uploaded the full version of the paper, which includes an
appendix. The final version of the paper will not have the appendix
but instead will cite a supplemental report.

For the reviewers' convenience we have included a diff between the
original and updated paper version at the end of the PDF. We hope this
will make it easier to see the changes made to the main body of the
paper.

# Major questions

## Formalization status of Theorem 4

Theorem 4, the simulation property, is formalized in PLT Redex, but not
proved; rather, we use randomized testing to give confidence that it
is correct. We don't have a pen and paper proof for it (and did
not claim that we did, in the text).

## Intended guarantee of Theorem 4

Simulation is intended to show that the use of fat pointers in
CoreChkC is not more expressive than a language that does not rely on
fat pointers, as is the expectation for the Checked C language.
The compilation procedure sheds light on how Checked C can be
compiled so as to not need fat pointers. The spatial safety property
is guaranteed by Theorem 3, the blame theorem, and is independent of
what simulation is trying to establish. 

## Undefinedness in code examples in Section IV

The target language of compilation, CoreC, is an untyped version of
CoreChkC, i.e., without metadata annotations. We did not intend to
design CoreC as a model of C or an intermediate language such as
LLVM IR. Rather, CoreC can be seen as a device for establishing the fact
that the more expressive semantics of CoreChkC (w.r.t the CheckedC
specification) does not require the use of fat pointers.  The
`deref_array` and `strlen` examples in Section IV (Figs 10-11) are
presented in C syntax to make them easier to understand. As such,
performing pointer arithmetic between a address-0 (null) pointer and a
non-zero integer is defined in CoreC even though it would not be in
actual C, as Reviewer C pointed out. To avoid confusion, we have
dropped type annotations in the examples and made them closer to
actual CoreC, including the use of relative bounds rather than
absolute ones.

## Dereferencing of (un)checked pointers in (un)checked regions

The ordering `u<c` is not a typo, it was the text that was wrong. In
particular, the condition in the rules enforces that unchecked
pointers cannot be used in checked regions; the reverse is
acceptable. 

Note that the blame theorem states that whenever the program gets
stuck, we can blame unchecked code. This does not necessarily mean we
always step into a stuck state from the unchecked region. Allowing
access to checked pointers in unchecked regions can allow unchecked
code to corrupt the addresses that checked pointers are assigned
to. The program can get stuck when we later access a corrupted checked pointer
in the checked region, but blame still holds, because the state would
not have been corrupted in the first place if there was no unchecked 
code to corrupt checked pointers. The theorem statements have been
tightened to make this apparent (and make them match the Coq model). 

## Discrepancies between the paper's calculus and the Coq formalization

We have added to the paper's supplemental report a dedicated section
that explains the differences between the paper's calculus and the Coq
formalization. For example, Coq syntactically distinguishes the `if`
form for potential ntarray widening and the plain `if` form for
everything else. We have also added a fair bit of extra detail to the
metatheory in Section III.

## Details on model-driven random testing

Our model driven testing approach follows the process recommended by
Pałka et al. [19]. We have added a couple of paragraphs to add more
details, and to clarify that this process is manual, not automatic.

# Other changes

We strived to take care of all of the requests made by the reviewers,
which can be see in the diff at the end of the PDF. Some notes about
specified requests below.

## Reviewer A

> clarify relationship between formalization and implementation

We have added a figure to section I that visualizes the relationship
between our contributions. We also added text to the end of 3.1 to
introduce the Coq and Redex models, and to explain some of their
differences and motivation. We have updated the abstract, conclusions,
and elsewhere to be clearer about what has been proved and what has
been tested.

> correct and address mistakes, typos, confusing terminology and code snippets

We have updated all of the examples. The `strcat` example has been
split into two figures, one in section 3 and one in seciton 4, and
renamed `safe_strcat` to make its intended semantics more clear
(thanks for the suggestion). The two examples intend to implement the
same functionaity, but differ according the semantics of bounds
widening; see the discussion at the end of Section IV-B.

> address pressing questions in the paper.

We have addressed the pressing questions as described in the main
response above, We have gone over all of the reviewer's comments and
attempted to address them; see the diff.

## Reviewer B

> Add details in section 5 (see above)

Done (see above).

> Clarify the status of Theorem 4

Done (see above). Per the reviewer's request, we have also added some
discussion about challenges in the proof, compared to Ruef et al. And
we have clarified the handling of null pointers in the formalism, and
some confusing details in the metatheory.

## Reviewer C

> confirmation that blame theorem issue is essentially just a typo.

Yes this was a typo. We fleshed out the metatheory section be more
precise.

> clarify the policy rules wrt accessing (un)checked pointers in
> (un)checked regions

See above.

> remove, or at least point out and justify the discrepancies between the Coq code and the paper, eg concerning Fig2

We added some discussion to the end of section 3.1 about both the Coq
and Redex models, and added a section to the Appendix about this.
