# Array inference

## Approach:

_Idea: Use abduction to infer possible bounds for pointers likely to be arrays._

1) Identify pointer variables that are potentially arrays. These
involve pointer arithmetic, or dereferencing with an index that is
non-zero. Our normal inference tool can identify these poitners, in
advance, before farming off to CRAB.

2) Perform inference locally, using abductive reasoning. In
particular, if we come across a dereference `p[e]` then for this access
to be safe requires that length(`p`) >= upperbound(`e`). We can look at
each access, generate constraints, and solve them. A solution might be
inconsistent in which case we can't learn the length, and we just
leave the pointer alone.

3) During solving we should consider contextual information. E.g., if
we had 
```
void foo(int *p, int len) {
  if (len > 2)
    p[2] = 3;
 }
```
then we shouldn't generally assume `p`'s length is at least 2; we
should only assume it if `len > 2`. Basically, this is an issue of
generalization; we want the most general bound. We could claim the
bound is (at least) 3 on `p` and that would allow `foo` to
typecheck. But we'd prefer to observe that `len > 2` when `p` is
accessed and thus `len >= 3` there, making it a suitable bound there,
and in general.

4) One question is how general bounds like the one for the example
above would actually be inferred. One possibility is to synthesize
possible predicates based on local syntax and put them in the code as
assertions, to be proved by CRAB. Unproved assertions are dropped. The
most general of the ones that remain are used for the bound.

For the above example, we could do
```
void foo(int *p, int len) {
  if (len > 2) {
    p[2] = 3; // infers that psize >= 2 if len > 2
  }
  assert(psize >= len);
  assert(psize >= 2); 
}
```
Here, psize is a ghost variable that represents `p`'s length (which
will be the annotation on the prototype). Neither assertion is
disproven by the context, but the first assertion should be preferred
because it does not rely on constants. This would yield the rewriting
```
void foo(Array_ptr<int> p : count(len), int len) {
  if (len > 2) {
    p[2] = 3; // infers that psize >= 2 if len > 2
  }
}
```

### Complications:

1) This approach is not guaranteed to produce code that the Checked C
type checker will like. This is because it is synthesizing local
constraints which might be violated globally. As an example, suppose
we have
```
void bar(void) {
  int x[2];
  foo(x,2);
}
void foo(int *p, int len) { ... } // as above
```
Now if we inferred that `p` should be annotated as having `count(3)`
(rather than `count(len)` which is better) them the call in `bar` will
fail the type checker since the given pointer `x` has length 2. If we
had chosen the more appropriate length it wouldn't have failed.

Ideally we attempt to figure out these cases during inference and
revert the pointer to an unchecked one. This idea might be a general
basis for an approach; more below.

2) Aliasing: p is an alias of q, and p is used to dereference at a
non-zero index. Hence, q is as well.

3) Pointer arithmetic: If we have a loop that iterates p via pointer
arithmetic, we need to pick bounds for p that are "constant" even as
the arithmetic takes place. Aliasing makes it worse: If we perform
pointer arithmetic on p, which is an alias of q, how will that fact
reflect back when determining q's length?

## Alternative idea

An alternative approach would be to involve the Checked C type checker
more directly. That is, rather than use CRAB to figure out what sizes
might be, we could instead synthesize possible sizes, add them in, and
then run the type checker. If it fails, we try a different size. If we
run out of options, we give up and leave the pointer as unchecked.

Synthesizing the sizes could come from lexical context, as described
above. The difference is that we are relying on the Checked C type
checker, rather than CRAB, to vet them.

Doing this interprocedurally is challenging, though, for the same
reasons it is for the main idea, above.
