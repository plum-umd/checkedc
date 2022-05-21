```coq
| SPlusNull : forall s R n1 t n2,
    n1 <= 0 -> is_check_array_ptr t ->
    step D F
      (s, R) (EPlus (ELit n1 t) (ELit n2 (TNat)))
      (s, R) RNull
```

Why would a arrayptr < 0?
