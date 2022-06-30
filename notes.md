not positive

```coq
Inductive position (p: term): Set :=
| root
| child: match p with
  | #n => Empty_set
  | \q => position q
  | $ q r => position q + position r
  end -> position p
.
```

can't match

```coq
Fixpoint position (p: term): Type :=
  option match p with
  | #n => Empty_set (* To match a leaf just use None *)
  | \q => position q
  | $ q r => position q + position r
  end
.
```
