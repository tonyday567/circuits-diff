# numhask-diff

Reverse-mode automatic differentiation carrier for the NumHask ecosystem.

`NumHask.Diff` provides `Diff' p a b` — a smooth function `a -> b` bundled
with its pullback `b -> a` — with NumHask instances that turn NumHask-
polymorphic code into differentiable code.

This package was extracted from `numhask-free` when `numhask` 0.14 absorbed
the free term algebras; `Diff` is a carrier/functorial lift, not a free term
algebra, so it lives in its own home.
