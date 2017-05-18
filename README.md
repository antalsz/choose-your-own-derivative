# `choose` Your Own Derivative

Code for the submitted TyDe '16 extended abstract and C∘mp∘se '17 talk "`choose`
Your Own Derivative".

## Compilation instructions

Download and install the [stack] tool if you don't have it, then run the
commands `stack setup` and `stack build` command in this directory.

This code requires GHC 8.  (You can skip `stack setup` if you already have GHC 8
installed.)

[stack]: http://haskellstack.org

## Files

* `Choose.hs`: Toplevel interface to selective choice and implementation for IO.
* `Constraints.hs`: Value-level manipulation of Haskell constraints, and proofs
  about contexts.
* `Derivatives.hs`: Implementing the derivative operators at the type level.
* `Equiv.hs`: Equivalence of contexts.
* `Locations.hs`: The `locations` function used in the implementation of
  `choose`.
* `NFI.hs`: The `NotFreeIn` relation.
* `Pretty.hs`: Pretty printing.
* `ToFM.hs`: Converting from Haskell types to FMTypes using type classes (not
  generics)
* `Types.hs`: Type-level representation of FMTypes.
* `examples/Timeout.hs`: A simple timeout example.

These files compile with GHC 7.10 or GHC 8.

[`async`]: https://hackage.haskell.org/package/async
