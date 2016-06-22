# `choose` Your Own Derivative

Code for the submitted TyDe '16 extended abstract "`choose` Your Own
Derivative".

## Compilation instructions

Download and install the [stack] tool if you don't have it, then run the
commands `stack setup` and `stack build` command in this directory.

This code requires GHC 8.  (You can skip `stack setup` if you already have GHC 8
installed.)

[stack]: http://haskellstack.org

## Files

* `Derivatives.hs`: Implementing the derivative operators at the type level.
* `Constraints.hs`: Value-level manipulation of Haskell constraints, and proofs
  about contexts.
* `SType.hs`: Singleton types for faking true dependent types.
* `Value.hs`: A uniform representation for values.
* `Locations.hs`: The `locations` function (see §3).
* `Choose.hs`: The `choose` function for `IO`.
* `Compat.hs`: GHC 8 support.

## Examples

In the `examples/` directory, we include some code that postulates
(instantiations of) `choose` to demonstrate what our library will be able to do
when the generic implementation of `choose` is completed.  (The instantiations
of `choose` are stubbed out with `undefined`.)

These files compile with GHC 7.10 or GHC 8.

* `Async.hs`: A reimplementation of some operations from the Haskell [`async`]
  library.
* `Timeout.hs`: An implementation of the `timout` operation in terms of `choose`
  and `Async.hs`.

[`async`]: https://hackage.haskell.org/package/async
