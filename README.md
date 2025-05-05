# Library of verified programs in Stainless and Dafny

Collection of verified software using Dafny and Stainles. Each program has two versions, one with each tool.

## Main differences

- In **Dafny**, methods cannot be called in specifications. You can indeed only call functions. This makes the translation from Stainless a bit tricky in some instances. Indeed, in the cases where we call some functions in specifications, that have to be translated to a Dafny method, this causes a problem.
- In Dafny, we cannot have class invariants. We have to rely on an invariant function we call in all other specifications as pre- and postconditions.