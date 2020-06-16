# casper-cbc-proofs
Repo for protocol verification of Casper Correct-By-Construction

# Requirements

* `Coq`: a relatively recent version

# Structure

* `Lib`: various extensions to the Coq standard library
* `CBC`: Formalizizations for FullNode and LightNode protocols
  specified in https://github.com/ethereum/cbc-casper
* `VLSM`: Formalization of Vlad Zamfir's new, composable, model
   used for stating and solving consensus problems.

# Building

To build and run the proof scripts for the main results, run

```
make
```

from the main directory.
