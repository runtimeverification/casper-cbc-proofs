# Casper CBC Proofs

[![coqdoc][coqdoc-shield]][coqdoc-link]

[coqdoc-shield]: https://img.shields.io/badge/docs-coqdoc-blue.svg
[coqdoc-link]: https://runtimeverification.github.io/casper-cbc-proof-docs/docs/latest/coqdoc/toc.html

Protocol verification of Casper Correct-By-Construction in Coq.

## Meta

- License: [University of Illinois/NCSA Open Source License](LICENSE.md)
- Compatible Coq versions: 8.11 or later
- Coq namespace: `CasperCBC`

## Building instructions

``` shell
git clone https://github.com/runtimeverification/casper-cbc-proofs.git
cd casper-cbc-proofs
make   # or make -j <number-of-cores-on-your-machine>
```

## Structure

- `Lib`: various extensions to the Coq standard library
- `CBC`: Formalizizations for FullNode and LightNode protocols
  specified in https://github.com/ethereum/cbc-casper
- `VLSM`: Formalization of Vlad Zamfir's new, composable, model
  used for stating and solving consensus problems.

See also the latest [online documentation][coqdoc-link] of the Coq files.

[coqdoc-link]: https://runtimeverification.github.io/casper-cbc-proof-docs/docs/latest/coqdoc/toc.html
