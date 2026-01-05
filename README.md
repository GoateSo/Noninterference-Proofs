# Introduction

This repository contains the Rocq definitions and proofs associated with the equivalence between the knowledge based and hyperproperty based definitions of progress sensitive noninterference, progress sensitive noninterference, and leakage free progress. 

A specification outline for both sets of security definitions are stated within an attached latex document, and are respectively adapted from definitions used by the papers "A Semantic Framework for Declassification and Endorsement" authored by Aslan Askarov & Andrew Myer, and "Nonmalleable Progress Leakage" authored by Ethan Cecchetti. The style of this project and summary is based off of the rocq archive accompanying the latter. In addition, the document also outlines the major proofs presented in the rocq code.

## Definition and Notational differences

- There's a slight difference in the usage of "trace" between the rocq code and in the definitions section of the latex outline. In the latex file, the terms trace and trace prefix refer to streams/lists of events respectively. In rocq, they refer to event stream/lists paired with the corresponding input store (the document refers to this as a store, trace pair).
- Specific details for the definitions of D-equivalence for traces and erasure (and the associated silence predicate) are left out of the outline as they are borrowed directly from "Nonmalleable Progress Leakage".
- The notable facts listed are represented as derived results in the code, with trace prefix maximization being a consequence of the language definition in the rocq code and indistinguishability for traces being derived from its definition in "Nonmalleable Progress Leakage".

# Building and checking Rocq proofs

Building and checking the proofs requires the following software:

* coqc, version 8.18 or later (see [the official Rocq downloads page](https://rocq-prover.org/releases))\* 
* coq_makefile (available the same place as coqc, see [below](#compiling) for differences if using rocq)
* make (the standard unix/linux utility)


*Latest version compiled for rocq (version 9.1.0) as opposed to coqc, which moves streams from `List.Streams` to `Streams.Streams`. If using a coq version, change this at the top of `rocq/theories/TraceTheories.v` 
## Compiling

To compile the archive, first generate a Makefile using the following command:
    `coq_makefile -f _CoqProject -o Makefile` or if using rocq: 
    `rocq makefile -f _CoqProject -o Makefile`.

Then build the definitions and proofs by simply running `make`. If you encounter an error related to `Streams`, see the [asterisk](#building-and-checking-rocq-proofs) in the previous section.

## Auditing the Proofs

Definitions are in the `rocq/definitions` directory organized as follows.
* The applicable family of languages are defined in `rocq/definitions/Lang.v`
* Coinductive encodings of traces and trace equivalence are defined in `rocq/definitions/Trace.v`
* A generalized definition of the determinism constraint is specified under `rocq/definitions/Determinism.v`
* The definitions of low-equivalence, knowledge, and both sets of security definitions as specified above are defined in `rocq/definitions/SecurityDefs.v`.

Proofs are in the `rocq/theories` directory. Most files primarily consist of intermediate lemmas, with the core equivalence results contained in:
* `rocq/theories/Psni.v`, which proves equivalence for progress sensitive noninterference
* `rocq/theories/LFP.v`, which proves equivalence for leakage free progress
* `rocq/theories/Pini.v`, which proves equivalence for progress insensitive noninterference. 