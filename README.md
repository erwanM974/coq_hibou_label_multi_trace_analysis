# Coq proof for a multi-trace analysis algorithm

This repository hosts a proof written in the Gallina language.
We use the Coq automated theorem prover to prove the correctness of an algorithm which analyze multi-traces (sets of distributed logs) against specifications of distributed systems written in the form of interaction models (formal models that can be represented graphically in the manner of Message Sequence Charts or UML Sequence Diagrams). This proof of correctness corresponds to proving that the algorithm returns "Pass" whenever the multi-trace belongs to the semantics of the interaction model and "Fail" otherwise.

This proof accompanies a paper, published in the proceedings of the 36th Annual ACM Symposium on Applied Computing:
- [A small-step approach to multi-trace checking against interactions](https://dl.acm.org/doi/abs/10.1145/3412841.3442054)

A web page (generated with coqdoc) presenting the proof can be accessed [here](https://erwanm974.github.io/coq_hibou_label_multi_trace_analysis/).

A tool, which implements and extends upon this multi-trace analysis algorithm is available on [this repository](https://github.com/erwanM974/hibou_label).
