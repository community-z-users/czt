# CZT interface to Z/EVES

The CZT interface to Z/EVES theorem prover provides a bi-directional link to the Z/EVES prover
process via CZT.

The project provides a CZT abstraction layer to communicate with Z/EVES process. The actual
communication is socket-based and uses Z/EVES XML API to send and receive messages. This project
provides the communications library and can support different UIs to drive the Z/EVES prover.

## Features

Some of the features provided by CZT to Z/EVES interface:

-   Start, stop and otherwise control Z/EVES process.
-   Receive messages from Z/EVES prover and read them to CZT ASTs using Z/EVES dialect.
-   Send commands to Z/EVES prover (translate CZT ASTs to Z/EVES XML).
-   Query Z/EVES prover state.
-   CZT representation of Z/EVES prover state.
-   Support for custom Z/EVES tactics using existing tactic commands.
