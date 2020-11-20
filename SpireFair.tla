---- MODULE SpireFair ----
(*****************************************************************************)
(* Extension of the base `Spire' module to facilitate bounded model          *)
(* checking of its liveness property.                                        *)
(*****************************************************************************)
EXTENDS Spire, TLC

CONSTANTS MaxRounds     \* an upper bound on `Rounds'

\* A finite set of rounds, required for bounded model checking.
FiniteRounds == 0..MaxRounds
----
TemporalProperties ==
    <>[](ENABLED Decided \/ ENABLED Terminated)

FairSpec == Spec /\ WF_vars(Next)
====