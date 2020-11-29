---- MODULE SpireLive ----
(*****************************************************************************)
(* Extension of the base `Spire' module to facilitate bounded model          *)
(* checking of its liveness property.                                        *)
(*****************************************************************************)
EXTENDS Spire, TLC

CONSTANTS MaxRound     \* an upper bound on `Rounds'

\* A finite set of rounds, required for bounded model checking.
FiniteRounds == 0..MaxRound
----
(*****************************************************************************)
(* Eventually, either a value is chosen or the bounded model runs out of     *)
(* round numbers.                                                            *)
(*****************************************************************************)
TemporalProperties ==
    <>[](ENABLED Decided \/ ENABLED Terminated)

FairSpec == Spec /\ WF_vars(Next)
====