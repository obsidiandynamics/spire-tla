---- MODULE SpireModel ----
(*****************************************************************************)
(* Extension of the base `Spire' module to facilitate bounded model          *)
(* checking of its safety property.                                          *)
(*****************************************************************************)
EXTENDS Spire, TLC, FiniteSets, Randomization, Sequences

CONSTANTS MaxRounds     \* an upper bound on `Rounds'

\* A finite set of rounds, required for bounded model checking.
FiniteRounds == 0..MaxRounds

\* Model symmetry across consenters and proposed values.
Symmetry == Permutations(Consenters) \union Permutations(Values)
----
(*****************************************************************************)
(* Additional invariants useful for model checking.                          *)
(*****************************************************************************)

(*****************************************************************************)
(* In any given round, at most one value may be primed.                      *)
(*****************************************************************************)
SingularPrimedPerRound ==
    \A r \in Rounds :
        LET primedAnswers == {m \in msgs : m.type = "Answer" /\ m.lastRound = r /\ m.lastPrimed}
        IN  ~\E m1, m2 \in primedAnswers : m1.lastVal # m2.lastVal
----
(*****************************************************************************)
(* A fully-inductive specification.                                          *)
(*****************************************************************************)
ISpec == Inv /\ [][Next]_vars
----
(*****************************************************************************)
(* Use of random sampling to reduce the number of initial states in the      *)
(* checking of an inductive invariant. This technique is outlined in         *)
(* Lamport's 2018 paper 'Using TLC to Check Inductive Invariance'.           *)                                
(*****************************************************************************)
CArg == 10000000    \* upper bound on `|msgs|'
PArg == 2           \* `PArg / |Messages|' is probability of including an element of `Messages` in a subset

RECURSIVE BoundedPowerOfTwo(_)
BoundedPowerOfTwo(p) ==
    IF p > 30 THEN 2147483647
    ELSE IF p = 0 THEN 1
    ELSE 2 * BoundedPowerOfTwo(p - 1)
PowersetCardinality(M) == BoundedPowerOfTwo(Cardinality(M))
Min(a, b) == IF a < b THEN a ELSE b
RInv == 
    LET powersetCardinality == PowersetCardinality(Messages)
        randomSubsets == RandomSetOfSubsets(Min(CArg, powersetCardinality), PArg, Messages)
    IN  /\  PrintT("Powerset cardinality: " \o ToString(powersetCardinality))
        /\  PrintT("Message cardinality: " \o ToString(Cardinality(Messages)))
        /\  PrintT("Random subsets: " \o ToString(Cardinality(randomSubsets)))
        /\  msgs \in randomSubsets
        /\  MsgInv
        /\  lastVal \in [Consenters -> Values \union {None}]
        /\  lastRound \in [Consenters -> Rounds \union {-1}]
        /\  lastPrimed \in [Consenters -> BOOLEAN]
        /\  ConsInv
RSpec == RInv /\ [][Next]_vars
====