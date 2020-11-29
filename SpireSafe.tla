---- MODULE SpireSafe ----
(*****************************************************************************)
(* Extension of the base `Spire' module to facilitate bounded model          *)
(* checking of its safety property.                                          *)
(*****************************************************************************)
EXTENDS Spire, TLC, FiniteSets, Randomization, Sequences

CONSTANTS MaxRound     \* an upper bound on `Rounds'

\* A finite set of rounds, required for bounded model checking.
FiniteRounds == 0..MaxRound

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

(*****************************************************************************)
(* If `v' was chosen in some round `s', then there must be an earlier        *)
(* round `r', such that `v' was accepted by a complete quorum in `r' and     *)
(* none of the offers for that quorum were primed in `r'.                    *)
(*****************************************************************************)
ChosenRequiresEarlierUnprimedOffers ==
    \A v \in Values : \A s \in Rounds : 
        /\  \E Q \in Quorums : \E A \in QuorumAnswers(Q) :
                \A a \in A : a.lastPrimed /\ a.lastRound = s /\ a.lastVal = v
        =>  \E r \in Rounds : r < s /\ \E R \in Quorums : \E B \in QuorumAnswers(R) :
                \A b \in B : ~b.lastPrimed /\ b.lastRound = r /\ b.lastVal = v

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
PArg == 2           \* `PArg / |Messages|' is probability of including an element of `Messages' in a subset

(*****************************************************************************)
(* Prevents integer overflow when computing an answer to `2^p' by capping    *)
(* the result.                                                               *)
(*****************************************************************************)
RECURSIVE BoundedPowerOfTwo(_)
BoundedPowerOfTwo(p) ==
    IF p > 30 THEN 2147483647
    ELSE IF p = 0 THEN 1
    ELSE 2 * BoundedPowerOfTwo(p - 1)

(*****************************************************************************)
(* Returns an integer that is at most as large as the cardinality of the     *)
(* powerset of `M'. For small `|M|', the value is `2^|M|' as expected.       *)
(* As `|M|' increases, the result is capped to avoid integer overflow.       *)
(*****************************************************************************)
PowersetCardinality(M) == BoundedPowerOfTwo(Cardinality(M))
Min(a, b) == IF a < b THEN a ELSE b

(*****************************************************************************)
(* A stricter variant of the `Inv' inductive invariant, where the            *)
(* type-correctness predicate for `msgs' has been restricted to a random     *)
(* set of the subsets of `Messages'.                                         *)
(*****************************************************************************)
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