---- MODULE Spire ----
(*****************************************************************************)
(* A TLA⁺ specification of the Spire consensus protocol.                     *)
(*****************************************************************************)
EXTENDS Integers

CONSTANTS Consenters,   \* `Consenters' is a set of consenter nodes
          Values,       \* `Values' is a set of proposed values
          Quorums       \* `Quorums' is a set of quorums, where each element is a set of
                        \* consenters

(*****************************************************************************)
(* All quorums must be within the powerset of consenters and all quorums     *)
(* must intersect.                                                           *)
(*****************************************************************************)
ASSUME QuorumAssumption == 
    /\  Quorums \subseteq SUBSET Consenters
    /\  \A Q1, Q2 \in Quorums : Q1 \intersect Q2 # {}  

Rounds == Nat           \* override with a finite set when model checking

VARIABLES msgs,         \* `msgs' comprises the history of all messages sent by proposers and consenters
          lastRound,    \* `lastRound[c]' is the last round accepted by a consenter
          lastVal,      \* `lastVal[c]' is the last value accepted by a consenter
          lastPrimed    \* `lastPrimed[c]' states whether the last accepted value was primed

vars == <<msgs, lastRound, lastVal, lastPrimed>>

(*****************************************************************************)
(* `None' represents the absence of a value.                                 *)
(*****************************************************************************)
None == CHOOSE v : v \notin Values

(*****************************************************************************)
(* Send a message `m' by appending it to the `msgs' history.                 *)
(*****************************************************************************)
Send(m) == msgs' = msgs \union {m}

(*****************************************************************************)
(* Conditionally send a message `m' if `m' is not already in the history.    *)
(*****************************************************************************)
TrySend(m) == m \notin msgs /\ Send(m)

(*****************************************************************************)
(* Filter all answers in `msgs' where the consenter is among `C'.            *)
(*****************************************************************************)
Answers(C) == 
    {m \in msgs : m.type = "Answer" /\ m.cons \in C}
        
(*****************************************************************************)
(* A superset of all unique answer sets, where the individual answers in     *)
(* each of the underlying sets `A' originate from the consenters in `Q', and *)
(* for every consenter `c' in `Q', there is precisely one answer in `A' that *)
(* originates from `c'.                                                      *)
(*                                                                           *)
(* Assuming that a proposer queries a fixed quorum of consenters, this       *)
(* operator is used to obtain the superset of all possible answer sets that  *)
(* the proposer might observe with respect to the queried consenters, which  *)
(* is consistent with the consenters' message histories.                     *)
(*                                                                           *)
(* A notable characteristic of this operator is that                         *)
(* `|QuorumAnswers(Q)| = |Q|'.                                               *)
(*****************************************************************************)
QuorumAnswers(Q) == 
    {A \in SUBSET Answers(Q) : \A c \in Q : 
        /\ \E m \in A : m.cons = c
        /\ \A m1, m2 \in A : m1.cons = m2.cons => m1 = m2}

(*****************************************************************************)
(* Selects the maximum value in a set.                                       *)
(*****************************************************************************)
SetMax(S) == CHOOSE t \in S : \A s \in S : t >= s

(*****************************************************************************)
(* The highest round appearing in a set of answers `M'.                      *)
(*****************************************************************************)
MaxLastRound(M) ==
    SetMax({m.lastRound : m \in M})

(*****************************************************************************)
(* Whether all answers in `M' feature identical round numbers.               *)
(*****************************************************************************)
AllIdenticalRounds(M) == 
    ~\E m1, m2 \in M : m1.lastRound # m2.lastRound

(*****************************************************************************)
(* Whether all answers in `M' encompass the same value.                      *)
(*****************************************************************************)
AllIdenticalValues(M) ==
    ~\E m1, m2 \in M : m1.lastVal # m2.lastVal

(*****************************************************************************)
(* Whether all answers in `M' are primed.                                    *)
(*****************************************************************************)
AllPrimed(M) == 
    \A m \in M : m.lastPrimed

(*****************************************************************************)
(* Selects an arbitrary value from the answers in `M'. It is assumed that    *)
(* there is at least one message in `M' and all answers contain identical    *)
(* values, therefore the choice of answer is irrelevant.                     *)
(*****************************************************************************)
PickValue(M) ==
    LET someAnswer == CHOOSE m \in M : TRUE
    IN  someAnswer.lastVal

(*****************************************************************************)
(* Selects an arbitrary round from the answers in `M'. It is assumed that    *)
(* there is at least one message in `M' and all answers contain identical    *)
(* rounds, therefore the choice of answer is irrelevant.                     *)
(*****************************************************************************)
PickRound(M) ==
    LET someAnswer == CHOOSE m \in M : TRUE
    IN  someAnswer.lastRound

(*****************************************************************************)
(* A set of allowed successor values from the answers in `M', assuming that  *)
(* `M' has at least one message.                                             *)
(*                                                                           *)
(* The algorithm for determining the successors is as follows:               *)
(*                                                                           *)
(* 1. Identify the highest round number among the answers in `M'.            *)
(*                                                                           *)
(* 2. Select a subset of answers from the highest round.                     *)
(*                                                                           *)
(* 3. Of the subset in (2), select those answers that are primed.            *)
(*                                                                           *)
(* 4. If (3) yields primed answers in the highest round, then return a       *)
(* singleton set containing the sole primed value. There may be at           *)
(* most one distinct primed value in a given round, therefore the returned   *)
(* set is deterministic.                                                     *)
(*                                                                           *)
(* 5. Otherwise, if (3) locates no primed answers, then return the set of    *)
(* highest round values filtered from (2). The successor is among those      *)
(* values.                                                                   *)
(*****************************************************************************)
SuccessorValues(M) ==
    LET highestRound == MaxLastRound(M)
        highestRoundAnswers == {m \in M : m.lastRound = highestRound}
        highestRoundPrimedAnswers == {m \in highestRoundAnswers : m.lastPrimed}
    IN  IF highestRoundPrimedAnswers # {} THEN
            {PickValue(highestRoundPrimedAnswers)}
        ELSE
            {a.lastVal : a \in highestRoundAnswers}

(*****************************************************************************)
(* The initial state predicate.                                              *)
(*****************************************************************************)
Init == 
    /\  msgs = {}
    /\  lastRound = [c \in Consenters |-> -1]
    /\  lastVal = [c \in Consenters |-> None]
    /\  lastPrimed = [c \in Consenters |-> FALSE]

(*****************************************************************************)
(* The next-state relation specifying a proposer's actions, submitting an    *)
(* offer on the basis of prior quorum-answers (if they exist), or an         *)
(* initial (round-0) offer containing an arbitrarily chosen value if no      *)
(* prior quorum-answer has been observed.                                    *)
(*                                                                           *)
(* Offers are submitted by appending to the message history variable `msgs'  *)
(* so any consenter may observe and answer any offer.                        *)
(*****************************************************************************)
Offer ==
    /\  \/  \E Q \in Quorums : \E A \in QuorumAnswers(Q) :
                IF AllIdenticalRounds(A) THEN
                    IF AllPrimed(A) THEN
                        FALSE
                    ELSE IF AllIdenticalValues(A) THEN
                        LET nextRound == PickRound(A) + 1
                        IN  /\  nextRound \in Rounds
                            /\  TrySend([type |-> "Offer", val |-> PickValue(A), 
                                         round |-> nextRound, primed |-> TRUE])
                    ELSE 
                        LET nextRound == PickRound(A) + 1
                        IN  /\  nextRound \in Rounds
                            /\  \E v \in SuccessorValues(A) :
                                    TrySend([type |-> "Offer", val |-> v, 
                                             round |-> nextRound, primed |-> FALSE])
                ELSE
                    \E v \in SuccessorValues(A) :
                        TrySend([type |-> "Offer", val |-> v, round |-> MaxLastRound(A), primed |-> FALSE])
        \/  \E v \in Values :
                TrySend([type |-> "Offer", val |-> v, round |-> 0, primed |-> FALSE])
    /\  UNCHANGED <<lastRound, lastVal, lastPrimed>>

(*****************************************************************************)
(* The next-state relation specifying a consenter's actions, responding to a *)
(* prior offer while ensuring that the consenter does not vote more than     *)
(* once in a given round.                                                    *)
(*                                                                           *)
(* This consenter behaviour corresponds to the Spire/RM (round-monotonic)    *)
(* variation, where a consenter does not vote in a round if it has already   *)
(* voted in a higher round.                                                  *)
(*****************************************************************************)
Answer(c) ==
    \E m \in msgs : 
        /\  m.type = "Offer"
        /\  m.round > lastRound[c]
        /\  lastRound' = [lastRound EXCEPT ![c] = m.round]
        /\  lastVal' = [lastVal EXCEPT ![c] = m.val]
        /\  lastPrimed' = [lastPrimed EXCEPT ![c] = m.primed]
        /\  Send([type |-> "Answer", cons |-> c, lastVal |-> m.val, 
                  lastRound |-> m.round, lastPrimed |-> m.primed])

(*****************************************************************************)
(* A special 'marker' state that signifies that a value has been chosen.     *)
(* This is determined by an existence of a primed uniform quorum-answer,     *)
(* i.e. where all answers are primed and bear an identical round number.     *)
(*                                                                           *)
(* This pseudo-action has no bearing on the operation of the algorithm; it   *)
(* has been added to conveniently highlight that consensus has been reached  *)
(* when model checking safety and liveness properties. This action does not  *)
(* change any variables and removing it has no adverse effect.               *)
(*****************************************************************************)
Decided ==
    /\  \E Q \in Quorums : \E A \in QuorumAnswers(Q) : AllIdenticalRounds(A) /\ AllPrimed(A)
    /\  UNCHANGED vars

(*****************************************************************************)
(* A special 'marker' state that signifies that the algorithm has            *)
(* terminated due to the exhaustion of the allowed round numbers. It is      *)
(* useful for bounded model checking (where `Rounds' is replaced with a      *)
(* finite set).                                                              *)
(*                                                                           *)
(* This pseudo-action has no bearing on the operation of the algorithm,      *)
(* other than to prevent TLC from flagging a deadlock due to the absence     *)
(* of a viable next-state action. This action does not                       *)
(* change any variables and removing it has no adverse effect.               *)
(*****************************************************************************)    
Terminated ==
    /\  ~   \/  ENABLED Offer
            \/  \E c \in Consenters : ENABLED Answer(c)
            \/  ENABLED Decided
    /\  UNCHANGED vars

(*****************************************************************************)
(* The canonical combined next-state action.                                 *)
(*****************************************************************************)
Next == 
    \/  Offer 
    \/  \E c \in Consenters : Answer(c)
    \/  Decided
    \/  Terminated

(*****************************************************************************)
(* The canonical specification.                                              *)
(*****************************************************************************)
Spec == Init /\ [][Next]_vars

(*****************************************************************************)
(* The invariant constraining all messages in `msg'.                         *)
(*****************************************************************************)
Messages == 
    [type : {"Offer"}, val : Values, round : Rounds, primed : BOOLEAN] \union
    [type : {"Answer"}, cons : Consenters, lastVal : Values, lastRound : Rounds, lastPrimed : BOOLEAN]

(*****************************************************************************)
(* The complete type-correctness invariant.                                  *)
(*****************************************************************************)        
TypeOK == 
    /\  msgs \in SUBSET Messages
    /\  lastVal \in [Consenters -> Values \union {None}]
    /\  lastRound \in [Consenters -> Rounds \union {-1}]
    /\  lastPrimed \in [Consenters -> BOOLEAN]

(*****************************************************************************)
(* Whether the given value `v' has been chosen within the current message    *)
(* history.                                                                  *)
(*****************************************************************************)
Chosen(v) ==
    \E Q \in Quorums :
        \E A \in QuorumAnswers(Q) :
            /\  AllIdenticalRounds(A) 
            /\  AllPrimed(A)
            /\  \E m \in A : m.lastVal = v

(*****************************************************************************)
(* The main consistency invariant, stating that no run of the consensus      *)
(* algorithm may arrive at two distinct chosen values. It doesn't imply      *)
(* that a value is chosen, only that once a value is chosen, no other        *)
(* value may be chosen.                                                      *)
(*****************************************************************************)
Consistency ==
    \A v1, v2 \in Values : Chosen(v1) /\ Chosen(v2) => v1 = v2
----
(*****************************************************************************)
(* Aspects of the inductive invariant that constrain the relationships       *)
(* between offers and answers within the message history variable `msgs'.    *)
(*****************************************************************************)
MsgInv ==
    \A m \in msgs :
        /\  m.type = "Offer" =>
                \* The only constraint on a round-0 offer is that it must 
                \* be unprimed.
                /\  m.round = 0 => ~m.primed
                /\  m.round # 0 =>
                        \* Round 1+ offers must ensure that only a value that has been
                        \* voted for in round `r' may be offered in `r + 1'. We call
                        \* this property 'value propagation'.
                        /\ m.primed =>
                            \* A round 1+ offer may be primed only if it comes
                            \* as a result of a uniform quorum-answer in the
                            \* preceding round. I.e. all consenters in some
                            \* quorum have voted for the same value in the
                            \* same round, and that round immediately precedes
                            \* this offer. This directly implies value propagation
                            \* for primed offers.
                            \E Q \in Quorums : \E A \in QuorumAnswers(Q) :
                                /\  AllIdenticalRounds(A) /\ AllIdenticalValues(A)
                                /\  m.val = PickValue(A)
                                /\  m.round = PickRound(A) + 1
                        /\ ~m.primed =>
                            \* A round 1+ offer may be unprimed only if there exists
                            \* quorum-answer in the preceding round bearing a value
                            \* that has been offered.
                            \*
                            \* The `Offer' next-state permission permits an unprimed
                            \* offer to originate from a current-round answer, if the
                            \* quorum-answer chosen by a proposer spans multiple rounds.
                            \* This may initially appear to be more relaxed than the
                            \* inductive invariant. We could have commensurately 
                            \* relaxed the inductive invariant, which would then require
                            \* us to prove that it satisfies value propagation in those
                            \* cases where the offer relates to the current-round answer.
                            \* 
                            \* Rather, we assert that any current-round answer must 
                            \* have directly or indirectly originated
                            \* from the immediately preceding round. By strengthening
                            \* the inductive invariant, we avoid having to prove the
                            \* value propagation property using finite set induction. Instead,
                            \* the subsequent proof demonstrates that all offers satisfy the
                            \* stronger inductive invariant property, while the 
                            \* strengthened inductive invariant satisfies
                            \* value propagation without resorting to finite set induction.
                            \*
                            \* As a result, the proof of the `Inv => Consistency' lemma
                            \* is significantly simplified at the expense of the 
                            \* `Inv /\ Next => Inv'' lemma proof, which becomes marginally more
                            \* involved for the mixed-round case of the `Offer' next-state
                            \* relation.
                            \E Q \in Quorums : \E A \in QuorumAnswers(Q) :
                                /\  AllIdenticalRounds(A)
                                /\  m.val \in SuccessorValues(A)
                                /\  m.round = PickRound(A) + 1
        /\  m.type = "Answer" =>
                \* For any answer, there must be a corresponding offer in the same round,
                \* bearing the same value and primed status.
                \E o \in msgs : 
                      /\  o.type = "Offer"
                      /\  o.round = m.lastRound
                      /\  o.val = m.lastVal
                      /\  o.primed = m.lastPrimed

(*****************************************************************************)
(* Aspects of the inductive invariant that constrain consenter variables and *)
(* the affinity of consenters with votes.                                    *)
(*****************************************************************************)
ConsInv ==
    \A c \in Consenters :
        \*  `lastRound[c]' can be set to `-1' if and only if `lastVal[c]' is `None'.
        /\  lastRound[c] = -1 <=> lastVal[c] = None
        \*  `lastPrimed[c]' must be `FALSE' if `lastRound[c]' is in its initial state.
        /\  lastRound[c] = -1 => ~lastPrimed[c]
        \*  If `lastRound[c]' is set (which implies that a consenter has voted),
        \*  then there should be an answer to that effect.
        /\  lastRound[c] # -1 => \E m \in msgs : 
                /\  m.type = "Answer" 
                /\  m.cons = c 
                /\  m.lastRound = lastRound[c]
                /\  m.lastVal = lastVal[c]
                /\  m.lastPrimed = lastPrimed[c]
        \*  No answer may exist for a round above `lastRound[c]'.
        /\  ~\E m \in msgs : m.type = "Answer" /\ m.cons = c /\ m.lastRound > lastRound[c]
        \*  A consenter votes at most once in any given round.
        /\  \A m1, m2 \in msgs :
                m1.type = "Answer" /\ m2.type = "Answer" /\ m1.cons = c /\ m2.cons = c /\
                m1.lastRound = m2.lastRound 
                    => m1 = m2

(*****************************************************************************)
(* The complete inductive invariant.                                         *)
(*                                                                           *)
(* The conjuncts of the type-correctness invariant otherwise defined by      *)
(* `TypeOK' have been                                                        *)
(* interleaved among the conjuncts of `Inv' as per the technique outlined    *)
(* in Lamport's 2018 paper 'Using TLC to Check Inductive Invariance'. This   *)
(* approach drastically reduces the number of raw states that TLC has        *)
(* to enumerate before applying the inductive constraints `MsgInv' and       *)
(* `ConsInv'.                                                                *)     
(*****************************************************************************)   
Inv == 
    /\  msgs \in SUBSET Messages
    /\  MsgInv
    /\  lastVal \in [Consenters -> Values \union {None}]
    /\  lastRound \in [Consenters -> Rounds \union {-1}]
    /\  lastPrimed \in [Consenters -> BOOLEAN]
    /\  ConsInv
====