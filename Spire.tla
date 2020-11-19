---- MODULE Spire ----
(*****************************************************************************)
(* A TLA⁺ specification of the Spire consensus protocol.                     *)
(*****************************************************************************)
EXTENDS Integers

CONSTANTS Consenters,   \* `Consenters' is a set of consenter nodes.
          Values,       \* `Values' is a set of proposed values
          Quorums       \* `Quorums' is a set of quorums, where each element is a set of
                        \* consenters

\* All quorums must be within the powerset of consenters and all quorums must
\* intersect.
ASSUME QuorumAssumption == 
    /\  Quorums \subseteq SUBSET Consenters
    /\  \A Q1, Q2 \in Quorums : Q1 \intersect Q2 # {}  

Rounds == Nat

VARIABLES msgs,         \* `msgs' comprises the history of all messages sent by proposers and consenters
          lastRound,    \* `lastRound[c]' is the last round accepted by a consenter
          lastVal,      \* `lastVal[c]' is the last value accepted by a consenter
          lastPrimed    \* `lastPrimed[c]' states whether the last accepted value was primed

vars == <<msgs, lastRound, lastVal, lastPrimed>>

\* `None' represents the absence of a value.
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
MaxLastRound(M) ==
    SetMax({m.lastRound : m \in M})
AllIdenticalRounds(M) == 
    /\  ~\E m1, m2 \in M : m1.lastRound # m2.lastRound
AllPrimed(M) == 
    /\  \A m \in M : m.lastPrimed
PickValue(M) ==
    LET someAnswer == CHOOSE m \in M : TRUE
    IN  someAnswer.lastVal
PickRound(M) ==
    LET someAnswer == CHOOSE m \in M : TRUE
    IN  someAnswer.lastRound
SuccessorValues(M) ==
    LET highestRound == MaxLastRound(M)
        highestRoundAnswers == {m \in M : m.lastRound = highestRound}
        highestRoundPrimedAnswers == {m \in highestRoundAnswers : m.lastPrimed}
    IN  IF highestRoundPrimedAnswers # {} THEN
            {PickValue(highestRoundPrimedAnswers)}
        ELSE
            {a.lastVal : a \in highestRoundAnswers}
AllIdenticalValues(M) ==
    ~\E m1, m2 \in M : m1.lastVal # m2.lastVal

Init == 
    /\  msgs = {}
    /\  lastRound = [c \in Consenters |-> -1]
    /\  lastVal = [c \in Consenters |-> None]
    /\  lastPrimed = [c \in Consenters |-> FALSE]

Offer ==
    /\  \/  \E Q \in Quorums : \E A \in QuorumAnswers(Q) :
                IF AllIdenticalRounds(A) THEN
                    IF AllPrimed(A) THEN
                        FALSE
                    ELSE IF AllIdenticalValues(A) THEN
                        LET nextRound == PickRound(A) + 1
                        IN  /\  nextRound \in Rounds
                            /\  TrySend([type |-> "Offer", val |-> PickValue(A), round |-> nextRound, primed |-> TRUE])
                    ELSE 
                        LET nextRound == PickRound(A) + 1
                        IN  /\  nextRound \in Rounds
                            /\  \E v \in SuccessorValues(A) :
                                    TrySend([type |-> "Offer", val |-> v, round |-> nextRound, primed |-> FALSE])
                ELSE
                    \E v \in SuccessorValues(A) :
                        TrySend([type |-> "Offer", val |-> v, round |-> MaxLastRound(A), primed |-> FALSE])
        \/  \E v \in Values :
                TrySend([type |-> "Offer", val |-> v, round |-> 0, primed |-> FALSE])
    /\  UNCHANGED <<lastRound, lastVal, lastPrimed>>

Answer(c) ==
    \E m \in msgs : 
        /\  m.type = "Offer"
        /\  m.round > lastRound[c]
        /\  lastRound' = [lastRound EXCEPT ![c] = m.round]
        /\  lastVal' = [lastVal EXCEPT ![c] = m.val]
        /\  lastPrimed' = [lastPrimed EXCEPT ![c] = m.primed]
        /\  Send([type |-> "Answer", cons |-> c, lastVal |-> m.val, lastRound |-> m.round, lastPrimed |-> m.primed])

Decided ==
    /\  \E Q \in Quorums : \E A \in QuorumAnswers(Q) : AllIdenticalRounds(A) /\ AllPrimed(A)
    /\  UNCHANGED vars
    
Terminated ==
    /\  ~   \/  ENABLED Offer
            \/  \E c \in Consenters : ENABLED Answer(c)
            \/  ENABLED Decided
    /\  UNCHANGED vars

Next == 
    \/  Offer 
    \/  \E c \in Consenters : Answer(c)
    \/  Decided
    \/  Terminated

Spec == Init /\ [][Next]_vars

Messages == 
    [type : {"Offer"}, val : Values, round : Rounds, primed : BOOLEAN] \union
    [type : {"Answer"}, cons : Consenters, lastVal : Values, lastRound : Rounds, lastPrimed : BOOLEAN]
        
TypeOK == 
    /\  msgs \in SUBSET Messages
    /\  lastVal \in [Consenters -> Values \union {None}]
    /\  lastRound \in [Consenters -> Rounds \union {-1}]
    /\  lastPrimed \in [Consenters -> BOOLEAN]

Chosen(v) ==
    \E Q \in Quorums :
        \E A \in QuorumAnswers(Q) :
            /\  AllIdenticalRounds(A) 
            /\  AllPrimed(A)
            /\  \E m \in A : m.lastVal = v

Consistency ==
    \A v1, v2 \in Values : Chosen(v1) /\ Chosen(v2) => v1 = v2

----
MsgInv ==
    \A m \in msgs :
        /\  m.type = "Offer" =>
                /\  m.round = 0 => ~m.primed
                /\  m.round # 0 =>
                        /\ m.primed => 
                            \E Q \in Quorums : \E A \in QuorumAnswers(Q) :
                                /\  AllIdenticalRounds(A) /\ AllIdenticalValues(A)
                                /\  m.val = PickValue(A)
                                /\  m.round = PickRound(A) + 1
                        /\ ~m.primed =>
                            \E Q \in Quorums : \E A \in QuorumAnswers(Q) :
                                /\  AllIdenticalRounds(A)
                                /\  m.val \in SuccessorValues(A)
                                /\  m.round = PickRound(A) + 1
        /\  m.type = "Answer" =>
                \E o \in msgs : 
                      /\  o.type = "Offer"
                      /\  o.round = m.lastRound
                      /\  o.val = m.lastVal
                      /\  o.primed = m.lastPrimed

ConsInv ==
    \A c \in Consenters :
        /\  lastRound[c] = -1 <=> lastVal[c] = None
        /\  lastRound[c] = -1 => ~lastPrimed[c]
        /\  lastRound[c] # -1 => \E m \in msgs : 
                /\  m.type = "Answer" 
                /\  m.cons = c 
                /\  m.lastRound = lastRound[c]
                /\  m.lastVal = lastVal[c]
                /\  m.lastPrimed = lastPrimed[c]
        \* no answer may exist for a round above lastRound[c]
        /\  ~\E m \in msgs : m.type = "Answer" /\ m.cons = c /\ m.lastRound > lastRound[c]
        \* a consenter answers at most once for any given lastRound
        /\  \A m1, m2 \in msgs :
                m1.type = "Answer" /\ m2.type = "Answer" /\ m1.cons = c /\ m2.cons = c /\ m1.lastRound = m2.lastRound => m1 = m2

Inv == 
    /\  msgs \in SUBSET Messages
    /\  MsgInv
    /\  lastVal \in [Consenters -> Values \union {None}]
    /\  lastRound \in [Consenters -> Rounds \union {-1}]
    /\  lastPrimed \in [Consenters -> BOOLEAN]
    /\  ConsInv
====