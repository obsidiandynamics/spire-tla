---- MODULE SPX ----
EXTENDS Integers, TLC

CONSTANTS 
    Proposers,
    Commands

VARIABLES
    forwarded,      \* `forwarded[p]' is a set of forwarded commands for proposer `p'
    proposals,      \* `proposals[s]' is a set of pending proposals for slot `s' 
    committed       \* `committed[s]' is the committed value for slot `s'

vars == <<forwarded, proposals, committed>>

Slots == Nat

\* A finite set of slots, required for bounded model checking.
FiniteSlots == 0..1

Values == Commands \X Proposers

\* ValidForwarded == forwarded \in [Proposers -> Commands]
\* ValidProposals == proposals \in [Slots -> SUBSET Values]
\* ValidCommitted == proposals \in [Slots -> Values]
ValidForwarded == \A p \in DOMAIN forwarded : forwarded[p] \in Commands
ValidProposals == \A s \in DOMAIN proposals : proposals[s] \in SUBSET Values
ValidCommitted == \A s \in DOMAIN committed : committed[s] \in Values

TypeOK ==
    ValidForwarded \/ ValidProposals \/ ValidCommitted

(*****************************************************************************)
(* Selects the maximum value in a set.                                       *)
(*****************************************************************************)
SetMax(S) == CHOOSE t \in S : \A s \in S : t >= s

HighestProposed == 
    IF DOMAIN proposals # {} THEN SetMax(DOMAIN proposals) ELSE -1

HighestCommitted ==
    IF DOMAIN committed # {} THEN SetMax(DOMAIN committed) ELSE -1

\* HighestStarted == 
\*     LET highestProposed == HighestProposed
\*     IN  IF highestProposed # -1 THEN highestProposed ELSE HighestCommitted

TrySubmitProposal(s, v) ==
    /\  s \notin DOMAIN committed
    /\  IF s \in DOMAIN proposals THEN 
            /\  v \notin proposals[s]
            /\  proposals' = [proposals EXCEPT ![s] = @ \union {s}]
        ELSE 
            proposals' = proposals @@ s :> {v}

ClearProposals(s) ==
    proposals' = [t \in DOMAIN proposals \ {s} |-> proposals[t]]

CommitValue(s, v) ==
    committed' = committed @@ s :> {v}

Consensus(s) ==
    /\  LET chosen == CHOOSE p \in proposals[s] : TRUE
        IN  /\  ClearProposals(s)
            /\  CommitValue(s, chosen)
    /\  UNCHANGED <<forwarded>>

ProposeLocal(p) ==
    /\  LET highestProposed == HighestProposed
        IN  IF highestProposed # -1 THEN
                \E c \in Commands :
                    TrySubmitProposal(highestProposed, <<c, p>>)
            ELSE 
                LET nextVacant == HighestCommitted + 1
                IN  /\  nextVacant \in Slots
                    /\  \E c \in Commands :
                            TrySubmitProposal(nextVacant, <<c, p>>)
    /\  UNCHANGED <<forwarded, committed>>

Init ==
    /\  forwarded = <<>>
    /\  proposals = <<>>
    /\  committed = <<>>

Terminated ==
    /\  ~   \/  \E s \in DOMAIN proposals : ENABLED Consensus(s)
            \/  \E p \in Proposers : 
                    \/  ENABLED ProposeLocal(p)
    /\  UNCHANGED vars

Next ==
    \/  \E s \in DOMAIN proposals : Consensus(s)
    \/  \E p \in Proposers : 
            \/  ProposeLocal(p)
    \/  Terminated

Spec == Init /\ [][Next]_vars
====