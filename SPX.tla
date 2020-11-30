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
FiniteSlots == 1..2

Values == Commands \X Proposers

ValidForwarded == \A p \in DOMAIN forwarded : forwarded[p] \in Commands
ValidProposals == \A s \in DOMAIN proposals : proposals[s] \in SUBSET Values
ValidCommitted == \A s \in DOMAIN committed : committed[s] \in Values

TypeOK ==
    ValidForwarded \/ ValidProposals \/ ValidCommitted

GapFreeLog ==
    \A s \in DOMAIN committed :
        s # 1 => s - 1 \in DOMAIN committed

(*****************************************************************************)
(* Selects the maximum value in a set.                                       *)
(*****************************************************************************)
SetMax(S) == CHOOSE t \in S : \A s \in S : t >= s

HighestProposed == 
    IF DOMAIN proposals # {} THEN SetMax(DOMAIN proposals) ELSE 0

HighestCommitted ==
    IF DOMAIN committed # {} THEN SetMax(DOMAIN committed) ELSE 0

TrySubmitProposal(s, v) ==
    /\  s \notin DOMAIN committed
    /\  IF s \in DOMAIN proposals THEN 
            /\  v \notin proposals[s]
            /\  proposals' = [proposals EXCEPT ![s] = @ \union {v}]
        ELSE 
            proposals' = proposals @@ s :> {v}

ClearProposals(s) ==
    proposals' = [t \in DOMAIN proposals \ {s} |-> proposals[t]]

CommitValue(s, v) ==
    committed' = committed @@ s :> v

Consensus(s) ==
    /\  s \in DOMAIN proposals
    /\  LET chosen == CHOOSE p \in proposals[s] : TRUE
        IN  /\  ClearProposals(s)
            /\  CommitValue(s, chosen)
    /\  UNCHANGED <<forwarded>>

TryForwardCommand(p, c) ==
    IF p \notin DOMAIN forwarded THEN
        forwarded' = forwarded @@ p :> {c}
    ELSE
        /\  c \notin forwarded[p]
        /\  forwarded' = [forwarded EXCEPT ![p] = @ \union {c}]

ProposeLocal(p) ==
    /\  LET highestProposed == HighestProposed
        IN  IF highestProposed # 0 THEN
                \E c \in Commands :
                    TrySubmitProposal(highestProposed, <<c, p>>)
            ELSE 
                LET nextVacant == HighestCommitted + 1
                IN  /\  nextVacant \in Slots
                    /\  \E c \in Commands :
                            TrySubmitProposal(nextVacant, <<c, p>>)
    /\  UNCHANGED <<forwarded, committed>>

ProposeForwarded(p) ==
    /\  p \in DOMAIN forwarded
    /\  LET command == CHOOSE c \in forwarded[p] : TRUE
            highestCommitted == HighestCommitted
        IN  /\  highestCommitted # 0
            /\  highestCommitted + 1 \in Slots
            /\  committed[highestCommitted][2] = p
            /\  TrySubmitProposal(highestCommitted + 1, <<command, p>>)
    /\  UNCHANGED <<forwarded, committed>>

ForwardToPrivileged(p) ==
    /\  \E c \in Commands :
            TryForwardCommand(p, c)
    /\  UNCHANGED <<proposals, committed>>

Init ==
    /\  forwarded = <<>>
    /\  proposals = <<>>
    /\  committed = <<>>

Terminated ==
    /\  ~   \/  \E s \in Slots : ENABLED Consensus(s)
            \/  \E p \in Proposers : 
                    \/  ENABLED ProposeLocal(p)
                    \/  ENABLED ForwardToPrivileged(p)
                    \/  ENABLED ProposeForwarded(p)
    /\  UNCHANGED vars

Next ==
    \/  \E s \in Slots : Consensus(s)
    \/  \E p \in Proposers : 
            \/  ProposeLocal(p)
            \/  ForwardToPrivileged(p)
            \/  ProposeForwarded(p)
    \/  Terminated

Spec == Init /\ [][Next]_vars
====