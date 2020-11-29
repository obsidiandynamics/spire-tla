---- MODULE SPX ----
EXTENDS Integers, TLC, FiniteSets

CONSTANTS 
    Proposers,
    Commands

VARIABLES
    forwarded,      \* `forwarded[p]' is a set of forwarded commands for proposer `p'
    proposals,      \* `proposals[s]' is a set of pending proposals for slot `s' 
    committed,      \* `committed[s]' is the committed value for slot `s'
    usedPrivileges  \* `usedPrivileges[p]' is the set of slot-usedPrivileges used by proposer `p'

vars == <<forwarded, proposals, committed, usedPrivileges>>

Slots == Nat

\* A finite set of slots, required for bounded model checking.
FiniteSlots == 1..2

(*****************************************************************************)
(* Invariants.                                                               *)
(*****************************************************************************)

Values == Commands \X Proposers
Proposals == [val: Values, priv: BOOLEAN]

ValidForwarded == 
    /\  DOMAIN forwarded \in SUBSET Proposers
    /\  \A p \in DOMAIN forwarded : forwarded[p] \in SUBSET Commands
ValidProposals == 
    /\  DOMAIN proposals \in SUBSET Slots
    /\  \A s \in DOMAIN proposals : proposals[s] \in SUBSET Proposals
ValidCommitted ==
    /\  DOMAIN committed \in SUBSET Slots
    /\  \A s \in DOMAIN committed : committed[s] \in Values
ValidUsedPrivileges == 
    /\  DOMAIN usedPrivileges \in SUBSET Proposers
    /\  \A s \in DOMAIN usedPrivileges : usedPrivileges[s] \in SUBSET Slots

TypeOK ==
    ValidForwarded /\ ValidProposals /\ ValidCommitted /\ ValidUsedPrivileges

GapFreeLog ==
    \A s \in DOMAIN committed :
        s # 1 => s - 1 \in DOMAIN committed

SingularityOfPrivilege ==
    \A s \in DOMAIN proposals :
        Cardinality({p \in proposals[s] : p.priv}) <= 1

(*****************************************************************************)
(* Selects the maximum value in a set.                                       *)
(*****************************************************************************)
SetMax(S) == CHOOSE t \in S : \A s \in S : t >= s

HighestProposed == 
    IF DOMAIN proposals # {} THEN SetMax(DOMAIN proposals) ELSE 0

HighestCommitted ==
    IF DOMAIN committed # {} THEN SetMax(DOMAIN committed) ELSE 0

TrySubmitProposal(s, p, v, privileged) ==
    LET proposal == [val |-> v, priv |-> privileged]
    IN  /\  s \notin DOMAIN committed
        /\  IF s \in DOMAIN proposals THEN 
                /\  proposal \notin proposals[s]
                /\  proposals' = [proposals EXCEPT ![s] = @ \union {proposal}]
            ELSE 
                proposals' = proposals @@ s :> {proposal}

ClearProposals(s) ==
    proposals' = [t \in DOMAIN proposals \ {s} |-> proposals[t]]

CommitValue(s, v) ==
    committed' = committed @@ s :> v

Consensus(s) ==
    /\  s \in DOMAIN proposals
    /\  LET chosen == CHOOSE p \in proposals[s] : TRUE
        IN  /\  ClearProposals(s)
            /\  CommitValue(s, chosen.val)
    /\  UNCHANGED <<forwarded, usedPrivileges>>

TryUsePrivilege(s, p) ==
    IF p \in DOMAIN usedPrivileges THEN
        /\  s \notin usedPrivileges[p]
        /\  usedPrivileges' = [usedPrivileges EXCEPT ![p] = @ \union {s}]
    ELSE
        usedPrivileges' = usedPrivileges @@ p :> {s}

TryForwardCommand(p, c) ==
    IF p \notin DOMAIN forwarded THEN
        forwarded' = forwarded @@ p :> {c}
    ELSE
        /\  c \notin forwarded[p]
        /\  forwarded' = [forwarded EXCEPT ![p] = @ \union {c}]

PromoteSelf(p) ==
    /\  LET highestProposed == HighestProposed
        IN  IF highestProposed # 0 THEN
                \E c \in Commands :
                    TrySubmitProposal(highestProposed, p, <<c, p>>, FALSE)
            ELSE 
                LET nextVacant == HighestCommitted + 1
                IN  /\  nextVacant \in Slots
                    /\  \E c \in Commands :
                            TrySubmitProposal(nextVacant, p, <<c, p>>, FALSE)
    /\  UNCHANGED <<forwarded, committed, usedPrivileges>>

ProposeForwarded(p) ==
    /\  p \in DOMAIN forwarded
    /\  LET command == CHOOSE c \in forwarded[p] : TRUE
            highestCommitted == HighestCommitted
        IN  /\  highestCommitted # 0
            /\  highestCommitted + 1 \in Slots
            /\  committed[highestCommitted][2] = p
            /\  TryUsePrivilege(highestCommitted + 1, p)
            /\  TrySubmitProposal(highestCommitted + 1, p, <<command, p>>, TRUE)
    /\  UNCHANGED <<forwarded, committed>>

ForwardToPrivileged(p) ==
    /\  \E c \in Commands :
            TryForwardCommand(p, c)
    /\  UNCHANGED <<proposals, committed, usedPrivileges>>

Init ==
    /\  forwarded = <<>>
    /\  proposals = <<>>
    /\  committed = <<>>
    /\  usedPrivileges = <<>>

Terminated ==
    /\  ~   \/  \E s \in Slots : ENABLED Consensus(s)
            \/  \E p \in Proposers : 
                    \/  ENABLED PromoteSelf(p)
                    \/  ENABLED ForwardToPrivileged(p)
                    \/  ENABLED ProposeForwarded(p)
    /\  UNCHANGED vars

Next ==
    \/  \E s \in Slots : Consensus(s)
    \/  \E p \in Proposers : 
            \/  PromoteSelf(p)
            \/  ForwardToPrivileged(p)
            \/  ProposeForwarded(p)
    \/  Terminated

Spec == Init /\ [][Next]_vars
====