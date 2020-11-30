---- MODULE SPX ----
(*****************************************************************************)
(* A TLA⁺ specification of the Spanning Privilege composition of a sequence  *)
(* of discrete single-value consensus instances to realise a                 *)
(* multi-value consensus protocol. The specification of the single-value     *)
(* protocol is irrelevant as are not trying to verify it here; the           *)
(* assumption is that the protocol is correct. The intention of this         *)
(* specification is to model the composition of discrete protocol instances. *)
(*                                                                           *)
(* Single-value consensus is modelled abstractly, as a black box.            *)
(* Rather than specifying a                                                  *)
(* complete ensemble of consenting processes and depicting all the           *)
(* admissible behaviours of the underlying protocol, we model a consensus    *)
(* instance as 1) a variable comprising the finite set of value-bearing      *)
(* proposals that any process may submit to, 2) an initially unset variable  *)
(* that specifies the chosen value, and 3) a next-state action that          *)
(* selects an arbitrary value from (1) and assigns it to (2). If at least    *)
(* one proposal is submitted, the protocol will eventually terminate by      *)
(* the execution of (3). Any process can learn the outcome by reading (2).   *)
(* No process can infuence the value of (2) after the protocol has           *)
(* terminated.                                                               *)
(*****************************************************************************)
EXTENDS Integers, TLC, FiniteSets

CONSTANTS 
    Proposers,      \* `Proposers' is a set of proposers that have a stable identity
    Commands        \* `Commands' is a set of commands that may be proposed

VARIABLES
    proposals,      \* `proposals[s]' is a set of pending proposals for slot `s',
                    \* used for abstractly modelling single-value consensus
    committed,      \* `committed[s]' is the committed value for slot `s',
                    \* used for abstractly modelling single-value consensus
    forwarded,      \* `forwarded[p]' is a set of forwarded commands for proposer `p'
    usedPrivilege   \* `usedPrivilege[p]' is the highest slot-privilege used by `p'

vars == <<proposals, committed, forwarded, usedPrivilege>>

Slots == Nat        \* override with a finite set when model checking

\* A finite set of slots, required for bounded model checking.
FiniteSlots == 1..2

(*****************************************************************************)
(* Invariants.                                                               *)
(*****************************************************************************)

Values == Commands \X Proposers
Proposals == [val: Values, priv: BOOLEAN]

ValidProposals == 
    /\  DOMAIN proposals \in SUBSET Slots
    /\  \A s \in DOMAIN proposals : proposals[s] \in SUBSET Proposals
ValidCommitted ==
    /\  DOMAIN committed \in SUBSET Slots
    /\  \A s \in DOMAIN committed : committed[s] \in Values
ValidForwarded == 
    /\  DOMAIN forwarded \in SUBSET Proposers
    /\  \A p \in DOMAIN forwarded : forwarded[p] \in SUBSET Commands
ValidUsedPrivilege == 
    /\  DOMAIN usedPrivilege \in SUBSET Proposers
    /\  \A s \in DOMAIN usedPrivilege : usedPrivilege[s] \in Slots

(*****************************************************************************)
(* The complete type-correctness invariant.                                  *)
(*****************************************************************************)  
TypeOK ==
    ValidProposals /\ ValidCommitted /\  ValidForwarded /\ ValidUsedPrivilege

(*****************************************************************************)
(* Selects the maximum value in a set.                                       *)
(*****************************************************************************)
SetMax(S) == CHOOSE t \in S : \A s \in S : t >= s
----
(*****************************************************************************)
(* Operators for abstractly modelling single-value consensus. Each slot in   *)
(* variables `proposals' and `committed' represents a distinct consensus     *)
(* instance. Slot indexing is 1-based.                                       *)
(*****************************************************************************)

(*****************************************************************************)
(* The highest slot number which has at least one pending proposal. If no    *)
(* slots have pending proposals, this operator returns `0'.                  *)
(*****************************************************************************)
HighestProposed == 
    IF DOMAIN proposals # {} THEN SetMax(DOMAIN proposals) ELSE 0

(*****************************************************************************)
(* The highest slot number which contains a committed value. If no           *)
(* slots have committed values, this operator returns `0'.                   *)
(*****************************************************************************)
HighestCommitted ==
    IF DOMAIN committed # {} THEN SetMax(DOMAIN committed) ELSE 0

(*****************************************************************************)
(* Conditionally submits a proposal for value `v' in slot `s' with the       *)
(* specified `privileged' mode. The proposal is appended to `proposals[s]'   *)
(* unless one is already present, or a value has been chosen in `s'.         *)
(*****************************************************************************)
TrySubmitProposal(s, v, privileged) ==
    LET proposal == [val |-> v, priv |-> privileged]
    IN  /\  s \notin DOMAIN committed
        /\  IF s \in DOMAIN proposals THEN 
                /\  proposal \notin proposals[s]
                /\  proposals' = [proposals EXCEPT ![s] = @ \union {proposal}]
            ELSE 
                proposals' = proposals @@ s :> {proposal}

(*****************************************************************************)
(* Clears all proposals in slot `s'.                                         *)
(*****************************************************************************)
ClearProposals(s) ==
    proposals' = [t \in DOMAIN proposals \ {s} |-> proposals[t]]

(*****************************************************************************)
(* Commits the specified value `v' in slot `s'.                              *)
(*****************************************************************************)
CommitValue(s, v) ==
    committed' = committed @@ s :> v

(*****************************************************************************)
(* The next-state action for conditionally executing the consensus protocol  *)
(* in slot `s'.                                                              *)
(*                                                                           *)
(* Termination will occur if at least one value has been proposed for        *)
(* `s'. If the set of proposed values in `s' is non-empty, an arbitrary      *)
(* value among those proposed will be chosen and assigned to `committed[s]', *)
(* while simultaneously clearing `proposals[s]'.                             *)
(*****************************************************************************)
Consensus(s) ==
    /\  s \in DOMAIN proposals
    /\  LET chosen == CHOOSE p \in proposals[s] : TRUE
        IN  /\  ClearProposals(s)
            /\  CommitValue(s, chosen.val)
    /\  UNCHANGED <<forwarded, usedPrivilege>>
----
(*****************************************************************************)
(* Invariants.                                                               *)
(*****************************************************************************)

(*****************************************************************************)
(* There are no gaps in the log from the first slot to the highest committed *)
(* slot.                                                                     *)
(*****************************************************************************)  
GapFreeLog ==
    \A s \in 1..HighestCommitted : s \in DOMAIN committed

(*****************************************************************************)
(* There may be at most one privilege exercised in any slot. Privilege may   *)
(* refer to the 'round-zero privilege' of Spire, or the                      *)
(* 'ballot-zero optimisation' of Paxos.                                      *)
(*****************************************************************************)
SingularityOfPrivilege ==
    \A s \in DOMAIN proposals :
        Cardinality({p \in proposals[s] : p.priv}) <= 1
----
(*****************************************************************************)
(* Proposer behaviour.                                                       *)
(*****************************************************************************)

(*****************************************************************************)
(* Atomically verify whether a slot-privilege for proposer `p' is available  *)
(* for slot `s', and lock out `s' and all slots and prior to it.             *)
(*                                                                           *)
(* This ensures that a privileged proposer does not use its privilege twice  *)
(* on the same slot for a different command. In practice, this cannot occur  *)
(* if the proposer remembers the last committed slot number and clears its   *)
(* status in the event of a restart.                                         *)
(*****************************************************************************)
TryUsePrivilege(s, p) ==
    IF p \in DOMAIN usedPrivilege THEN
        /\  s > usedPrivilege[p]
        /\  usedPrivilege' = [usedPrivilege EXCEPT ![p] = s]
    ELSE
        usedPrivilege' = usedPrivilege @@ p :> s

(*****************************************************************************)
(* Conditionally forward the command `c' to a proposer `p', if one was not   *)
(* already sent.                                                             *)
(*****************************************************************************)
TryForwardCommand(p, c) ==
    IF p \notin DOMAIN forwarded THEN
        forwarded' = forwarded @@ p :> {c}
    ELSE
        /\  c \notin forwarded[p]
        /\  forwarded' = [forwarded EXCEPT ![p] = @ \union {c}]

(*****************************************************************************)
(* Proposer `p' commits a command to the log and promotes itself as the new  *)
(* privileged proposer in doing so (by attaching its PID to the command).    *)
(*                                                                           *)
(* Ordinarily, a proposer will prefer to forward a command to a privileged   *)
(* proposer. However, it might not be aware of one.                          *)
(* Perhaps, the log is empty, or `p' has not yet learned a value.            *)
(* Alternatively, it might suspect that the privileged proposer has failed   *)
(* by way of some failure detector (such as a timeout). So it is forced to   *)
(* take matters into its own hands.                                          *)
(*                                                                           *)
(* The protocol requires `p' to first select a vacant slot, which should     *)
(* ideally be after the last committed slot in the log. But the new slot     *)
(* should not leave a gap between itself and the                             *)
(* most recently committed slot. `p' can                                     *)
(* conservatively discover a vacant slot by 1) looking at its own copy of    *)
(* the log, 2) asking its peers for the highest slot number they are aware   *)
(* of, or 3) querying the consenters for the highest slot number that is     *)
(* occupied. In cases (1) and (2), `p' can advance to the slot immediately   *)
(* following the last committed slot. But in (3), the slot might not         *)
(* be committed (an occupied slot in a consenter does not imply that a value *)
(* has been chosen in that slot), so `p' would conservatively                *)
(* start at that slot number and attempt to terminate the protocol.          *)
(*****************************************************************************)
PromoteSelf(p) ==
    /\  LET highestProposed == HighestProposed
            nextVacant == IF highestProposed # 0 THEN highestProposed ELSE HighestCommitted + 1
        IN  \E s \in 1..nextVacant, c \in Commands :
                /\  s \in Slots
                /\  TrySubmitProposal(s, <<c, p>>, FALSE)
    /\  UNCHANGED <<forwarded, committed, usedPrivilege>>

(*****************************************************************************)
(* If a proposer has been forwarded a command from its peer, it should try   *)
(* to commit it by the slot-privilege it holds.                              *)
(*                                                                           *)
(* This condition occurs when a non-privileged proposer receives a command   *)
(* from a client, and decides that the best course of action is to forward   *)
(* it to the privileged proposer. This is the optimal behaviour in the       *)
(* stable case, as serialising commands through a single proposer eliminates *)
(* contention for log slots. However, the forwarder might mistake `p' for    *)
(* the privileged proposer when, in fact, `p''s status has since been        *)
(* superseded by another proposer.                                           *)
(*                                                                           *)
(* In a practical implementation, `p' must only commit a value in `s' if it  *)
(* has committed a value in `s - 1' — a fact that it is intrinsically aware  *)
(* of. But if `p' restarts, it loses this information. In a real             *)
(* implementation, an initialising proposer makes no assumptions as to its   *)
(* status. So the specification assumes amnesia, and checks the committer    *)
(* of the preceding value.                                                   *)
(*****************************************************************************)
ProposeForwarded(p) ==
    /\  p \in DOMAIN forwarded
    /\  LET command == CHOOSE c \in forwarded[p] : TRUE
            highestCommitted == HighestCommitted
        IN  /\  highestCommitted # 0
            /\  highestCommitted + 1 \in Slots
            /\  committed[highestCommitted][2] = p
            /\  TryUsePrivilege(highestCommitted + 1, p)
            /\  TrySubmitProposal(highestCommitted + 1, <<command, p>>, TRUE)
    /\  UNCHANGED <<forwarded, committed>>

(*****************************************************************************)
(* The range of a function `F'.                                              *)
(*****************************************************************************)
Range(F) == {F[d] : d \in DOMAIN F}

(*****************************************************************************)
(* Forwards a command to a proposer that at one time or another held the     *)
(* privileged status.                                                        *)
(*                                                                           *)
(* This emulates the behaviour of a proposer `p' when it does not hold the   *)
(* privileged status itself, but knows of some proposer `q' that might be    *)
(* privileged. A pragmatic implementation would cache the identity of the    *)
(* privileged proposer and update it if it learns of another.                *)
(*                                                                           *)
(* Because the identity of the privileged proposer is discovered             *)
(* by learning values, and `p' might not be privy to all values up to the    *)
(* end of the log, it is conceivable that `q' is not the most recent         *)
(* privileged proposer. Perhaps, some other proposer has taken over `q' —    *)
(* an event that `p' is not yet aware of. So we account for all admissible   *)
(* behaviours by allowing proposers to forward commands to any proposer      *)
(* that held the privileged status at one time or another.                   *)
(*****************************************************************************)
ForwardToPrivileged ==
    /\  \E p \in {v[2] : v \in Range(committed)} :
            \E c \in Commands :
                TryForwardCommand(p, c)
    /\  UNCHANGED <<proposals, committed, usedPrivilege>>
----
(*****************************************************************************)
(* The initial state predicate.                                              *)
(*****************************************************************************)
Init ==
    /\  forwarded = <<>>
    /\  proposals = <<>>
    /\  committed = <<>>
    /\  usedPrivilege = <<>>

(*****************************************************************************)
(* A special 'marker' state that signifies that the algorithm has            *)
(* terminated due to the exhaustion of the allowed slot numbers. It is       *)
(* useful for bounded model checking (where `Slots' is replaced with a       *)
(* finite set).                                                              *)
(*                                                                           *)
(* This pseudo-action has no bearing on the operation of the algorithm,      *)
(* other than to prevent TLC from flagging a deadlock due to the absence     *)
(* of a viable next-state action. This action does not                       *)
(* change any variables and removing it has no adverse effect.               *)
(*****************************************************************************)  
Terminated ==
    /\  ~   \/  \E s \in Slots : ENABLED Consensus(s)
            \/  \E p \in Proposers : 
                    \/  ENABLED PromoteSelf(p)
                    \/  ENABLED ProposeForwarded(p)
            \/  ENABLED ForwardToPrivileged
    /\  UNCHANGED vars

(*****************************************************************************)
(* The canonical combined next-state action.                                 *)
(*****************************************************************************)
Next ==
    \/  \E s \in Slots : Consensus(s)
    \/  \E p \in Proposers : 
            \/  PromoteSelf(p)
            \/  ProposeForwarded(p)
    \/  ForwardToPrivileged
    \/  Terminated

(*****************************************************************************)
(* The canonical specification.                                              *)
(*****************************************************************************)
Spec == Init /\ [][Next]_vars
====