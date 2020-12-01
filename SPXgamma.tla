---- MODULE SPXgamma ----
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
    Proposers,      \* `Proposers' is a set of proposers that have a stable identity.
    Commands,       \* `Commands' is a set of commands that may be proposed.
    Gamma,          \* `Gamma' is the number of slots that a proposer has privilege
                    \* over. E.g. for `Gamma=3' and a secured slot `s', the proposer
                    \* has privilege over slots `s+1..s+Gamma'.
    Nil

VARIABLES
    proposals,      \* `proposals[s]' is a set of pending proposals for slot `s',
                    \* used for abstractly modelling single-value consensus
    committed,      \* `committed[s]' is the committed value for slot `s',
                    \* used for abstractly modelling single-value consensus
    forwarded,      \* `forwarded[p]' is a set of forwarded commands for proposer `p'
    epoch,          \* `epoch[p]' is the current epoch number of `p'
    lastProposed,   \* `lastProposed[p]' is the highest slot that `p' proposed in
    lastChosen      \* `lastChosen[p]' is the highest slot that `p's proposal was chosen in

vars == <<proposals, committed, forwarded, epoch, lastProposed, lastChosen>>

Slots == Nat        \* override with a finite set when model checking
Epochs == Nat       \* override with a finite set when model checking

\* A finite set of slots, required for bounded model checking.
FiniteSlots == 1..6

\* A finite set of epochs, required for bounded model checking.
FiniteEpochs == 1..1

Values == Commands \X (Proposers \union {Nil}) \X (Epochs \union {Nil})
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
ValidEpoch == epoch \in [Proposers -> Epochs]
ValidLastProposed == 
    /\  DOMAIN lastProposed \in SUBSET Proposers
    /\  \A s \in DOMAIN lastProposed : lastProposed[s] \in Slots
ValidLastChosen == 
    /\  DOMAIN lastChosen \in SUBSET Proposers
    /\  \A s \in DOMAIN lastChosen : lastChosen[s] \in Slots

(*****************************************************************************)
(* The complete type-correctness invariant.                                  *)
(*****************************************************************************)  
TypeOK ==
    /\  ValidProposals /\ ValidCommitted /\ ValidForwarded /\ ValidEpoch
    /\  ValidLastProposed /\ ValidLastChosen

(*****************************************************************************)
(* Selects the maximum value in a set.                                       *)
(*****************************************************************************)
SetMax(S) == CHOOSE t \in S : \A s \in S : t >= s

(*****************************************************************************)
(* Selects the maximum among two values.                                     *)
(*****************************************************************************)
Max(a, b) == IF a > b THEN a ELSE b
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
(* Clears all proposals in slot `s'. This is only done when a value          *)
(* has been decided.                                                         *)
(*****************************************************************************)
ClearProposals(s) ==
    proposals' = [t \in DOMAIN proposals \ {s} |-> proposals[t]]

(*****************************************************************************)
(* Commits the specified value `v' in slot `s'.                              *)
(*****************************************************************************)
CommitValue(s, v) ==
    committed' = committed @@ s :> v

(*****************************************************************************)
(* The next-state relation for conditionally executing the consensus         *)
(* protocol in slot `s'.                                                     *)
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
    /\  UNCHANGED <<forwarded, epoch, lastProposed, lastChosen>>
----
(*****************************************************************************)
(* Invariants.                                                               *)
(*****************************************************************************)

\* CappedPendingProposals ==
\*     Cardinality(DOMAIN proposals) <= Gamma

SlidingWindowSingularityOfPrivilegedProposer ==
    \A s \in Slots :
        s \in DOMAIN committed /\ committed[s][2] # Nil 
            => \A t \in Max(1, s - Gamma + 1)..(s - 1) :
                    \/  t \notin DOMAIN committed
                    \/  committed[t][2] = Nil
                    \/  committed[t][2] = committed[s][2] /\ committed[t][3] = committed[s][3]

(*****************************************************************************)
(* There may be at most one privilege exercised in any slot. The concept     *)
(* of privilege is protocol-specific; it may refer to the                    *)
(* 'round-zero privilege' of Spire, or the                                   *)
(* 'ballot-zero optimisation' of Paxos.                                      *)
(*****************************************************************************)
SingularityOfExercisedPrivilege ==
    \A s \in DOMAIN proposals :
        Cardinality({p \in proposals[s] : p.priv}) <= 1

UniqueLastChosen ==
    \A p1, p2 \in DOMAIN lastChosen : lastChosen[p1] = lastChosen[p2] => p1 = p2
----
(*****************************************************************************)
(* Proposer behaviour, covering both privileged and non-privileged cases as  *)
(* separate next-state relations.                                            *)
(*****************************************************************************)

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
(* Helper for conditinally setting `var[p]' to `s' if either the entry is    *)
(* unassigned, or if `s' is greater than the currently assigned entry.       *)
(*****************************************************************************)
SetLast(s, p, var) ==
    IF p \in DOMAIN var THEN 
        /\  s > var[p]
        /\  var' = [var EXCEPT ![p] = s]
    ELSE 
        var' = var @@ p :> s

(*****************************************************************************)
(* Conditionally set `lastProposed[p]' to `s' if either the entry is         *)
(* unassigned, or if `s' is greater than the currently assigned entry.       *)
(*****************************************************************************)
SetLastProposed(s, p) == \*TODO
    IF p \in DOMAIN lastProposed THEN 
        /\  s > lastProposed[p]
        /\  lastProposed' = [lastProposed EXCEPT ![p] = s]
    ELSE 
        lastProposed' = lastProposed @@ p :> s

(*****************************************************************************)
(* Conditionally set `lastChosen[p]' to `s' if either the entry is           *)
(* unassigned, or if `s' is greater than the currently assigned entry.       *)
(*****************************************************************************)
SetLastChosen(s, p) == \*TODO
    IF p \in DOMAIN lastChosen THEN 
        /\  s > lastChosen[p]
        /\  lastChosen' = [lastChosen EXCEPT ![p] = s]
    ELSE 
        lastChosen' = lastChosen @@ p :> s

(*****************************************************************************)
(* Checks that all of the given `slots' have been committed, and are either  *)
(* unmarked or marked with the given `p' PID and `e' epoch number.           *)
(*****************************************************************************)
AreNeutralOrMarked(slots, p, e) ==
    \A s \in slots : 
        /\  s \in DOMAIN committed 
        /\  \/  committed[s][2] = Nil
            \/  committed[s][2] = p /\ committed[s][3] = e

(*****************************************************************************)
(* Proposer `p' attempts to elevate its status to privileged by committing   *)
(* `Γ' entries ahead of the most recent privileged proposer,                 *)
(* with the last of those entries marked with `p''s PID and epoch.           *)
(*                                                                           *)
(* Ordinarily, `p' will prefer to forward a command to a privileged          *)
(* proposer. However, it might not be aware of one.                          *)
(* Perhaps, the log is empty, or `p' has not yet learned a value.            *)
(* Alternatively, it might suspect that the privileged proposer has failed   *)
(* through some failure detector (such as a timeout). At this point, `p'     *)
(* must either locate an alternate proposer to forward to, or commit the     *)
(* command directly to the log. If `p' and possibly other proposers are      *)
(* able to commit `Γ - 1' contiguous unmarked entries, the proposer that     *)
(* commits the                                                               *)
(* `Γ'th marked entry will acquire commit privileges over the following `Γ'  *)
(* slots.                                                                    *)
(*                                                                           *)
(* The protocol requires `p' to first select a vacant slot, which should     *)
(* ideally follow the last committed slot in the log. `p' can                *)
(* discover a vacant slot by 1) looking at its own copy of                   *)
(* the log, 2) asking its peers for the highest slot number they are aware   *)
(* of, or 3) querying the consenters for the highest slot number that is     *)
(* occupied.                                                                 *)
(*                                                                           *)
(* The next objective is to propose a contiguous series of entries,          *)
(* which may be real commands or no-ops. The latter may be necessary if `p'  *)
(* wishes to proactively elevate its status, even in the absence of          *)
(* steady command traffic from its clients.                                  *)
(* The first `Γ - 1' entries must be unmarked. The `Γ'th entry               *)
(* is marked with `p''s PID and epoch. Prior to committing the `Γ'th entry,  *)
(* `p' must ascertain that the preceding `Γ - 1' entries have been chosen    *)
(* and are unmarked. If some other proposer commits a marked entry,          *)
(* `p' must either accept the new privileged proposer or restart its count.  *)      
(* Proposing a marked entry does not imply that                              *)
(* `p' will succeed; `p' must ascertain that its command (and not some       *)
(* other proposer's) was committed to the last slot.                         *)
(* This is done by checking that the PID and epoch numbers match. Generally  *)
(* speaking, any proposer that has committed a marked entry in slot `s' is   *)
(* implicitly granted commit privileges over slots `(s + 1)..(s + Γ)'.       *)
(*****************************************************************************)
PromoteSelf(p) ==
    /\  p \notin DOMAIN lastChosen
    /\  LET highestProposed == HighestProposed
            nextVacant == IF highestProposed # 0 THEN highestProposed ELSE HighestCommitted + 1
            s == nextVacant
        IN  (*\E s \in 1..nextVacant, *) \E c \in Commands : \*TODO
                /\  s \in Slots
                \* /\  PrintT(Max(1, s - Gamma + 1)..(s - 1))
                /\  IF AreNeutralOrMarked(Max(1, s - Gamma + 1)..(s - 1), p, epoch[p]) THEN
                        TrySubmitProposal(s, <<c, p, epoch[p]>>, FALSE)
                    ELSE
                        TrySubmitProposal(s, <<c, Nil, Nil>>, FALSE)
                /\  SetLastProposed(s, p)
    /\  UNCHANGED <<forwarded, committed, epoch, lastChosen>>

(*****************************************************************************)
(* If a proposer `p' has been forwarded a command from its peer, it should   *)
(* try to commit it by the slot-privilege it presumably holds.               *)
(*                                                                           *)
(* This condition occurs when some other non-privileged                      *)
(* proposer receives a command                                               *)
(* from a client, and decides that the best course of action is to forward   *)
(* it to `p'. This is the optimal behaviour in the                           *)
(* stable case, as serialising commands through a single proposer eliminates *)
(* contention for log slots. However, the forwarder might mistake `p' for    *)
(* the privileged proposer when, in fact, `p''s status has since been        *)
(* superseded by another proposer.                                           *)
(*                                                                           *)
(* In a practical implementation, `p' may only exercise its privilege when   *)
(* committing a value in `s' if it has committed at least one value in the   *)
(* slot range `(s - Γ)..(s - 1)' — a fact that it is intrinsically aware     *)
(* of. The specification mimics this property by tracking two variables:     *)
(* `lastProposed' and `lastChosen'. The commit status of prior slots         *)
(* is asynchronously verified by `VerifyChosenProposal(p)', which updates    *)
(* `lastChosen[p]' accordingly.                                              *)
(* `p' halts in `s' if it hasn't ascertained its privilege.                  *)
(* A real implementation will eventually time out and reply with a NACK. If  *)
(* another proposer secures one of the prior `Γ' slots,                      *)
(* `p' should disavow its status and                                         *)
(* NACK the forwarded request. Its status would also be dropped if `p' were  *)
(* to restart. The implementation should                                     *)
(* immediately NACK all forwarded requests if `p' is non-privileged.         *)
(*                                                                           *)
(* This specification does not model NACKs as this would only make the       *)
(* forwarding proposer try some other proposer or attempt to promote itself; *)
(* both actions are already adequately specified.                            *)
(*****************************************************************************)
ProposeForwarded(p) ==
    /\  p \in DOMAIN lastChosen
    /\  p \in DOMAIN forwarded
    /\  LET command == CHOOSE c \in forwarded[p] : TRUE
            nextSlot == lastProposed[p] + 1
        IN  /\  nextSlot \in Slots
            \* /\  PrintT(nextSlot - lastChosen[p])
            \* /\  nextSlot <= lastChosen[p] + Gamma \*TODO
            /\  TrySubmitProposal(nextSlot, <<command, p, epoch[p]>>, TRUE)
            /\  lastProposed' = [lastProposed EXCEPT ![p] = @ + 1]
    /\  UNCHANGED <<forwarded, committed, epoch, lastChosen>>

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
(* a fact that `p' is not yet aware of. So we account for all admissible     *)
(* behaviours by allowing commands to be forwarded to any proposer           *)
(* that held the privileged status at one time or another.                   *)
(*****************************************************************************)
ForwardToPrivileged ==
    /\  \E p \in {v[2] : v \in Range(committed)} :
            /\  p # Nil
            /\  \E c \in Commands :
                    TryForwardCommand(p, c)
    /\  UNCHANGED <<proposals, committed, epoch, lastProposed, lastChosen>>

(*****************************************************************************)
(* Verifies that `p''s value proposed in slot `lastProposed[p]' or any of    *)
(* the prior `Γ - 1' slots were chosen                                       *)
(* by consensus, thereby extended `p''s privileged status by `Γ' slots from  *)
(* the last chosen slot marked by `p'.                                       *)
(*                                                                           *)
(* Verification occurs when `p' learns of a result favouring `p' — sometime  *)
(* after proposing the value.                                                *)
(* Until this has been verified for slots `(s - Γ + 1)..(s)',                *)
(* `p' is blocked from using its privilege in `s + 1'. (`p' halts until      *)
(* it has a confirmation of a marked commit in that range.)                  *)
(* A practical implementation should also consider the case where some other *)
(* proposer supersedes `p' by committing a marked value. The                 *)
(* implementation may simply reset `p' — yielding its status and             *)
(* incrementing the epoch. The specification disregards this case because    *)
(* the next-state action `Reset(p)' already covers this indirectly.          *)
(*****************************************************************************)
VerifyChosenProposal(p) ==
    /\  p \in DOMAIN lastProposed
    /\  LET lastSlot == lastProposed[p]
            lastLearned == IF p \in DOMAIN lastChosen THEN lastChosen[p] ELSE 0
        IN  /\  lastSlot \in DOMAIN committed
            /\  \E s \in Max(lastLearned + 1, lastSlot - Gamma + 1)..lastSlot :
                    /\  s \in DOMAIN committed
                    /\  committed[s][2] = p
                    /\  committed[s][3] = epoch[p]
                    \* /\  SetLastChosen(s, p)
                    /\  p \in DOMAIN lastChosen => s > lastChosen[p]
                    /\  lastChosen' = [x \in DOMAIN lastChosen \union {p} |->
                                        IF x = p THEN s
                                        ELSE lastChosen[x]]
                    \* /\  IF p \in DOMAIN lastChosen THEN 
                    \*         /\  s > lastChosen[p]
                    \*         /\  lastChosen' = [lastChosen EXCEPT ![p] = s]
                    \*     ELSE 
                    \*         lastChosen' = [x \in DOMAIN lastChosen \union {p} |->
                    \*                        IF x = p THEN s
                    \*                        ELSE lastChosen[x]]
                    /\  UNCHANGED <<forwarded, proposals, committed, epoch, lastProposed>>
                    /\  PrintT(lastChosen') \*TODO

(*****************************************************************************)
(* Reset proposer `p', wiping any transient variables — thereby simulating   *)
(* a fail-stop, followed by reinitialisation.                                *)
(*                                                                           *)
(* A reset is also useful is when `p' determines that some                   *)
(* other proposer has acquired privileged status. In this case `p'           *)
(* should voluntarily yield its status — an equivalent of a reset.           *)
(*                                                                           *)
(* Upon restart, the `p' will disregard any prior privileged status. Its     *)
(* epoch will be incremented, so that any privilege status acquired within   *)
(* the new epoch will be distinct from the previous. This ensures that a     *)
(* proposer never uses its slot-privilege twice.                             *)
(*****************************************************************************)
Reset(p) ==
    \* Only reset a proposer if it might be privileged. Resetting a non-privileged
    \* proposer would have no effect, other than to increment its epoch.
    /\  p \in DOMAIN lastProposed
    /\  epoch[p] + 1 \in Epochs
    /\  lastProposed' = [d \in DOMAIN lastProposed \ {p} |-> lastProposed[d]]
    /\  lastChosen' = [d \in DOMAIN lastChosen \ {p} |-> lastChosen[d]]
    /\  epoch' = [epoch EXCEPT ![p] = @ + 1]
    /\  UNCHANGED <<forwarded, proposals, committed>>
----
(*****************************************************************************)
(* The initial state predicate.                                              *)
(*****************************************************************************)
Init ==
    /\  forwarded = <<>>
    /\  proposals = <<>>
    /\  committed = <<>>
    /\  epoch = [p \in Proposers |-> 1]
    /\  lastProposed = <<>>
    /\  lastChosen = <<>>

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
                    \/  ENABLED VerifyChosenProposal(p)
                    \/  ENABLED Reset(p)
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
            \/  VerifyChosenProposal(p)
            \/  Reset(p)
    \/  ForwardToPrivileged
    \/  Terminated

(*****************************************************************************)
(* The canonical specification.                                              *)
(*****************************************************************************)
Spec == Init /\ [][Next]_vars
====