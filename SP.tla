---- MODULE SP ----
(*****************************************************************************)
(* A TLA+ specification of the Spanning Privilege algorithm —                *)
(* the composition of a sequence of discrete single-value consensus          *)
(* instances to form a complete multi-value consensus protocol.              *)
(*                                                                           *)
(* The specification of the single-value protocol is irrelevant as we are    *)
(* not trying to verify it here; the assumption is that the protocol is      *)
(* correct. The intention of this specification is to describe the           *)
(* composition of discrete protocol instances.                               *)
(*                                                                           *)
(* Single-value consensus is modelled abstractly as a black box.             *)
(* Rather than specifying a complete ensemble of consenting processes and    *)
(* depicting all the admissible behaviours of the underlying protocol, we    *)
(* model a consensus instance as 1) a variable comprising the finite set of  *)
(* value-bearing proposals that any process may submit to, 2) an initially   *)
(* unset variable that specifies the chosen value, and 3) a next-state       *)
(* action that selects an arbitrary value from (1) and assigns it to (2).    *)
(* If at least one proposal is submitted, the protocol will eventually       *)
(* terminate by the execution of (3). Any process can learn the outcome by   *)
(* reading (2). No process may influence the value of (2) after the protocol *)
(* has terminated.                                                           *)
(*****************************************************************************)
EXTENDS Integers, TLC, FiniteSets

CONSTANTS 
    Proposers,      \* `Proposers' is a set of proposers that have a stable identity.
    Commands,       \* `Commands' is a set of commands that may be proposed.
    Gamma,          \* `Gamma' is the number of slots that a proposer has privilege
                    \* over. For a slot `s' marked by proposer `p', `p' has
                    \* implicit privilege over slots `(s + 1)..(s + Gamma)'.
    Null

VARIABLES
    proposals,      \* `proposals[s]' is a set of pending proposals for slot `s',
                    \* used for abstractly modelling single-value consensus
    committed,      \* `committed[s]' is the committed value for slot `s',
                    \* used for abstractly modelling single-value consensus
    theta,          \* `theta[p]' is the current `theta' of `p'
    lastProposed,   \* `lastProposed[p]' is the highest slot that `p' proposed in
    lastChosen      \* `lastChosen[p]' is the highest slot in which a value 
                    \* marked by `p' was chosen in

vars == <<proposals, committed, theta, lastProposed, lastChosen>>

Slots == Nat        \* override with a finite set when model checking
Thetas == Nat       \* override with a finite set when model checking

Values == Commands \X (Proposers \union {Null}) \X (Thetas \union {Null})
Proposals == [val: Values, priv: BOOLEAN]

ValidProposals == 
    /\  DOMAIN proposals \in SUBSET Slots
    /\  \A s \in DOMAIN proposals : proposals[s] \in SUBSET Proposals
ValidCommitted ==
    /\  DOMAIN committed \in SUBSET Slots
    /\  \A s \in DOMAIN committed : committed[s] \in Values
ValidTheta == theta \in [Proposers -> Thetas]
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
    /\  ValidProposals /\ ValidCommitted /\ ValidTheta
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
(* unless one is already present.                                            *)
(*****************************************************************************)
TrySubmitProposal(s, v, privileged) ==
    LET proposal == [val |-> v, priv |-> privileged]
    IN  IF s \in DOMAIN proposals THEN 
            /\  proposal \notin proposals[s]
            /\  proposals' = [proposals EXCEPT ![s] = @ \union {proposal}]
        ELSE 
            proposals' = proposals @@ s :> {proposal}

(*****************************************************************************)
(* The next-state relation for conditionally executing the consensus         *)
(* protocol in slot `s'.                                                     *)
(*                                                                           *)
(* Termination occurs if at least one value has been proposed for            *)
(* `s'. If the set of proposed values in `s' is non-empty, an arbitrary      *)
(* value among those proposed will be chosen and assigned to `committed[s]'. *)
(* By the agreement property, once a value has been committed in `s', no     *)
(* other value may be committed in `s'.                                      *)
(*****************************************************************************)
Consensus(s) ==
    /\  s \in DOMAIN proposals
    /\  s \notin DOMAIN committed
    /\  LET chosen == CHOOSE p \in proposals[s] : TRUE
        IN  committed' = committed @@ s :> chosen.val
    /\  UNCHANGED <<theta, lastProposed, lastChosen, proposals>>
----
(*****************************************************************************)
(* Invariants.                                                               *)
(*****************************************************************************)

(*****************************************************************************)
(* No two proposers may commit a distinctly marked value within `Gamma'      *)
(* slots of each other.                                                      *)
(*****************************************************************************)
PrivilegedProposerSeparation ==
    \A s \in Slots :
        s \in DOMAIN committed /\ committed[s][2] # Null 
            => \A t \in Max(1, s - Gamma + 1)..(s - 1) :
                    \/  t \notin DOMAIN committed
                    \/  committed[t][2] = Null
                    \/  committed[t][2] = committed[s][2] /\ committed[t][3] = committed[s][3]

(*****************************************************************************)
(* There may be at most one privilege exercised in any slot. The concept     *)
(* of privilege is protocol-specific; for example, it may refer to the       *)
(* 'round-zero privilege' of Spire, or the 'ballot-zero optimisation' of     *)
(* Paxos.                                                                    *)
(*****************************************************************************)
SingularityOfExercisedPrivilege ==
    \A s \in DOMAIN proposals :
        Cardinality({p \in proposals[s] : p.priv}) <= 1

(*****************************************************************************)
(* The `lastChosen' offsets of no two proposers may come within `Gamma'      *)
(* of each other.                                                            *)
(*****************************************************************************)
LastChosenOffsetSeparation ==
    LET Abs(x) == IF x < 0 THEN -x ELSE x
    IN  \A p1, p2 \in DOMAIN lastChosen : 
            Abs(lastChosen[p1] - lastChosen[p2]) < Gamma => p1 = p2

(*****************************************************************************)
(* No gap in the log (largest contiguous sequence of uncommitted             *)
(* slots) may exceed `Gamma'.                                                *)
(*****************************************************************************)
WidestGapInLog ==
    \A s \in DOMAIN committed : 
        s > Gamma => ~\A t \in (s - Gamma)..(s - 1) : t \notin DOMAIN committed
----
(*****************************************************************************)
(* Proposer behaviour, covering both privileged and non-privileged cases as  *)
(* separate next-state relations.                                            *)
(*****************************************************************************)

(*****************************************************************************)
(* Helper for conditionally setting `map[p]' to `s' if either the entry is   *)
(* unassigned, or if `s' is greater than the currently assigned entry.       *)
(*****************************************************************************)
SetLast(s, p, map) ==
    /\  p \in DOMAIN map => s > map[p]
    /\  map' = [x \in DOMAIN map \union {p} |-> IF x = p THEN s ELSE map[x]]

(*****************************************************************************)
(* Conditionally set `lastProposed[p]' to `s' if either the entry is         *)
(* unassigned, or if `s' is greater than the currently assigned entry.       *)
(*****************************************************************************)
SetLastProposed(s, p) == SetLast(s, p, lastProposed)

(*****************************************************************************)
(* Conditionally set `lastChosen[p]' to `s' if either the entry is           *)
(* unassigned, or if `s' is greater than the currently assigned entry.       *)
(*****************************************************************************)
SetLastChosen(s, p) == SetLast(s, p, lastChosen)

(*****************************************************************************)
(* Checks that all of the given `slots' have been committed, and are either  *)
(* unmarked or marked with the given `_rho' and `_theta'.                    *)
(*****************************************************************************)
AreNeutralOrMarked(slots, _rho, _theta) ==
    \A s \in slots : 
        /\  s \in DOMAIN committed 
        /\  \/  committed[s][2] = Null
            \/  committed[s][2] = _rho /\ committed[s][3] = _theta

(*****************************************************************************)
(* Proposer `q' attempts to promote itself to privileged status by           *)
(* committing `Gamma' entries ahead of the most recent privileged proposer,  *)
(* with the last of those entries marked with `q''s `rho' and `theta' pair.  *)
(*                                                                           *)
(* Ordinarily, `q' will prefer to forward its command to a privileged        *)
(* proposer. However, it might not be aware of one.                          *)
(* Perhaps, the log is empty, or `q' has not yet learned a value.            *)
(* Alternatively, it might suspect that the privileged proposer has failed   *)
(* via some failure detector (such as a timeout). At this point, `q'         *)
(* must either locate an alternate proposer to forward to, or commit the     *)
(* command directly to the log. If `q' and possibly other proposers can      *)
(* commit `Gamma - 1' contiguous unmarked entries, the proposer that         *)
(* commits the `Gamma'th marked entry will acquire privileges over the       *)
(* following `Gamma' slots. `q' may nominate any proposer for privileged     *)
(* status, including the current privileged proposer. In practice, `q' may   *)
(* do so if it needs to commit a value urgently, but it would rather not     *)
(* become privileged itself. An example is where `q' is acting under a soft  *)
(* deadline and, in the absence of a timely response, `q' decides to offer   *)
(* directly but allows the current privileged proposer to retain its status. *)
(*                                                                           *)
(* The protocol requires `q' to first select a vacant slot, which should     *)
(* ideally follow the last committed slot in the log. `q' can                *)
(* discover a vacant slot by 1) looking at its own copy of the log,          *)
(* 2) asking its peers for the highest slot number they are aware of, or     *)
(* 3) querying the consenters for the highest slot number that is occupied.  *)
(*                                                                           *)
(* The next objective is to propose a contiguous series of entries,          *)
(* which may be real commands or no-ops. The latter may be necessary if `q'  *)
(* wishes to proactively elevate its status, even in the absence of          *)
(* steady command traffic from its clients.                                  *)
(* The first `Gamma - 1' entries must be unmarked. The `Gamma'th entry is    *)
(* marked with `q''s `rho' and `theta'. Prior to committing the `Gamma'th    *)
(* entry, `q' must ascertain that the preceding `Gamma - 1' entries have     *)
(* been chosen and are unmarked. If some other proposer commits a marked     *)
(* entry, `q' must either accept the new privileged proposer or restart its  *)
(* count. Proposing a marked entry does not imply that                       *)
(* `q' will succeed; `q' must ascertain that its command (and not some       *)
(* other proposer's) was committed to the last slot.                         *)
(* This is done by checking that the `rho' and `theta' match. Any proposer   *)
(* that has committed a marked entry in slot `s' is implicitly granted       *)
(* privileges over slots `(s + 1)..(s + Gamma)'.                             *)
(*****************************************************************************)
PromoteSelf(q) ==
    /\  q \notin DOMAIN lastChosen
    /\  LET highestProposed == HighestProposed
            nextVacant == IF highestProposed # 0 THEN highestProposed ELSE HighestCommitted + 1
        IN  \E s \in 1..nextVacant, c \in Commands :
                /\  s \in Slots
                /\  IF AreNeutralOrMarked(Max(1, s - Gamma + 1)..(s - 1), q, theta[q]) THEN
                        TrySubmitProposal(s, <<c, q, theta[q]>>, FALSE)
                    ELSE
                        TrySubmitProposal(s, <<c, Null, Null>>, FALSE)
                /\  SetLastProposed(s, q)
    /\  UNCHANGED <<committed, theta, lastChosen>>

(*****************************************************************************)
(* If a proposer `p' has been forwarded a command from its peer, it should   *)
(* try to commit it by the slot-privilege it presumably holds.               *)
(*                                                                           *)
(* This scenario occurs when some non-privileged                             *)
(* proposer `q' receives a command                                           *)
(* from a client, and decides that the best course of action is to forward   *)
(* it to `p'. This is the optimal behaviour in the                           *)
(* stable case, as serialising commands through a single proposer eliminates *)
(* contention for log slots. However, `q' might mistake `p' for              *)
(* the privileged proposer when, in fact, `p''s status has since been        *)
(* superseded by another proposer.                                           *)
(*                                                                           *)
(* Because the identity of the privileged proposer is discovered             *)
(* by learning values, and `q' might not be privy to all values up to the    *)
(* end of the log, it is conceivable that `p' is not the most recent         *)
(* privileged proposer, and should not fulfil `q''s request. We account for  *)
(* all admissible behaviours by allowing commands to be forwarded            *)
(* to any proposer, irrespective of whether or not it is privileged.         *)
(*                                                                           *)
(* The proxy `p' may only exercise its privilege when committing             *)
(* a value in `s' if it has committed at least one marked value in the       *)
(* slot range `(s - Gamma)..(s - 1)' — a fact that it is intrinsically aware *)
(* of. The specification fulfils this property by tracking two variables:    *)
(* `lastProposed' and `lastChosen'. The commit status of prior slots         *)
(* is asynchronously verified by `VerifyChosenProposal(p)', which updates    *)
(* `lastChosen[p]' accordingly. If `p' has not ascertained its privilege     *)
(* in the last `Gamma' slots, it will halt until it has done so.             *)
(* A real implementation will eventually time out and reply with a NACK. If  *)
(* another proposer secures one of the prior `Gamma' slots, and `p' observes *)
(* this, `p' should voluntarily disavow its status and                       *)
(* NACK the forwarded request. Its status would also be dropped if `p' were  *)
(* to restart. At any rate, the implementation should                        *)
(* immediately NACK all forwarded requests if `p' is non-privileged.         *)
(*                                                                           *)
(* This specification does not model NACKs as this would only make the       *)
(* forwarding proposer `q' try some other proposer or attempt to promote     *)
(* itself; both actions are already adequately specified.                    *)
(*****************************************************************************)
ProposePrivileged(p) ==
    /\  p \in DOMAIN lastChosen
    /\  \E command \in Commands :
            LET nextSlot == lastProposed[p] + 1
            IN  /\  nextSlot \in Slots
                /\  nextSlot <= lastChosen[p] + Gamma
                /\  TrySubmitProposal(nextSlot, <<command, p, theta[p]>>, TRUE)
                /\  SetLastProposed(nextSlot, p)
    /\  UNCHANGED <<committed, theta, lastChosen>>

(*****************************************************************************)
(* Verifies that `p''s value proposed in slot `lastProposed[p]' or any of    *)
(* the prior `Gamma - 1' slots were chosen                                   *)
(* by consensus, thereby extending `p''s privileged status by `Gamma' slots  *)
(* from the last chosen slot marked by `p'.                                  *)
(*                                                                           *)
(* Verification occurs when `p' learns of a result favouring `p' — sometime  *)
(* after proposing the value.                                                *)
(* Until this has been verified for slots `(s - Gamma + 1)..(s)',            *)
(* `p' is blocked from using its privilege in `s + 1'. (`p' halts until      *)
(* it has a confirmation of a marked commit in that range.)                  *)
(* A practical implementation should also consider the case where some other *)
(* proposer supersedes `p' by committing a marked value. The                 *)
(* implementation may simply reset `p' — yielding its status and             *)
(* incrementing its `theta'. The specification disregards this case because  *)
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
                    /\  committed[s][3] = theta[p]
                    /\  SetLastChosen(s, p)
    /\  UNCHANGED <<proposals, committed, theta, lastProposed>>

(*****************************************************************************)
(* Resets proposer `p', wiping any transient variables — thereby simulating  *)
(* a fail-stop, followed by reinitialisation.                                *)
(*                                                                           *)
(* A reset is also useful is when `p' determines that some                   *)
(* other proposer has acquired privileged status. In this case, `p'          *)
(* should voluntarily yield its status — an equivalent of a reset.           *)
(*                                                                           *)
(* Upon restart, the `p' will disregard any prior privileged status. Its     *)
(* `theta' will be incremented, so that any privileged status acquired       *)
(* within the new `theta' will be distinct from the previous. This ensures   *)
(* that a proposer never uses its slot-privilege twice.                      *)
(*****************************************************************************)
Reset(p) ==
    \* Only reset a proposer if it might be privileged. Resetting a non-privileged
    \* proposer would have no effect, other than to increment its `theta'.
    /\  p \in DOMAIN lastProposed
    /\  theta[p] + 1 \in Thetas
    /\  lastProposed' = [d \in DOMAIN lastProposed \ {p} |-> lastProposed[d]]
    /\  lastChosen' = [d \in DOMAIN lastChosen \ {p} |-> lastChosen[d]]
    /\  theta' = [theta EXCEPT ![p] = @ + 1]
    /\  UNCHANGED <<proposals, committed>>
----
(*****************************************************************************)
(* The initial state predicate.                                              *)
(*****************************************************************************)
Init ==
    /\  proposals = <<>>
    /\  committed = <<>>
    /\  theta = [p \in Proposers |-> 1]
    /\  lastProposed = <<>>
    /\  lastChosen = <<>>

(*****************************************************************************)
(* A special 'marker' state that signifies that the algorithm has            *)
(* terminated due to the exhaustion of the allowed slot numbers or `theta'   *)
(* increments. It is useful for bounded model checking (where `Slots' and    *)
(* `Thetas' are replaced with a finite set).                                 *)
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
                    \/  ENABLED ProposePrivileged(p)
                    \/  ENABLED VerifyChosenProposal(p)
                    \/  ENABLED Reset(p)
    /\  UNCHANGED vars

(*****************************************************************************)
(* The canonical combined next-state action.                                 *)
(*****************************************************************************)
Next ==
    \/  \E s \in Slots : Consensus(s)
    \/  \E p \in Proposers : 
            \/  PromoteSelf(p)
            \/  ProposePrivileged(p)
            \/  VerifyChosenProposal(p)
            \/  Reset(p)
    \/  Terminated

(*****************************************************************************)
(* The canonical specification.                                              *)
(*****************************************************************************)
Spec == Init /\ [][Next]_vars
====