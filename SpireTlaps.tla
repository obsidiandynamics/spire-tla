---- MODULE SpireTlaps ----
(*****************************************************************************)
(* The complete proof of the safety of the Spire consensus algorithm.        *)
(*****************************************************************************)
EXTENDS Spire, TLAPS, NaturalsInduction, FiniteSetTheorems

(*****************************************************************************)
(* No quorum may be empty.                                                   *)
(*****************************************************************************)
LEMMA QuorumNonEmpty == \A Q \in Quorums : Q # {}
  BY QuorumAssumption

(*****************************************************************************)
(* The symbol `None' is not in the set of `Values'.                          *)
(*****************************************************************************)  
LEMMA NoneNotAValue == None \notin Values
  BY NoSetContainsEverything DEF None

(*****************************************************************************)
(* For a superset of quorum-answers obtained by `QuorumAnswers(Q)', each     *)
(* set of answers `A' is non-empty if and only if `Q' is non-empty.          *)
(*****************************************************************************)  
LEMMA AnswersNonEmpty ==
    \A Q \in Quorums : \A A \in QuorumAnswers(Q) : Q # {} <=> A # {}
  BY DEF QuorumAnswers, Answers

(*****************************************************************************)
(* The image of `PickRound(M)' is a single element in                        *)
(* `{m.lastRound : m \in M}' if `M' is a non-empty set of messages.          *)
(*****************************************************************************)  
LEMMA PickRoundImage ==
    \A M \in SUBSET Messages : M # {} => PickRound(M) \in {m.lastRound : m \in M}
  BY DEF PickRound, Messages

(*****************************************************************************)
(* The image of `PickValue(M)' is a single element in                        *)
(* `{m.lastVal : m \in M}' if `M' is a non-empty set of messages.            *)
(*****************************************************************************)  
LEMMA PickValueImage ==
    \A M \in SUBSET Messages : M # {} => PickValue(M) \in {m.lastVal : m \in M}
  BY DEF PickValue, Messages
  
(*****************************************************************************)
(* Determines whether the given finite set `S' of naturals contains an       *)
(* element that is greater or equal to all other elements. This seemingly    *)
(* frivolous result is required for the proof of                             *)
(* `AllNonEmptyFiniteNaturalsHaveMax' by finite set induction.               *)
(*****************************************************************************)  
HasMax(S) ==
    S \in SUBSET Nat /\ S # {} => \E n1 \in S : \A n2 \in S : n1 >= n2

(*****************************************************************************)
(* Every non-empty finite set of naturals `S' has a maximum                  *)
(* within `S' — an element that is greater than all other elements in `S'.   *)
(*                                                                           *)
(* Proof is by finite set induction: the predicate `HasMax({})' holds, and   *)
(* the addition of a natural number `x' to some set of naturals `R', where   *)
(* `x' is not already in `R' and `HasMax(R)', preserves                      *)
(* `HasMax(R \union {x})'.                                                   *)
(*****************************************************************************)
LEMMA AllNonEmptyFiniteNaturalsHaveMax ==
  ASSUME NEW S \in SUBSET Nat,
         S # {},
         IsFiniteSet(S),
         HasMax({})
  PROVE  HasMax(S)
  <1> DEFINE Q(T) == HasMax(T)
  <1> SUFFICES Q(S)
    BY DEF HasMax
  <1>1 Q({})
    OBVIOUS
  <1>2 ASSUME NEW R, NEW x, Q(R), x \notin R
       PROVE  Q(R \cup {x})
    BY <1>2 DEF HasMax
  <1> HIDE DEF Q
  <1> QED
    BY <1>1, <1>2, FS_Induction, IsaM("blast") DEF HasMax    

(*****************************************************************************)
(* The image of `MaxLastRound(M)' is a single element in                     *)
(* `{m.lastRound : m \in M}' if `M' is a non-empty set of messages.          *)
(*****************************************************************************)  
LEMMA MaxLastRoundImage ==
    \A M \in SUBSET Messages : M # {} => MaxLastRound(M) \in {m.lastRound : m \in M}
  <1> SUFFICES ASSUME NEW M \in SUBSET Messages,
                      M # {}
               PROVE  MaxLastRound(M) \in {m.lastRound : m \in M}
    OBVIOUS
  <1> USE DEF MaxLastRound
  <1>1 MaxLastRound(M) \in {m.lastRound : m \in M}
    BY AllNonEmptyFiniteNaturalsHaveMax DEF MaxLastRound, SetMax
  <1>2 QED
    BY <1>1
  
(*****************************************************************************)
(* The image of `MaxLastRound(M)' is in the powerset of                      *)
(* `{m.lastVal : m \in M}' if `M' is a non-empty set of messages.            *)
(*****************************************************************************)  
LEMMA SuccessorValuesImage ==
    \A M \in SUBSET Messages : M # {} => SuccessorValues(M) \in SUBSET {m.lastVal : m \in M}
  <1> SUFFICES ASSUME NEW M \in SUBSET Messages,
                      M # {},
                      SuccessorValues(M) =
                        LET highestRound == MaxLastRound(M)
                            highestRoundAnswers == {m \in M : m.lastRound = highestRound}
                            highestRoundPrimedAnswers == {m \in highestRoundAnswers : m.lastPrimed}
                        IN  IF highestRoundPrimedAnswers # {} THEN
                                {PickValue(highestRoundPrimedAnswers)}
                            ELSE
                                {a.lastVal : a \in highestRoundAnswers}
               PROVE  \A v \in SuccessorValues(M) : v \in {m.lastVal : m \in M}
    BY DEF SuccessorValues
  <1>1 DEFINE highestRound == MaxLastRound(M)
  <1>2 DEFINE highestRoundAnswers == {m \in M : m.lastRound = highestRound}
  <1>3 DEFINE highestRoundPrimedAnswers == {m \in highestRoundAnswers : m.lastPrimed}
  <1>4 \A a \in highestRoundAnswers : a \in M
    OBVIOUS
  <1>5 CASE highestRoundPrimedAnswers # {}
    BY <1>5, PickValueImage DEF PickValue
  <1>6 CASE highestRoundPrimedAnswers = {} 
    BY <1>6
  <1>7 QED
    BY <1>5, <1>6

(*****************************************************************************)
(* A uniform (same round number, same value), non-empty set of answers       *)
(* leads to a single successor value.                                        *)
(*****************************************************************************)
LEMMA SingularityOfSuccessorsToUniformAnswers ==
    \A M \in SUBSET Messages : M # {} /\ AllIdenticalRounds(M) /\ AllIdenticalValues(M) 
        => SuccessorValues(M) = {PickValue(M)}
    BY DEF SuccessorValues, AllIdenticalRounds, AllIdenticalValues, MaxLastRound, SetMax, PickValue

(*****************************************************************************)
(* A primed offer bearing a value `v' in round `r' implies that a uniform    *)
(* set of answers exists in `r-1' for `v' for at least one complete quorum.  *)
(*                                                                           *)
(* The proof follows from `MsgInv' for the case                              *)
(* `\A m \in msgs : m.type = "Offer" /\ m.round # 0 /\ m.primed'.            *)
(*****************************************************************************)
LEMMA PrimedOfferFollowsUniformAnswers ==
    TypeOK /\ MsgInv => 
        \A o \in msgs : o.type = "Offer" /\ o.primed =>
            \E Q \in Quorums : \E A \in QuorumAnswers(Q):
                \A a \in A : a.lastRound = o.round - 1 /\ a.lastVal = o.val
  <1> SUFFICES ASSUME MsgInv, TypeOK,
                      NEW o \in msgs,
                      o.type = "Offer" /\ o.primed
               PROVE  \E Q \in Quorums : \E A \in QuorumAnswers(Q):
                          \A a \in A : a.lastRound = o.round - 1 /\ a.lastVal = o.val
    OBVIOUS
  <1>1 \E Q \in Quorums : \E A \in QuorumAnswers(Q) :
          /\  A # {}
          /\  AllIdenticalRounds(A) /\ AllIdenticalValues(A)
          /\  o.val = PickValue(A)
          /\  o.round = PickRound(A) + 1
    BY AnswersNonEmpty, QuorumAssumption DEF MsgInv
  <1>2 \E Q \in Quorums : \E A \in QuorumAnswers(Q) :
          /\  A # {}
          /\  AllIdenticalRounds(A) /\ AllIdenticalValues(A)
          /\  o.val = PickValue(A)
          /\  o.round - 1 = PickRound(A)
    BY <1>1, PickRoundImage DEF Messages, TypeOK, QuorumAnswers, Answers, Rounds
  <1>3 PICK R \in Quorums : \E A \in QuorumAnswers(R) :
          /\  A # {}
          /\  AllIdenticalRounds(A) /\ AllIdenticalValues(A)
          /\  o.val = PickValue(A)
          /\  o.round - 1 = PickRound(A)
    BY <1>2
  <1>4 PICK B \in QuorumAnswers(R) :
          /\  B # {}
          /\  AllIdenticalRounds(B) /\ AllIdenticalValues(B)
          /\  o.val = PickValue(B)
          /\  o.round - 1 = PickRound(B)
    BY <1>3
  <1>5  /\  B # {}
        /\  AllIdenticalRounds(B)
        /\  PickRound(B) \in {a.lastRound : a \in B}
        /\  o.round - 1 \in {a.lastRound : a \in B}
        /\  \A a \in B : a.lastRound = o.round - 1
    BY <1>4, PickRoundImage DEF AllIdenticalRounds, TypeOK, QuorumAnswers, Answers
  <1>6  /\  B # {}
        /\  AllIdenticalValues(B)
        /\  o.val = PickValue(B)
        /\  o.val \in {a.lastVal : a \in B}
        /\  \A a \in B : a.lastVal = o.val
    BY <1>4, PickValueImage DEF AllIdenticalValues, TypeOK, QuorumAnswers, Answers
  <1>7 \E Q \in Quorums : \E A \in QuorumAnswers(Q): 
          /\ \A a \in A : a.lastRound = o.round - 1 
          /\ \A a \in A : a.lastVal = o.val
    BY <1>5, <1>6
  <1>8 QED
    BY <1>7
  
(*****************************************************************************)
(* All primed answers in a given round must refer to the same value.         *)
(*                                                                           *)
(* The proof follows from a combination of `PrimedOfferFollowsUniformAnswer' *)
(* and the quorum intersection property.                                     *)
(*****************************************************************************)
LEMMA SingularityOfPrimedRoundAnswers ==
    TypeOK /\ MsgInv /\ ConsInv => 
        \A m1, m2 \in msgs : 
            m1.type = "Answer" /\ m1.lastPrimed /\ m2.type = "Answer" /\ m2.lastPrimed /\
            m1.lastRound = m2.lastRound 
                => m1.lastVal = m2.lastVal
  <1> SUFFICES ASSUME TypeOK /\ MsgInv /\ ConsInv,
                      NEW m1 \in msgs,    NEW m2 \in msgs,
                      m1.type = "Answer", m2.type = "Answer",
                      m1.lastPrimed,      m2.lastPrimed,
                      m1.lastRound = m2.lastRound
               PROVE  m1.lastVal = m2.lastVal
    OBVIOUS
  <1>1 \E o \in msgs : o.type = "Offer" /\ o.round = m1.lastRound /\ o.primed /\ o.val = m1.lastVal
    BY DEF MsgInv
  <1>2 \E o \in msgs : o.type = "Offer" /\ o.round = m2.lastRound /\ o.primed /\ o.val = m2.lastVal
    BY DEF MsgInv
  <1>3 PICK o1 \in msgs : o1.type = "Offer" /\ o1.round = m1.lastRound /\ o1.primed /\ o1.val = m1.lastVal
    BY <1>1
  <1>4 PICK o2 \in msgs : o2.type = "Offer" /\ o2.round = m2.lastRound /\ o2.primed /\ o2.val = m2.lastVal
    BY <1>2
  <1>5 \E R \in Quorums : \E B \in QuorumAnswers(R) :
          \A a \in B : a.lastRound = o1.round - 1 /\ a.lastVal = o1.val
    BY <1>1, <1>3, PrimedOfferFollowsUniformAnswers
  <1>6 \E R \in Quorums : \E B \in QuorumAnswers(R) :
          \A a \in B : a.lastRound = o2.round - 1 /\ a.lastVal = o2.val
    BY <1>2, <1>4, PrimedOfferFollowsUniformAnswers
  <1>7 \E R \in Quorums : \E B \in QuorumAnswers(R) :
           \A a \in B : a.lastRound = m1.lastRound - 1 /\ a.lastVal = m1.lastVal /\ a.type = "Answer"
    BY <1>1, <1>3, <1>5 DEF QuorumAnswers, Answers
  <1>8 PICK R1 \in Quorums : \E B \in QuorumAnswers(R1) :
          \A a \in B : a.lastRound = m1.lastRound - 1 /\ a.lastVal = m1.lastVal /\ a.cons \in R1
    BY <1>7 DEF QuorumAnswers, Answers
  <1>9 \E R \in Quorums : \E B \in QuorumAnswers(R) :
           \A a \in B : a.lastRound = m1.lastRound - 1 /\ a.lastVal = m2.lastVal /\ a.type = "Answer"
    BY <1>2, <1>4, <1>6 DEF QuorumAnswers, Answers
  <1>10 PICK R2 \in Quorums : \E B \in QuorumAnswers(R2) :
           \A a \in B : a.lastRound = m1.lastRound - 1 /\ a.lastVal = m2.lastVal /\ a.cons \in R2
    BY <1>9 DEF QuorumAnswers, Answers
  <1>11 PICK c \in Consenters : c \in R1 /\ c \in R2
    BY <1>8, <1>10, QuorumAssumption
  <1>12 \E B \in QuorumAnswers(R1) : \E a \in B : 
            a.lastRound = m1.lastRound - 1 /\ a.lastVal = m1.lastVal /\ a.cons = c
    BY <1>8, <1>11 DEF QuorumAnswers, Answers
  <1>13 \E B \in QuorumAnswers(R2) : \E a \in B : 
            a.lastRound = m1.lastRound - 1 /\ a.lastVal = m2.lastVal /\ a.cons = c
    BY <1>10, <1>11 DEF QuorumAnswers, Answers
  <1>14 QED
    BY <1>12, <1>13 DEF QuorumAnswers, Answers, ConsInv
  
(*****************************************************************************)
(* A set of quorum-answers of primed values for identical rounds is uniform. *)
(*****************************************************************************)
LEMMA PrimedRoundQuorumAnswersAreUniform ==
    TypeOK /\ MsgInv /\ ConsInv => 
        \A Q \in Quorums : \A A \in QuorumAnswers(Q) : 
            AllPrimed(A) /\ AllIdenticalRounds(A) => \A m1, m2 \in A : m1.lastVal = m2.lastVal
  <1> SUFFICES ASSUME TypeOK, MsgInv, ConsInv,
                      NEW Q \in Quorums,
                      NEW A \in QuorumAnswers(Q),
                      AllPrimed(A) /\ AllIdenticalRounds(A),
                      NEW m1 \in A, NEW m2 \in A
               PROVE  m1.lastVal = m2.lastVal
    OBVIOUS
  <1>1 /\ m1 \in msgs         /\ m2 \in msgs 
       /\ m1.type = "Answer"  /\ m2.type = "Answer" 
       /\ m1.lastPrimed       /\ m2.lastPrimed 
       /\ m1.lastRound = m2.lastRound
    BY DEF QuorumAnswers, Answers, AllPrimed, AllIdenticalRounds
  <1> QED
    BY <1>1, SingularityOfPrimedRoundAnswers

(*****************************************************************************)
(* Whether the value `v' was chosen in round `r'.                            *)
(*****************************************************************************) 
ChosenIn(r, v) ==  
    \E Q \in Quorums :
        \E A \in QuorumAnswers(Q) :
            /\  AllIdenticalRounds(A) 
            /\  AllPrimed(A)
            /\  \E m \in A : m.lastVal = v /\ m.lastRound = r
            
(*****************************************************************************)
(* Whether the set of values `V' was not among those offered in round        *)
(* `r'.                                                                      *)
(*****************************************************************************) 
NotOfferedIn(r, V) ==
    ~\E m \in msgs : m.type = "Offer" /\ m.round = r /\ m.val \in V

(*****************************************************************************)
(* Whether the value `v' was offered in round `r'.                           *)
(*****************************************************************************) 
OfferedIn(r, v) ==
    \E o \in msgs : o.type = "Offer" /\ o.round = r /\ o.val = v
    
(*****************************************************************************)
(* Whether an answer in round `r' referred to the value `v'.                 *)
(*****************************************************************************) 
AnsweredIn(r, v) ==
    \E o \in msgs : o.type = "Answer" /\ o.lastRound = r /\ o.lastVal = v

(*****************************************************************************)
(* A value that was chosen in a round must be among those values that were   *)
(* offered in that round.                                                    *)
(*****************************************************************************)    
LEMMA ChosenFromOffer ==
    MsgInv =>
        \A r \in Rounds, v \in Values : ChosenIn(r, v) => OfferedIn(r, v)
  <1> SUFFICES ASSUME MsgInv,
                      NEW r \in Rounds, NEW v \in Values,
                      NEW Q \in Quorums,
                      NEW A \in QuorumAnswers(Q),
                      AllIdenticalRounds(A),
                      AllPrimed(A),
                      NEW m \in A,
                      m.lastVal = v /\ m.lastRound = r
               PROVE  OfferedIn(r, v)
    BY DEF ChosenIn
  <1>1 \E a \in A : a.lastRound = r
    BY DEF ChosenIn, AllIdenticalRounds
  <1>2 \E o \in msgs : o.type = "Offer" /\ o.round = m.lastRound /\ o.val = m.lastVal
    BY DEF MsgInv, QuorumAnswers, Answers
  <1>3 QED
    BY <1>1, <1>2 DEF OfferedIn

(*****************************************************************************)
(* An offer in a non-zero round `r' must source its value from an answer     *)
(* in `r - 1'.                                                               *)
(*****************************************************************************)
LEMMA ValuePropagation ==
    TypeOK /\ MsgInv =>
        \A r \in Rounds, v \in Values : r # 0 /\ OfferedIn(r, v) => AnsweredIn(r - 1, v)
  <1> SUFFICES ASSUME MsgInv, TypeOK,
                      NEW r \in Rounds, NEW v \in Values,
                      r # 0,
                      NEW o \in msgs,
                      o.type = "Offer" /\ o.round = r /\ o.val = v
               PROVE  AnsweredIn(r - 1, v)
    BY DEF OfferedIn
  <1>1 \A n \in msgs : n.type = "Offer" /\ n.round = r /\ n.val = v =>
            /\ n.primed => 
                \E R \in Quorums : \E B \in QuorumAnswers(R) :
                    /\  AllIdenticalRounds(B) /\ AllIdenticalValues(B)
                    /\  n.val = PickValue(B)
                    /\  n.round = PickRound(B) + 1
            /\ ~n.primed =>
                \E R \in Quorums : \E B \in QuorumAnswers(R) :
                    /\  AllIdenticalRounds(B)
                    /\  n.val \in SuccessorValues(B)
                    /\  n.round = PickRound(B) + 1
            /\ \E a \in msgs : a.type = "Answer" /\ a.lastRound = r - 1 /\ a.lastVal = v
    <2> SUFFICES ASSUME NEW n \in msgs,
                        n.type = "Offer" /\ n.round = r /\ n.val = v,
                        n.primed => 
                            \E R \in Quorums : \E B \in QuorumAnswers(R) :
                                /\  AllIdenticalRounds(B) /\ AllIdenticalValues(B)
                                /\  n.val = PickValue(B)
                                /\  n.round = PickRound(B) + 1,
                        ~n.primed =>
                            \E R \in Quorums : \E B \in QuorumAnswers(R) :
                                /\  AllIdenticalRounds(B)
                                /\  n.val \in SuccessorValues(B)
                                /\  n.round = PickRound(B) + 1
                     PROVE \E a \in msgs : a.type = "Answer" /\ a.lastRound = r - 1 /\ a.lastVal = v
      BY DEF MsgInv, Rounds
    <2>1.CASE n.primed
      <3>1 PICK R \in Quorums : \E B \in QuorumAnswers(R) :
              /\  AllIdenticalRounds(B) /\ AllIdenticalValues(B)
              /\  n.val = PickValue(B)
              /\  n.round = PickRound(B) + 1
        BY <2>1
      <3>2 PICK B \in QuorumAnswers(R) : 
              /\  AllIdenticalRounds(B) /\ AllIdenticalValues(B)
              /\  n.val = PickValue(B)
              /\  n.round = PickRound(B) + 1
        BY <3>1
      <3>3 \A m1, m2 \in B : m1.lastRound = m2.lastRound
        BY <3>2 DEF AllIdenticalRounds
      <3>4 B # {}
        BY <3>2, QuorumAssumption DEF QuorumAnswers, Answers
      <3>5 PickRound(B) \in {mmm.lastRound : mmm \in B}
        BY <3>2, <3>4, PickRoundImage DEF PickRound
      <3>6 \A b \in B : b.type = "Answer" /\ b.lastRound \in Rounds
        BY <3>2 DEF QuorumAnswers, Answers, TypeOK, Messages
      <3>7 PickRound(B) \in Rounds
        BY <3>2, <3>4, <3>6, PickRoundImage DEF PickRound
      <3>8 n.round - 1 \in {mmm.lastRound : mmm \in B}
        BY <3>5, <3>2, <3>7 DEF Rounds
      <3>9 \A b \in B : b.lastRound = r - 1
        BY <3>2, <3>3, <3>5, <3>8 DEF Rounds
      <3>10 \E b \in B : b.lastVal = n.val
        BY <3>2, <3>4, PickValueImage DEF PickValue
      <3>11 QED
        BY <3>9, <3>10 DEF QuorumAnswers, Answers
    <2>2 CASE ~n.primed
      <3>1 PICK R \in Quorums : \E B \in QuorumAnswers(R) :
              /\  AllIdenticalRounds(B)
              /\  n.val \in SuccessorValues(B)
              /\  n.round = PickRound(B) + 1
        BY <2>2
      <3>2 PICK B \in QuorumAnswers(R) :
              /\  AllIdenticalRounds(B)
              /\  n.val \in SuccessorValues(B)
              /\  n.round = PickRound(B) + 1
        BY <3>1
      <3>3 \A m1, m2 \in B : m1.lastRound = m2.lastRound
        BY <3>2 DEF AllIdenticalRounds
      <3>4 B # {}
        BY <3>2, QuorumAssumption DEF QuorumAnswers, Answers
      <3>5 PickRound(B) \in {mmm.lastRound : mmm \in B}
        BY <3>2, <3>4, PickRoundImage DEF PickRound
      <3>6 \A b \in B : b.type = "Answer" /\ b.lastRound \in Rounds
        BY <3>2 DEF QuorumAnswers, Answers, TypeOK, Messages
      <3>7 PickRound(B) \in Rounds
        BY <3>2, <3>4, <3>6, PickRoundImage DEF PickRound, QuorumAnswers, Answers
      <3>8 n.round - 1 \in {mmm.lastRound : mmm \in B}
        BY <3>5, <3>2, <3>7 DEF Rounds
      <3>9 \A b \in B : b.lastRound = r - 1
        BY <3>2, <3>3, <3>8
      <3>10 \A b \in B : b \in Messages
        BY <3>2 DEF TypeOK, QuorumAnswers, Answers
      <3>11 n.val \in {b.lastVal : b \in B}
         BY <3>2, <3>4, <3>10, SuccessorValuesImage
      <3>12 QED
        BY <3>9, <3>11 DEF QuorumAnswers, Answers
    <2>3 QED
      BY <2>1, <2>2
  <1>2 QED
    BY <1>1 DEF AnsweredIn

(*****************************************************************************)
(* If a set of values `V' is not offered in round `r', then it is also not   *)
(* offered in `r + 1'. This is a set-oriented variant of                     *)
(* `ValuePropagation' that is used as the basis for an induction proof of    *)
(* of `NotOfferedInSuffix'.                                                  *)
(*****************************************************************************)
LEMMA NotOfferedInCarry ==
    TypeOK /\ MsgInv =>
        \A r \in Nat, V \in SUBSET Values : NotOfferedIn(r, V) => NotOfferedIn(r + 1, V)
  <1> SUFFICES ASSUME MsgInv, TypeOK,
                      NEW r \in Nat, NEW V \in SUBSET Values,
                      NotOfferedIn(r, V)
               PROVE  NotOfferedIn(r + 1, V)
    OBVIOUS
  <1>1 USE DEF NotOfferedIn
  <1>2 ~\E o \in msgs : o.type = "Offer" /\ o.round = r /\ o.val \in V
    OBVIOUS
  <1>3 ~\E a \in msgs : a.type = "Answer" /\ a.lastRound = r /\ a.lastVal \in V
    BY <1>2 DEF MsgInv
  <1>4 \A a \in msgs : a.type = "Answer" /\ a.lastRound = r => a.lastVal \notin V
    BY <1>3
  <1>5 \A o \in msgs : o.type = "Offer" /\ o.round = r + 1 => 
           \E a \in msgs : a.type = "Answer" /\ a.lastRound = r /\ a.lastVal = o.val
    BY ValuePropagation DEF OfferedIn, AnsweredIn, Messages, TypeOK
  <1>6 \A o \in msgs : o.type = "Offer" /\ o.round = r + 1 => 
           \E a \in msgs : a.type = "Answer" /\ a.lastRound = r /\ a.lastVal = o.val /\ a.lastVal \notin V
    BY <1>5, <1>4
  <1>7 QED
    BY <1>6  

(*****************************************************************************)
(* If a set of values `V' is not offered in some round `r1', then it is not  *)
(* offered in any round `r2' where `r2' is greater than or equal to `r1'.    *)
(*                                                                           *)
(* The proof is by naturals induction of `NotOfferedInCarry'.                *)
(*****************************************************************************)  
LEMMA NotOfferedInSuffix ==
  ASSUME TypeOK, MsgInv,
         NEW r \in Rounds, 
         NEW V \in SUBSET Values,
         NotOfferedIn(r, V)
  PROVE \A i \in Rounds : i >= r => NotOfferedIn(i, V)
  <1> DEFINE Q(i) == i \in Rounds /\ i >= r => NotOfferedIn(i, V)
  <1> SUFFICES \A i \in Rounds : Q(i)
    OBVIOUS
  <1>1 Q(0)
    BY DEF Rounds
  <1>2 \A i \in Rounds : Q(i) => Q(i + 1)
    BY NotOfferedInCarry DEF Rounds
  <1> HIDE DEF Q
  <1> QED
    BY <1>1, <1>2, NatInduction DEF Rounds

(*****************************************************************************)
(* Any set of quorum-answers in round `r' overlaps with every other set      *)
(* in `r' by at least one answer.                                            *)
(*                                                                           *)
(* Proof is straightforward by the quorum intersection property and the      *)
(* constraint that a consenter may vote at most once in any given round.     *)
(*****************************************************************************)
LEMMA RoundAnswersOverlap ==
    ConsInv =>
        \A Q, R \in Quorums : \A A \in QuorumAnswers(Q), B \in QuorumAnswers(R) : 
            (\A a \in A, b \in B : a.lastRound = b.lastRound) => 
                \E a \in A, b \in B : a = b
  BY QuorumAssumption DEF ConsInv, QuorumAnswers, Answers

(*****************************************************************************)
(* If a value `v' is chosen in round `r', then only `v' may be offered in    *)
(* the successor round `r + 1'.                                              *) 
(*****************************************************************************)
LEMMA ChosenCarry ==
    TypeOK /\ MsgInv /\ ConsInv =>
        \A r \in Rounds, v1, v2 \in Values : ChosenIn(r, v1) /\ OfferedIn(r + 1, v2) => v1 = v2
  <1> SUFFICES ASSUME TypeOK, MsgInv, ConsInv,
                      NEW r \in Rounds, NEW v1 \in Values, NEW v2 \in Values,
                      NEW Q \in Quorums,
                      NEW A \in QuorumAnswers(Q),
                      AllIdenticalRounds(A),
                      AllPrimed(A),
                      NEW m \in A,
                      m.lastVal = v1 /\ m.lastRound = r,
                      NEW o \in msgs,
                      o.type = "Offer" /\ o.round = (r + 1) /\ o.val = v2
               PROVE  v1 = v2
    BY DEF ChosenIn, OfferedIn
  <1>1 \A mmm \in A : mmm.type = "Answer" /\ mmm.lastRound = r /\ mmm.lastPrimed
    BY DEF QuorumAnswers, Answers, AllIdenticalRounds, AllPrimed
  <1>2 \A mmm \in A : mmm.lastVal = v1
    BY PrimedRoundQuorumAnswersAreUniform
  <1>3 \A n \in msgs : n.type = "Offer" /\ n.round = r + 1 =>
            /\ n.primed => 
                \E R \in Quorums : \E B \in QuorumAnswers(R) :
                    /\  AllIdenticalRounds(B) /\ AllIdenticalValues(B)
                    /\  n.val = PickValue(B)
                    /\  n.round = PickRound(B) + 1
            /\ ~n.primed =>
                \E R \in Quorums : \E B \in QuorumAnswers(R) :
                    /\  AllIdenticalRounds(B)
                    /\  n.val \in SuccessorValues(B)
                    /\  n.round = PickRound(B) + 1
            /\ n.val = v1
    <2> SUFFICES ASSUME NEW n \in msgs,
                        n.type = "Offer" /\ n.round = r + 1,
                        n.primed => 
                            \E R \in Quorums : \E B \in QuorumAnswers(R) :
                                /\  AllIdenticalRounds(B) /\ AllIdenticalValues(B)
                                /\  n.val = PickValue(B)
                                /\  n.round = PickRound(B) + 1,
                        ~n.primed =>
                            \E R \in Quorums : \E B \in QuorumAnswers(R) :
                                /\  AllIdenticalRounds(B)
                                /\  n.val \in SuccessorValues(B)
                                /\  n.round = PickRound(B) + 1
                     PROVE   n.val = v1
      BY DEF MsgInv, Rounds
    \* Where the next-round `r + 1' offer is primed, the quorum-answers in `r' must
    \* therefore have been uniform. Because `r' contained the chosen answer `v1', every
    \* set of quorum-answers in `r' must contain at least one answer with `v1' by
    \* lemma `RoundAnswersOverlap'. Seeing that `B' is uniform, then all answers in 
    \* `B' contain `v1'. 
    <2>1.CASE n.primed
      <3>1 PICK R \in Quorums : \E B \in QuorumAnswers(R) :
              /\  AllIdenticalRounds(B) /\ AllIdenticalValues(B)
              /\  n.val = PickValue(B)
              /\  n.round = PickRound(B) + 1
        BY <2>1
      <3>2 PICK B \in QuorumAnswers(R) : 
              /\  AllIdenticalRounds(B) /\ AllIdenticalValues(B)
              /\  n.val = PickValue(B)
              /\  n.round = PickRound(B) + 1
        BY <3>1
      <3>3 \A m1, m2 \in B : m1.lastRound = m2.lastRound
        BY <3>2 DEF AllIdenticalRounds
      <3>4 B # {}
        BY <3>2, QuorumAssumption DEF QuorumAnswers, Answers
      <3>5 PickRound(B) \in {mmm.lastRound : mmm \in B}
        BY <3>2, <3>4, PickRoundImage DEF PickRound
      <3>6 \A b \in B : b.type = "Answer" /\ b.lastRound \in Rounds
        BY <3>2 DEF QuorumAnswers, Answers, TypeOK, Messages
      <3>7 PickRound(B) \in Rounds
        BY <3>2, <3>4, <3>6, PickRoundImage DEF PickRound
      <3>8 n.round - 1 \in {mmm.lastRound : mmm \in B}
        BY <2>1, <3>5, <3>2, <3>7 DEF Rounds
      <3>9 \A b \in B : b.lastRound = r
        BY <2>1, <3>2, <3>3, <3>5, <3>8 DEF Rounds
      <3>10 \A a \in A, b \in B : a.lastRound = b.lastRound
        BY <1>1, <3>9
      <3>11 \E a \in A, b \in B : a = b
        BY <3>9, <3>10, RoundAnswersOverlap
      <3>12 \A b \in B : b.lastVal = v1
        BY <1>2, <3>2, <3>11 DEF AllIdenticalValues
      <3>13 QED
        BY <3>2, <3>4, <3>12, PickValueImage DEF PickValue
    \* When the next-round `r + 1' offer is unprimed, the quorum-answers in `r' may
    \* contain a mix of values. Because `r' contained the chosen answer `v1', every
    \* set of quorum-answers in `r' must contain a primed `v1' by lemma 
    \* `RoundAnswersOverlap'. Furthermore, by
    \* lemma `SingularityOfPrimedRoundAnswers', no value other than `v1' may be primed
    \* in `r'. By the image of `SuccessorValues', the sole successor value must
    \* therefore be `v1'.
    <2>2 CASE ~n.primed
      <3>1 PICK R \in Quorums : \E B \in QuorumAnswers(R) :
              /\  AllIdenticalRounds(B)
              /\  n.val \in SuccessorValues(B)
              /\  n.round = PickRound(B) + 1
        BY <2>2
      <3>2 PICK B \in QuorumAnswers(R) :
              /\  AllIdenticalRounds(B)
              /\  n.val \in SuccessorValues(B)
              /\  n.round = PickRound(B) + 1
        BY <3>1
      <3>3 B # {}
        BY <3>2, QuorumAssumption DEF QuorumAnswers, Answers
      <3>4 \A b \in B : b.type = "Answer" /\ b.lastRound \in Rounds
        BY <3>2 DEF QuorumAnswers, Answers, TypeOK, Messages
      <3>5 \A m1, m2 \in B : m1.lastRound = m2.lastRound
        BY <3>2 DEF AllIdenticalRounds
      <3>6 PickRound(B) \in {mmm.lastRound : mmm \in B}
        BY <3>2, <3>3, PickRoundImage DEF PickRound
      <3>7 PickRound(B) \in Rounds
        BY <3>2, <3>3, <3>4, PickRoundImage DEF PickRound, QuorumAnswers, Answers
      <3>8 n.round - 1 \in {mmm.lastRound : mmm \in B}
        BY <2>2, <3>2, <3>4, <3>6 DEF Rounds
      <3>9 \A b \in B : b.lastRound = r
        BY <2>2, <3>2, <3>3, <3>5, <3>8 DEF Rounds
      <3>10 \A a \in A, b \in B : a.lastRound = b.lastRound
        BY <1>1, <3>9
      <3>11 \E a \in A, b \in B : a = b
        BY <3>9, <3>10, RoundAnswersOverlap
      <3>12 \E b \in B : b.lastVal = v1 /\ b.lastPrimed
        BY <1>2, <3>11 DEF AllPrimed
      <3>13 PICK p \in B : p.lastVal = v1 /\ p.lastPrimed
        BY <3>12
      <3>14 MaxLastRound(B) = r
        BY <3>3, <3>9 DEF MaxLastRound, SetMax
      <3>15 DEFINE highestRoundAnswers == {b \in B : b.lastRound = MaxLastRound(B)}
      <3>16 highestRoundAnswers = B
        BY <3>9, <3>14
      <3>17 \A b \in B : b \in msgs
        BY <3>1, <3>2 DEF QuorumAnswers, Answers
      <3>18 \A b \in B : b.lastPrimed /\ b.lastRound = r => b.lastVal = v1
        BY <3>4, <3>9, <3>13, <3>17, SingularityOfPrimedRoundAnswers
      <3>19 DEFINE highestRoundPrimedAnswers == {b \in highestRoundAnswers : b.lastPrimed}
      <3>20 highestRoundPrimedAnswers = {b \in B : b.lastPrimed}
        BY <3>16
      <3>21 highestRoundPrimedAnswers # {}
        BY <3>12, <3>18, <3>20
      <3>22 \A mmm \in highestRoundPrimedAnswers : mmm.lastVal = v1
        BY <3>9, <3>18
      <3>23 \A v \in SuccessorValues(B) : v = v1
        BY <3>21, <3>22 DEF SuccessorValues, PickValue
      <3>24 HIDE DEF highestRoundAnswers, highestRoundPrimedAnswers
      <3>25 QED
        BY <3>2, <3>23
    <2>3. QED
      BY <2>1, <2>2
  <1>4 QED 
    BY <1>3
        
(*****************************************************************************)
(* Stability of value selection.                                             *)
(*                                                                           *)
(* For any two rounds `r1' and `r2', where `r1 < r2', if some value `v' is   *)
(* chosen in `r1' then only `v' may be offered in `r2'.                      *)
(*                                                                           *)
(* The proof is assembled in two tranches. First, we prove that if `v' is    *)
(* chosen in `r1', then only `v' may be offered in `r1 + 1' by lemma         *)
(* `ChosenCarry'. Second, if `v' is offered in `r1 + 1', then only `v' may   *)
(* be offered in all future rounds following `r1 + 1'. The latter is         *)
(* accomplished by rewriting the obligations in terms of what cannot be      *)
(* offered, which is the set `Values \ {v}', and using the inductive lemma   *)
(* `NotOfferedInSuffix' to project that `Values \ {v}' cannot be offered in  *)
(* all subsequent rounds, leaving only `v' as a candidate value in `r2'.     *)
(*****************************************************************************)
LEMMA Stability ==
    TypeOK /\ MsgInv /\ ConsInv =>
        \A r1, r2 \in Rounds, v1, v2 \in Values : r1 < r2 /\ ChosenIn(r1, v1) /\ OfferedIn(r2, v2) 
            => v1 = v2
  <1> SUFFICES ASSUME TypeOK, MsgInv, ConsInv,
                      NEW r1 \in Rounds,  NEW r2 \in Rounds, 
                      NEW v1 \in Values,  NEW v2 \in Values,
                      r1 < r2,
                      NEW Q \in Quorums,
                      NEW A \in QuorumAnswers(Q),
                      AllIdenticalRounds(A),
                      AllPrimed(A),
                      NEW m \in A,
                      m.lastVal = v1 /\ m.lastRound = r1,
                      NEW o \in msgs,
                      o.type = "Offer" /\ o.round = r2 /\ o.val = v2
               PROVE  v1 = v2
    BY DEF ChosenIn, OfferedIn
  <1>1 \E mmm \in msgs : mmm.type = "Offer" /\ mmm.round = r1 + 1 => mmm.val = v1
    BY ChosenCarry DEF ChosenIn, OfferedIn
  <1>2 \A v \in Values : OfferedIn(r1 + 1, v) => v = v1
    BY ChosenCarry DEF ChosenIn, OfferedIn
  <1>3 \A mmm \in msgs : mmm.type = "Offer" /\ mmm.round = r1 + 1 => mmm.val = v1
    BY <1>2 DEF OfferedIn, Messages, TypeOK
  <1>4 NotOfferedIn(r1 + 1, Values \ {v1})
    BY <1>3 DEF NotOfferedIn
  <1>5 NotOfferedIn(r2, Values \ {v1})
    BY <1>4, NotOfferedInSuffix DEF Rounds
  <1>6 QED
    BY <1>5 DEF NotOfferedIn, OfferedIn
  
(*****************************************************************************)
(* The initial state satisfies the inductive invariant `Inv'.                *)
(*****************************************************************************)
LEMMA Initial == Init => Inv
  BY DEF Init, Inv, MsgInv, ConsInv

(*****************************************************************************)
(* All states that satisfy the inductive invariant `Inv' also                *)
(* satisfy the `Consistency' invariant.                                      *)
(*****************************************************************************)  
LEMMA Consistent == Inv => Consistency
  <1> SUFFICES ASSUME Inv,
                      NEW v1 \in Values,          NEW v2 \in Values,
                      NEW Q \in Quorums,          NEW R \in Quorums,
                      NEW A \in QuorumAnswers(Q), NEW B \in QuorumAnswers(R),
                      AllIdenticalRounds(A),      AllIdenticalRounds(B),
                      AllPrimed(A),               AllPrimed(B),
                      NEW m \in A,                NEW n \in B,
                      m.lastVal = v1,             n.lastVal = v2
               PROVE  v1 = v2
    BY DEF Chosen, Consistency
  <1> USE DEF Inv, Consistency
  <1>1 /\ m.type = "Answer" /\ m.lastRound \in Rounds /\ n.type = "Answer" /\ n.lastRound \in Rounds 
       /\ m.lastVal \in Values /\ n.lastVal \in Values
    BY DEF Messages, QuorumAnswers, Answers
  <1>2 (\A mmm \in A : mmm.lastVal = v1) /\ (\A mmm \in B : mmm.lastVal = v2)
    BY PrimedRoundQuorumAnswersAreUniform DEF TypeOK
  \* Where the two messages `m' from `A' and `n' from `B' are in the same round, 
  \* and `AllIdenticalRounds' holds for both answer sets `A' and `B', then there
  \* must be a common answer in their intersection by lemma `RoundAnswersOverlap'.
  <1>3 CASE m.lastRound = n.lastRound
    <2>1 \A ma \in A, mb \in B : ma.lastRound = mb.lastRound
      BY <1>3 DEF AllIdenticalRounds
    <2>2 \E ma \in A, mb \in B : ma.lastVal = mb.lastVal
      BY <2>1, RoundAnswersOverlap
    <2>3 QED
      BY <1>2, <1>3, <2>2
  \* Where the two messages `m' from `A' and `n' from `B' are in different rounds
  \* and `AllIdenticalRounds' holds for both `A' and `B', then either `m' precedes
  \* `n' or `n' precedes `m'. Both sub-cases are interchangeable and proven by lemmas
  \* `Stability' and `ChosenFromOffer'.
  <1>4 CASE m.lastRound # n.lastRound
    BY <1>1, <1>4, Stability, ChosenFromOffer DEF ChosenIn, OfferedIn, TypeOK, Rounds
  <1>5 QED
    BY <1>1, <1>3, <1>4 DEF Rounds

(*****************************************************************************)
(* The inductive invariant `Inv' is preserved when `vars' is unchanged.      *)
(*                                                                           *)
(* The result is trivially determined, and has been extracted into a         *)
(* separate lemma for convenience and reuse.                                 *)
(*****************************************************************************)
LEMMA InvariantPreservedOnUnchanged ==
    Inv /\ UNCHANGED vars => Inv'
  <1> SUFFICES ASSUME Inv /\ UNCHANGED vars
               PROVE  Inv'
    OBVIOUS
  <1> USE DEF Inv, vars
  <1>1. (msgs \in SUBSET Messages)'
    OBVIOUS
  <1>2. MsgInv'
    BY DEF MsgInv, QuorumAnswers, Answers
  <1>3. (lastVal \in [Consenters -> Values \union {None}])'
    OBVIOUS
  <1>4. (lastRound \in [Consenters -> Rounds \union {-1}])'
    OBVIOUS
  <1>5. (lastPrimed \in [Consenters -> BOOLEAN])'
    OBVIOUS
  <1>6. ConsInv'
    BY DEF ConsInv
  <1>7. QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Inv

(*****************************************************************************)
(* Preservation of the inductive invariant.                                  *)
(*                                                                           *)
(* Starting from any state that satisfies the inductive invariant `Inv', all *)
(* enabled transitions will result in some successor state that also         *)
(* satisfies `Inv'.                                                          *)
(*****************************************************************************)
LEMMA Inductive == Inv /\ Next => Inv'
  <1> SUFFICES ASSUME Inv,
                      Next
               PROVE  Inv'
    OBVIOUS
  <1> USE DEF Inv, Next
  <1>1. CASE Offer
    <2> USE DEF Offer
    <2>1. (msgs \in SUBSET Messages)'
      <3>1. ASSUME NEW Q \in Quorums,
                   NEW A \in QuorumAnswers(Q),
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
            PROVE  (msgs \in SUBSET Messages)'
        <4>1 A \in SUBSET Messages /\ A # {}
          BY QuorumAssumption DEF QuorumAnswers, Answers
        <4>2 PickRound(A) \in Rounds
          BY <3>1, <4>1, PickRoundImage DEF QuorumAnswers, Answers, Messages
        <4>3 SuccessorValues(A) \in SUBSET Values
          BY <3>1, <4>1, SuccessorValuesImage DEF QuorumAnswers, Answers, Messages
        <4>4 CASE AllIdenticalRounds(A)
          <5>1 CASE AllIdenticalValues(A)
            <6>1 PickValue(A) \in Values
              BY <3>1, <4>1, PickValueImage DEF QuorumAnswers, Answers, Messages
            <6>2 DEFINE n == [type |-> "Offer", val |-> PickValue(A), round |-> PickRound(A) + 1, primed |-> TRUE]
            <6>3 n \in Messages
              BY <4>2, <6>1 DEF Messages, Rounds
            <6>4 QED
              BY <3>1, <4>4, <5>1, <6>3 DEF TrySend, Send
          <5>2 CASE ~AllIdenticalValues(A)
            <6>1 PICK v \in SuccessorValues(A) : 
                    TrySend([type |-> "Offer", val |-> v, round |-> PickRound(A) + 1, primed |-> FALSE])
              BY <3>1, <4>4, <5>2
            <6>2 DEFINE n == [type |-> "Offer", val |-> v, round |-> PickRound(A) + 1, primed |-> FALSE]
            <6>3 n \in Messages
              BY <4>2, <4>3 DEF Messages, Rounds
            <6>4 QED
              BY <3>1, <4>4, <5>2, <6>1, <6>3 DEF TrySend, Send
          <5>3 QED
            BY <1>1, <3>1, <4>4, <5>1, <5>2
        <4>5 CASE ~AllIdenticalRounds(A)
          <5>1 \A mmm \in A : mmm.lastRound \in Rounds
            BY <3>1, <4>1 DEF Messages, QuorumAnswers, Answers
          <5>2 MaxLastRound(A) \in {m.lastRound : m \in A}
            BY <3>1, <4>1, MaxLastRoundImage
          <5>3 MaxLastRound(A) \in Rounds
            BY <5>1, <5>2
          <5>4 PICK v \in SuccessorValues(A) : 
                  TrySend([type |-> "Offer", val |-> v, round |-> MaxLastRound(A), primed |-> FALSE])
             BY <3>1, <4>4, <4>5
          <5>5 DEFINE n == [type |-> "Offer", val |-> v, round |-> MaxLastRound(A), primed |-> FALSE]
          <5>6 n \in Messages
            BY <4>3, <5>3, <5>4 DEF Messages, Rounds
          <5>7 QED
            BY <1>1, <3>1, <4>5, <5>4, <5>6 DEF TrySend, Send
        <4>6 QED
          BY <1>1, <3>1, <4>4, <4>5
      <3>2. ASSUME NEW v \in Values,
                   TrySend([type |-> "Offer", val |-> v, round |-> 0, primed |-> FALSE])
            PROVE  (msgs \in SUBSET Messages)'
        <4>1 DEFINE n == [type |-> "Offer", val |-> v, round |-> 0, primed |-> FALSE]
        <4>2 n \in Messages
          BY DEF Messages, Rounds
        <4>3 QED
          BY <1>1, <3>2, <4>2 DEF Messages, TrySend, Send
      <3>3. QED
        BY <1>1, <3>1, <3>2
    <2>2. MsgInv'
      <3> USE DEF MsgInv
      <3>1. ASSUME NEW Q \in Quorums,
                   NEW A \in QuorumAnswers(Q),
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
            PROVE  MsgInv'
        <4>4 CASE AllIdenticalRounds(A)
          <5>1 CASE AllIdenticalValues(A)
            <6> SUFFICES ASSUME NEW m \in msgs'
                         PROVE  (/\  m.type = "Offer" =>
                                         /\  m.round = 0 => ~m.primed
                                         /\  m.round # 0 =>
                                                 /\ m.primed => 
                                                     \E R \in Quorums : \E B \in QuorumAnswers(R) :
                                                         /\  AllIdenticalRounds(B) /\ AllIdenticalValues(B)
                                                         /\  m.val = PickValue(B)
                                                         /\  m.round = PickRound(B) + 1
                                                 /\ ~m.primed =>
                                                     \E R \in Quorums : \E B \in QuorumAnswers(R) :
                                                         /\  AllIdenticalRounds(B)
                                                         /\  m.val \in SuccessorValues(B)
                                                         /\  m.round = PickRound(B) + 1
                                 /\  m.type = "Answer" =>
                                         \E o \in msgs : 
                                             /\  o.type = "Offer"
                                             /\  o.round = m.lastRound
                                             /\  o.val = m.lastVal
                                             /\  o.primed = m.lastPrimed)'
              BY DEF MsgInv
            <6>1. (m.type = "Offer" =>
                       /\  m.round = 0 => ~m.primed
                       /\  m.round # 0 =>
                               /\ m.primed => 
                                   \E R \in Quorums : \E B \in QuorumAnswers(R) :
                                       /\  AllIdenticalRounds(B) /\ AllIdenticalValues(B)
                                       /\  m.val = PickValue(B)
                                       /\  m.round = PickRound(B) + 1
                               /\ ~m.primed =>
                                   \E R \in Quorums : \E B \in QuorumAnswers(R) :
                                       /\  AllIdenticalRounds(B)
                                       /\  m.val \in SuccessorValues(B)
                                       /\  m.round = PickRound(B) + 1)'
              <7>1 msgs' = msgs \union {[type |-> "Offer", val |-> PickValue(A), round |-> PickRound(A) + 1, primed |-> TRUE]}
                BY <3>1, <4>4, <5>1 DEF TrySend, Send
              \* Round-0 case holds for existing messages. For new messages, a round-0 offer is never issued in the case of 
              \* `AllIdenticalRounds(A) /\ AllIdenticalValues(A)' because `PickRound(A) + 1' results in a round number 
              \* that exceeds 0.
              <7>2. CASE m.type = "Offer" /\ m.round = 0
                <8>1 A \in SUBSET Messages /\ A # {} /\ \A a \in A : a.lastRound \in Rounds
                  BY <3>1, QuorumAssumption DEF QuorumAnswers, Answers, Messages
                <8>2 PickRound(A) \in Rounds
                  BY <8>1, PickRoundImage
                <8>3 PickRound(A) + 1 > 0
                  BY <8>2 DEF Rounds
                <8>4 QED
                  BY <7>1, <7>2, <8>3
              \* Non-zero round with a primed offer: either `m' is in `msgs' (invariant is preserved) or, if `m' is
              \* the newly sent message, by a simple consequence of the definition of `Offer'.
              <7>3 CASE m.type = "Offer" /\ m.round # 0 /\ m.primed
                <8>1 CASE m \in msgs
                  BY <7>1, <7>3, <8>1 DEF QuorumAnswers, Answers
                <8>2 CASE m \notin msgs
                  BY <3>1, <4>4, <5>1, <7>1, <7>3, <8>2 DEF QuorumAnswers, Answers
                <8>3 QED
                  BY <8>1, <8>2
              \* Non-zero round with an unprimed offer: either `m' is in `msgs' (the invariant is implicitly 
              \* preserved), or the newly sent message `m' is primed — a contradiction of the `~m.primed' conjunct
              \* in this case.
              <7>4 CASE m.type = "Offer" /\ m.round # 0 /\ ~m.primed
                <8>2 CASE m \in msgs
                  <9>1 ~m.primed
                    BY <7>4
                  <9>2 QED 
                    BY <7>1, <9>1 DEF QuorumAnswers, Answers
                <8>3 CASE m \notin msgs
                  BY <3>1, <4>4, <7>1, <7>4, <8>3 DEF QuorumAnswers, Answers
                <8>4 QED
                  BY <8>2, <8>3, <7>4
              <7>5. QED
                BY <7>2, <7>3, <7>4
            <6>2. (m.type = "Answer" =>
                       \E o \in msgs : 
                             /\  o.type = "Offer"
                             /\  o.round = m.lastRound
                             /\  o.val = m.lastVal
                             /\  o.primed = m.lastPrimed)'
              BY <3>1, <4>4, <5>1 DEF TrySend, Send
            <6>3. QED
              BY <6>1, <6>2
          <5>2 CASE ~AllIdenticalValues(A)
            <6> SUFFICES ASSUME NEW m \in msgs'
                         PROVE  (/\  m.type = "Offer" =>
                                         /\  m.round = 0 => ~m.primed
                                         /\  m.round # 0 =>
                                               /\ m.primed => 
                                                   \E R \in Quorums : \E B \in QuorumAnswers(R) :
                                                       /\  AllIdenticalRounds(B) /\ AllIdenticalValues(B)
                                                       /\  m.val = PickValue(B)
                                                       /\  m.round = PickRound(B) + 1
                                               /\ ~m.primed =>
                                                   \E R \in Quorums : \E B \in QuorumAnswers(R) :
                                                       /\  AllIdenticalRounds(B)
                                                       /\  m.val \in SuccessorValues(B)
                                                       /\  m.round = PickRound(B) + 1
                                 /\  m.type = "Answer" =>
                                         \E o \in msgs : 
                                               /\  o.type = "Offer"
                                               /\  o.round = m.lastRound
                                               /\  o.val = m.lastVal
                                               /\  o.primed = m.lastPrimed)'
              BY DEF MsgInv
            <6>1. (m.type = "Offer" =>
                       /\  m.round = 0 => ~m.primed
                       /\  m.round # 0 =>
                               /\ m.primed => 
                                   \E R \in Quorums : \E B \in QuorumAnswers(R) :
                                       /\  AllIdenticalRounds(B) /\ AllIdenticalValues(B)
                                       /\  m.val = PickValue(B)
                                       /\  m.round = PickRound(B) + 1
                               /\ ~m.primed =>
                                   \E R \in Quorums : \E B \in QuorumAnswers(R) :
                                       /\  AllIdenticalRounds(B)
                                       /\  m.val \in SuccessorValues(B)
                                       /\  m.round = PickRound(B) + 1)'
              <7>1 \E v \in SuccessorValues(A) : 
                        msgs' = msgs \union {[type |-> "Offer", val |-> v, round |-> PickRound(A) + 1, primed |-> FALSE]}
                BY <3>1, <4>4, <5>2 DEF TrySend, Send
              \* Round-0 case holds for existing messages. For new messages, a round-0 offer is never issued in the case of 
              \* `AllIdenticalRounds(A) /\ ~AllIdenticalValues(A)' because `PickRound(A) + 1' results in a round number 
              \* that exceeds 0.
              <7>2. CASE m.type = "Offer" /\ m.round = 0
                BY <7>1, <7>2
              \* Non-zero round with a primed offer: Either `m' is in `msgs' (the invariant is implicitly 
              \* preserved), or the newly sent message `m' is unprimed (a contradiction in this case).
              <7>3 CASE m.type = "Offer" /\ m.round # 0 /\ m.primed
                BY <3>1, <4>4, <7>1, <7>3 DEF QuorumAnswers, Answers
              \* Non-zero round with an unprimed offer: either `m' is in `msgs' (invariant is preserved) or, if `m' is
              \* the newly sent message, by a simple consequence of the definition of `Offer'.
              <7>4 CASE m.type = "Offer" /\ m.round # 0 /\ ~m.primed
                <8>1 msgs \subseteq msgs'
                  BY <3>1 DEF TrySend, Send
                \* When `m' is in `msgs', the invariant is preserved.
                <8>2 CASE m \in msgs
                  <9>1 (A \in QuorumAnswers(Q) /\ AllIdenticalRounds(A))'
                    BY <3>1, <4>4, <8>1 DEF QuorumAnswers, Answers, AllIdenticalRounds
                  <9>2 QED
                    BY <4>4, <7>1, <7>4, <8>1, <8>2, <9>1 DEF TrySend, Send, QuorumAnswers, Answers, AllIdenticalRounds
                \* For the `m \notin msgs' sub-case, we employ additional hints to show that the predicates
                \* `A \in QuorumAnswers(Q)', `AllIdenticalRounds(A)', `m.val \in SuccessorValues(A)'
                \* and `m.round = PickRound(A) + 1' are preserved in the next state.
                <8>3 CASE m \notin msgs
                  <9>1 \E v \in SuccessorValues(A) : 
                            m = [type |-> "Offer", val |-> v, round |-> PickRound(A) + 1, primed |-> FALSE]
                    BY <7>1, <8>3
                  <9>2 (A \in QuorumAnswers(Q) /\ AllIdenticalRounds(A))'
                    BY <3>1, <4>4, <8>1 DEF QuorumAnswers, Answers, AllIdenticalRounds
                  <9>3 (m.val \in SuccessorValues(A))'
                    BY <3>1, <4>4, <9>1
                  <9>4 (m.round = PickRound(A) + 1)'
                    BY <3>1, <4>4, <9>1
                  <9>5 QED
                    BY <7>4, <9>2, <9>3, <9>4
                <8>4 QED
                  BY <7>4, <8>2, <8>3
              <7>5. QED
                BY <7>2, <7>3, <7>4
            <6>2. (m.type = "Answer" =>
                       \E o \in msgs : 
                           /\  o.type = "Offer"
                           /\  o.round = m.lastRound
                           /\  o.val = m.lastVal
                           /\  o.primed = m.lastPrimed)'
              \* Either `msgs' is unchanged or the newly sent message is an offer.
              <7>1 \E v \in SuccessorValues(A) : 
                        msgs' = msgs \union {[type |-> "Offer", val |-> v, round |-> PickRound(A) + 1, primed |-> FALSE]}
                BY <3>1, <4>4, <5>2 DEF TrySend, Send
              <7>2 QED
                BY <7>1
            <6>3. QED
              BY <6>1, <6>2
          <5>3 QED
            BY <1>1, <3>1, <4>4, <5>1, <5>2
        <4>5 CASE ~AllIdenticalRounds(A)
          <5> SUFFICES ASSUME NEW m \in msgs'
                       PROVE  (/\  m.type = "Offer" =>
                                       /\  m.round = 0 => ~m.primed
                                       /\  m.round # 0 =>
                                            /\ m.primed => 
                                                 \E R \in Quorums : \E B \in QuorumAnswers(R) :
                                                     /\  AllIdenticalRounds(B) /\ AllIdenticalValues(B)
                                                     /\  m.val = PickValue(B)
                                                     /\  m.round = PickRound(B) + 1
                                            /\ ~m.primed =>
                                                 \E R \in Quorums : \E B \in QuorumAnswers(R) :
                                                     /\  AllIdenticalRounds(B)
                                                     /\  m.val \in SuccessorValues(B)
                                                     /\  m.round = PickRound(B) + 1
                               /\  m.type = "Answer" =>
                                       \E o \in msgs : 
                                            /\  o.type = "Offer"
                                            /\  o.round = m.lastRound
                                            /\  o.val = m.lastVal
                                            /\  o.primed = m.lastPrimed)'
            BY DEF MsgInv
          <5>1. (m.type = "Offer" =>
                     /\  m.round = 0 => ~m.primed
                     /\  m.round # 0 =>
                             /\ m.primed => 
                                   \E R \in Quorums : \E B \in QuorumAnswers(R) :
                                       /\  AllIdenticalRounds(B) /\ AllIdenticalValues(B)
                                       /\  m.val = PickValue(B)
                                       /\  m.round = PickRound(B) + 1
                             /\ ~m.primed =>
                                   \E R \in Quorums : \E B \in QuorumAnswers(R) :
                                       /\  AllIdenticalRounds(B)
                                       /\  m.val \in SuccessorValues(B)
                                       /\  m.round = PickRound(B) + 1)'
            <6>1 \E v \in SuccessorValues(A) : 
                      msgs' = msgs \union {[type |-> "Offer", val |-> v, round |-> MaxLastRound(A), primed |-> FALSE]}
              BY <3>1, <4>5 DEF TrySend, Send
            \* Round-0 case holds for existing messages, and the newly sent message is
            \* not in round 0 as the quorum-answer `A' spans multiple rounds and `MaxLastRound(A)'
            \* will therefore be greater than 0.
            <6>2 CASE m.type = "Offer" /\ m.round = 0
              BY <6>1, <6>2
            \* Non-zero round with primed offer: holds for existing messages and the newly sent
            \* message is unprimed (a contradiction in this case).
            <6>3 CASE m.type = "Offer" /\ m.round # 0 /\ m.primed
              BY <6>1, <6>3 DEF QuorumAnswers, Answers 
            \* Non-zero round with unprimed offer: See detailed comment at `MsgInv' for the case where
            \* `\A m \in msgs : m.type = "Offer" /\ m.round # 0 /\ ~m.primed', outlining the proof strategy.
            \* While the offer may have been based on a current-round answer, we rely on the `MsgInv'
            \* invariant, which states that every answer must have been in response to some
            \* offer in the same round, and every offer must have propagated the value from some
            \* answer in the immediately preceding round.
            <6>4 CASE m.type = "Offer" /\ m.round # 0 /\ ~m.primed
              \* The `m \in msgs' sub-case is trivially proven by the preservation of `msgs'.
              <7>1 CASE m \in msgs
                <8>1 \E R \in Quorums : \E B \in QuorumAnswers(R) :
                         /\  AllIdenticalRounds(B)
                         /\  m.val \in SuccessorValues(B)
                         /\  m.round = PickRound(B) + 1
                  BY <3>1, <4>5, <6>4, <7>1
                <8>2 QED
                  BY <6>1, <6>4, <8>1 DEF QuorumAnswers, Answers
              \* For the `m \notin msgs' sub-case, we tie the newly sent offer `m' to an existing
              \* answer in the current round which we pick as `a'. Then by `MsgInv', we show
              \* that `a' must have a corresponding offer `o' in the current round. We then
              \* infer that `o' must have preserved a value from the immediately preceding round
              \* by `MsgInv'. Therefore, `a' must have preserved some value from `a.round - 1'.
              <7>2 CASE m \notin msgs
                <8>1 \E v \in SuccessorValues(A) : 
                          m = [type |-> "Offer", val |-> v, round |-> MaxLastRound(A), primed |-> FALSE]
                   BY <3>1, <4>5, <6>4, <7>2 DEF TrySend, Send
                <8>2 MaxLastRound(A) = m.round
                   BY <8>1
                <8>3 A # {}
                   BY <3>1, QuorumAssumption DEF QuorumAnswers, Answers
                <8>4 SuccessorValues(A) # {}
                  BY <8>1
                <8>5 DEFINE highestRoundAnswers == {a \in A : a.lastRound = MaxLastRound(A)}
                            highestRoundPrimedAnswers == {a \in highestRoundAnswers : a.lastPrimed}
                <8>6 SuccessorValues(A) = IF highestRoundPrimedAnswers # {} THEN 
                                              {PickValue(highestRoundPrimedAnswers)}
                                           ELSE
                                              {a.lastVal : a \in highestRoundAnswers}
                   BY <3>1 DEF SuccessorValues
                <8>7 \A v \in SuccessorValues(A) : \E a \in A : a.lastVal = v /\ a.lastRound = MaxLastRound(A)
                  BY <8>6 DEF PickValue
                <8>8 HIDE DEF highestRoundAnswers, highestRoundPrimedAnswers
                <8>9 \E a \in A : a.lastRound = MaxLastRound(A) /\ a.lastVal \in SuccessorValues(A)
                  BY <8>7, <8>4
                <8>10 PICK a \in A : a.lastRound = m.round /\ a.lastVal = m.val
                  BY <8>1, <8>7
                <8>11 a \in msgs /\ a.type = "Answer"
                  BY <3>1 DEF QuorumAnswers, Answers
                <8>12 PICK o \in msgs : o.type = "Offer" /\ o.round = a.lastRound /\ o.val = a.lastVal /\ o.primed = a.lastPrimed
                  BY <3>1, <8>10, <8>11
                <8>13 o.round # 0 /\ o.val = m.val /\ o.round = m.round
                  BY <6>4, <8>12, <8>10
                <8>14 msgs \subseteq msgs'
                  BY <3>1 DEF TrySend, Send
                <8>15 m.type = "Offer" /\ m.round # 0 /\ ~m.primed
                  BY <8>1, <8>13
                <8>16 o.primed => \E R \in Quorums : \E B \in QuorumAnswers(R) :
                                       /\  AllIdenticalRounds(B) /\ AllIdenticalValues(B)
                                       /\  o.val = PickValue(B)
                                       /\  o.round = PickRound(B) + 1
                  BY <3>1, <8>10, <8>12, <8>13
                <8>17 CASE o.primed
                  <9>1 (\E R \in Quorums : \E B \in QuorumAnswers(R) :
                             /\  AllIdenticalRounds(B)
                             /\  m.val \in SuccessorValues(B)
                             /\  m.round = PickRound(B) + 1)'
                    \* When `o' is primed, the source quorum-answer set must be uniform (all identical
                    \* rounds and values). A uniform set of answers leads to a single successor value,
                    \* therefore `SuccessorValues(B)' must be a singleton set containing `PickValue(B)'.
                    BY <8>13, <8>14, <8>16, <8>17, SingularityOfSuccessorsToUniformAnswers, QuorumAssumption 
                       DEF QuorumAnswers, Answers
                  <9>2 QED
                    BY <9>1, <8>15
                <8>18 ~o.primed => \E R \in Quorums : \E B \in QuorumAnswers(R) :
                                       /\  AllIdenticalRounds(B)
                                       /\  o.val \in SuccessorValues(B)
                                       /\  o.round = PickRound(B) + 1
                  BY <3>1, <8>10, <8>12, <8>13
                <8>19 CASE ~o.primed
                  BY <8>13, <8>14, <8>15, <8>18, <8>19 DEF QuorumAnswers, Answers
                <8>20 QED
                  BY <8>17, <8>19
              <7>3
                QED BY <7>1, <7>2
            <6>5 QED 
              BY <6>2, <6>3, <6>4
          <5>2. (m.type = "Answer" =>
                     \E o \in msgs : 
                         /\  o.type = "Offer"
                         /\  o.round = m.lastRound
                         /\  o.val = m.lastVal
                         /\  o.primed = m.lastPrimed)'
            \* Existing messages are preserved and the sent message is an offer.
            <6>1 \E v \in SuccessorValues(A) : 
                      msgs' = msgs \union {[type |-> "Offer", val |-> v, round |-> MaxLastRound(A), primed |-> FALSE]}
              BY <3>1, <4>5 DEF TrySend, Send
            <6>2 QED
              BY <6>1
          <5>3. QED
            BY <5>1, <5>2
        <4>6 QED
          BY <1>1, <3>1, <4>4, <4>5
      <3>2. ASSUME NEW v \in Values,
                   TrySend([type |-> "Offer", val |-> v, round |-> 0, primed |-> FALSE])
            PROVE  MsgInv'
        <4> SUFFICES ASSUME NEW m \in msgs'
                     PROVE  (/\  m.type = "Offer" =>
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
                                         /\  o.primed = m.lastPrimed)'
          BY DEF MsgInv
        <4>1 msgs' = msgs \union {[type |-> "Offer", val |-> v, round |-> 0, primed |-> FALSE]}
          BY <3>2 DEF TrySend, Send
        <4>2. (m.type = "Offer" =>
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
                                   /\  m.round = PickRound(A) + 1)'
          \* The sent offer `m' is unprimed and for round 0, which directly satisfies the goal
          \* `m.type = "Offer" /\ m.round = 0 => ~m.primed'.
          BY <3>2, <4>1 DEF QuorumAnswers, Answers, AllIdenticalRounds, AllIdenticalValues
        <4>3. (m.type = "Answer" =>
                   \E o \in msgs : 
                       /\  o.type = "Offer"
                       /\  o.round = m.lastRound
                       /\  o.val = m.lastVal
                       /\  o.primed = m.lastPrimed)'
          \* Existing messages are preserved and the sent message is an offer.
          BY <4>1
        <4>4. QED
          BY <4>2, <4>3
      <3>3. QED
        BY <1>1, <3>1, <3>2
    <2>3. (lastVal \in [Consenters -> Values \union {None}])'
      BY <1>1 DEF TrySend
    <2>4. (lastRound \in [Consenters -> Rounds \union {-1}])'
      BY <1>1 DEF TrySend
    <2>5. (lastPrimed \in [Consenters -> BOOLEAN])'
      BY <1>1 DEF TrySend
    <2>6. ConsInv'
      <3> SUFFICES ASSUME NEW c \in Consenters'
                   PROVE  (/\  lastRound[c] = -1 <=> lastVal[c] = None
                           /\  lastRound[c] = -1 => ~lastPrimed[c]
                           /\  lastRound[c] # -1 => \E m \in msgs : 
                                   /\  m.type = "Answer" 
                                   /\  m.cons = c 
                                   /\  m.lastRound = lastRound[c]
                                   /\  m.lastVal = lastVal[c]
                                   /\  m.lastPrimed = lastPrimed[c]
                           /\  ~\E m \in msgs : m.type = "Answer" /\ m.cons = c /\ m.lastRound > lastRound[c]
                           /\  \A m1, m2 \in msgs :
                                   m1.type = "Answer" /\ m2.type = "Answer" /\ m1.cons = c /\ m2.cons = c /\ 
                                   m1.lastRound = m2.lastRound 
                                       => m1 = m2)'
        BY DEF ConsInv
      <3> USE DEF ConsInv
      <3>1. (lastRound[c] = -1 <=> lastVal[c] = None)'
        BY <1>1
      <3>2. (lastRound[c] = -1 => ~lastPrimed[c])'
        BY <1>1
      <3>3. (lastRound[c] # -1 => \E m \in msgs : 
                 /\  m.type = "Answer" 
                 /\  m.cons = c 
                 /\  m.lastRound = lastRound[c]
                 /\  m.lastVal = lastVal[c]
                 /\  m.lastPrimed = lastPrimed[c])'
        BY <1>1 DEF TrySend, Send
      <3>4. (~\E m \in msgs : m.type = "Answer" /\ m.cons = c /\ m.lastRound > lastRound[c])'
        <4>1. ASSUME NEW Q \in Quorums,
                     NEW A \in QuorumAnswers(Q),
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
              PROVE  (~\E m \in msgs : m.type = "Answer" /\ m.cons = c /\ m.lastRound > lastRound[c])'
          \* Regardless of which branch is evaluated, the new message can take one of three forms,
          \* enumerated by the following disjuncts.
          <5>1 \/ msgs' = msgs \union {[type |-> "Offer", val |-> PickValue(A), round |-> PickRound(A) + 1, primed |-> TRUE]}
               \/ \E v \in SuccessorValues(A) :
                     msgs' = msgs \union {[type |-> "Offer", val |-> v, round |-> PickRound(A) + 1, primed |-> FALSE]}
               \/ \E v \in SuccessorValues(A) :
                     msgs' = msgs \union {[type |-> "Offer", val |-> v, round |-> MaxLastRound(A), primed |-> FALSE]}
            BY <4>1 DEF TrySend, Send
          \* In any case, the new message can only be an offer.
          <5>2 \A m \in msgs' \ msgs : m.type = "Offer"
            BY <5>1
          <5>3 QED
            BY <1>1, <4>1, <5>2
        <4>2. ASSUME NEW v \in Values,
                     TrySend([type |-> "Offer", val |-> v, round |-> 0, primed |-> FALSE])
              PROVE  (~\E m \in msgs : m.type = "Answer" /\ m.cons = c /\ m.lastRound > lastRound[c])'
          \* The sent message can only be an offer.
          <5>1 msgs' = msgs \union {[type |-> "Offer", val |-> v, round |-> 0, primed |-> FALSE]}
            BY <4>2 DEF TrySend, Send
          <5>2 QED
            BY <1>1, <4>1, <5>1
        <4>3. QED
          BY <1>1, <4>1, <4>2
      <3>5. (\A m1, m2 \in msgs :
                 m1.type = "Answer" /\ m2.type = "Answer" /\ m1.cons = c /\ m2.cons = c /\ 
                 m1.lastRound = m2.lastRound 
                    => m1 = m2)'
        <4>1. ASSUME NEW Q \in Quorums,
                     NEW A \in QuorumAnswers(Q),
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
              PROVE  (\A m1, m2 \in msgs :
                          m1.type = "Answer" /\ m2.type = "Answer" /\ m1.cons = c /\ m2.cons = c /\ 
                          m1.lastRound = m2.lastRound 
                              => m1 = m2)'
          \* Regardless of which branch is evaluated, the new message can take one of three forms,
          \* enumerated by the following disjuncts.
          <5>1 \/ msgs' = msgs \union {[type |-> "Offer", val |-> PickValue(A), round |-> PickRound(A) + 1, primed |-> TRUE]}
               \/ \E v \in SuccessorValues(A) :
                     msgs' = msgs \union {[type |-> "Offer", val |-> v, round |-> PickRound(A) + 1, primed |-> FALSE]}
               \/ \E v \in SuccessorValues(A) :
                     msgs' = msgs \union {[type |-> "Offer", val |-> v, round |-> MaxLastRound(A), primed |-> FALSE]}
            BY <4>1 DEF TrySend, Send
          \* In any case, the new message can only be an offer.
          <5>2 \A m \in msgs' \ msgs : m.type = "Offer"
            BY <5>1
          <5>3 QED
            BY <1>1, <4>1, <5>2
        <4>2. ASSUME NEW v \in Values,
                     TrySend([type |-> "Offer", val |-> v, round |-> 0, primed |-> FALSE])
              PROVE  (\A m1, m2 \in msgs :
                          m1.type = "Answer" /\ m2.type = "Answer" /\ m1.cons = c /\ m2.cons = c /\ 
                          m1.lastRound = m2.lastRound 
                              => m1 = m2)'
          \* `TrySend` preserves existing messages, and the new message is an offer.
          <5>1 msgs' = msgs \union {[type |-> "Offer", val |-> v, round |-> 0, primed |-> FALSE]}
            BY <4>2 DEF TrySend, Send
          <5>2 QED
            BY <1>1, <4>1, <5>1
        <4>3. QED
          BY <1>1, <4>1, <4>2
      <3>6. QED
        BY <3>1, <3>2, <3>3, <3>4, <3>5
    <2>7. QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6 DEF Inv
  <1>2. ASSUME NEW c \in Consenters,
               NEW m \in msgs,
               /\  m.type = "Offer"
               /\  m.round > lastRound[c]
               /\  lastRound' = [lastRound EXCEPT ![c] = m.round]
               /\  lastVal' = [lastVal EXCEPT ![c] = m.val]
               /\  lastPrimed' = [lastPrimed EXCEPT ![c] = m.primed]
               /\  Send([type |-> "Answer", cons |-> c, lastVal |-> m.val, lastRound |-> m.round, lastPrimed |-> m.primed])
        PROVE  Inv'
    <2> USE DEF Answer
    <2>1. (msgs \in SUBSET Messages)'
      BY <1>2 DEF Send, Messages
    <2>2. MsgInv'
      <3> SUFFICES ASSUME NEW n \in msgs'
                   PROVE  (  /\  n.type = "Offer" =>
                                     /\  n.round = 0 => ~n.primed
                                     /\  n.round # 0 =>
                                           /\ n.primed => 
                                                 \E Q \in Quorums : \E A \in QuorumAnswers(Q) :
                                                   /\  AllIdenticalRounds(A) /\ AllIdenticalValues(A)
                                                   /\  n.val = PickValue(A)
                                                   /\  n.round = PickRound(A) + 1
                                           /\ ~n.primed =>
                                               \E Q \in Quorums : \E A \in QuorumAnswers(Q) :
                                                   /\  AllIdenticalRounds(A)
                                                   /\  n.val \in SuccessorValues(A)
                                                   /\  n.round = PickRound(A) + 1
                             /\  n.type = "Answer" =>
                                       \E o \in msgs : 
                                           /\  o.type = "Offer"
                                           /\  o.round = n.lastRound
                                           /\  o.val = n.lastVal
                                           /\  o.primed = n.lastPrimed)'
        BY DEF MsgInv
      <3> USE DEF MsgInv
      <3>1. (n.type = "Offer" =>
               /\  n.round = 0 => ~n.primed
               /\  n.round # 0 =>
                       /\ n.primed => 
                             \E Q \in Quorums : \E A \in QuorumAnswers(Q) :
                                 /\  AllIdenticalRounds(A) /\ AllIdenticalValues(A)
                                 /\  n.val = PickValue(A)
                                 /\  n.round = PickRound(A) + 1
                       /\ ~n.primed =>
                           \E Q \in Quorums : \E A \in QuorumAnswers(Q) :
                                 /\  AllIdenticalRounds(A)
                                 /\  n.val \in SuccessorValues(A)
                                 /\  n.round = PickRound(A) + 1)'
         \* Message `n' is in `msgs', therefore invariant is implicitly preserved.
         <4>1 CASE n \in msgs
           BY <1>2, <4>1 DEF Send, Messages, QuorumAnswers, Answers
         \* Sent message `n' is not an offer. 
         <4>2 CASE n \notin msgs
           BY <1>2, <4>2 DEF Send
         <4>3 QED
           BY <4>2, <4>1
      <3>2. (n.type = "Answer" =>
                   \E o \in msgs : 
                         /\  o.type = "Offer"
                         /\  o.round = n.lastRound
                         /\  o.val = n.lastVal
                         /\  o.primed = n.lastPrimed)'
        BY <1>2 DEF Send
      <3>3. QED
        BY <3>1, <3>2
    <2>3. (lastVal \in [Consenters -> Values \union {None}])'
      BY <1>2 DEF Send, Messages
    <2>4. (lastRound \in [Consenters -> Rounds \union {-1}])'
      BY <1>2 DEF Send, Messages
    <2>5. (lastPrimed \in [Consenters -> BOOLEAN])'
      BY <1>2 DEF Send, Messages
    <2>6. ConsInv'
      <3> SUFFICES ASSUME NEW d \in Consenters'
                   PROVE  (/\  lastRound[d] = -1 <=> lastVal[d] = None
                           /\  lastRound[d] = -1 => ~lastPrimed[d]
                           /\  lastRound[d] # -1 => \E a \in msgs : 
                                   /\  a.type = "Answer" 
                                   /\  a.cons = d 
                                   /\  a.lastRound = lastRound[d]
                                   /\  a.lastVal = lastVal[d]
                                   /\  a.lastPrimed = lastPrimed[d]
                           /\  ~\E a \in msgs : 
                                   a.type = "Answer" /\ a.cons = d /\ a.lastRound > lastRound[d]
                           /\  \A m1, m2 \in msgs :
                                   m1.type = "Answer" /\ m2.type = "Answer" /\ m1.cons = d /\ m2.cons = d /\ 
                                   m1.lastRound = m2.lastRound 
                                      => m1 = m2)'
        BY DEF ConsInv
      <3> USE DEF ConsInv
      \* The equivalence between `lastRound[d] = -1' and `lastVal[d] = None'.
      <3>1. (lastRound[d] = -1 <=> lastVal[d] = None)'
        \* No assignment to `lastRound[d]' and `lastVal[d]' in `Answer(c)', therefore implicitly true.
        <4>1 CASE d # c
          BY <1>2, <4>1
        \* Assignment: `lastRound[d]' must have been assigned a round that is 
        \* greater than `-1' by the `Messages' type-correctness invariant and 
        \* `lastVal[d]' is assigned a value that is not `None'
        \* by lemma `NoneNotAValue'. `-1' and `None' cannot be used for assignent at a
        \* later point because no valid offer `o' permits `o.val = None' or 
        \* `o.round = -1' by the definition of `Messages'.
        <4>2 CASE d = c
          <5>1 lastRound[d]' = m.round /\ lastRound[d]' # -1
            BY <1>2, <4>2 DEF Rounds
          <5>2 lastVal[d]' = m.val /\ lastVal[d]' # None
            BY <1>2, <4>2, NoneNotAValue DEF Messages
          <5>3 QED
            BY <5>1, <5>2
        <4>3 QED
          BY <4>1, <4>2
      \* `lastPrimed[d]' is `FALSE' when `lastRound[d]' is not set, which is shown
      \* by monotonic assignment: all rounds assigned to `lastRound[d]' are greater
      \* than the previous, therefore `lastRound[d]' cannot be `-1' after it transitions past
      \* its initial state, and the falseness of `lastPrimed[d]' in that state
      \* is guaranteed by `ConsInv'.
      <3>2. (lastRound[d] = -1 => ~lastPrimed[d])'
        \* No assignment to `lastRound[d]' and `lastVal[d]', therefore implicitly true.
        <4>1 CASE d # c
          BY <1>2, <4>1
        \* Assignment: true by monotonicity of `lastPrimed[d]'.
        <4>2 CASE d = c
          BY <1>2, <4>2 DEF Rounds
        <4>3 QED
          BY <4>1, <4>2
      \* For any answer, there must be a corresponding offer in the same round,
      \* bearing the same value and primed status.
      <3>3. (lastRound[d] # -1 => \E a \in msgs : 
                 /\  a.type = "Answer" 
                 /\  a.cons = d 
                 /\  a.lastRound = lastRound[d]
                 /\  a.lastVal = lastVal[d]
                 /\  a.lastPrimed = lastPrimed[d])'
        \* Where the consenter `d' differs from the one considered in `Answer(c)',
        \* the invariant is preserved since the history variable `msgs' is unchanged,
        \* as are `lastRound[d]', `lastVal[d]' and `lastPrimed[d]'.
        <4>1 CASE d # c
          BY <1>2, <4>1 DEF Send
        \* Where the consenter `d' is the one considered in `Answer(c)', then the
        \* proof is a simple consequence of the next-state relation `Answer'.
        <4>2 CASE d = c
          <5>1 lastRound[d]' = m.round /\ lastRound[d]' # -1
            BY <1>2, <4>2 DEF Rounds
          <5>2 lastVal[d]' = m.val /\ lastPrimed[d]' = m.primed
            BY <1>2, <4>2
          <5>3 \E mmm \in msgs' : 
                  mmm = [type |-> "Answer", cons |-> c, lastVal |-> m.val, 
                         lastRound |-> m.round, lastPrimed |-> m.primed]
            BY <1>2 DEF Send
          <5>4 QED
            BY <1>2, <5>3 DEF Send
        <4>3 QED
          BY <4>1, <4>2
      \* A consenter `d' cannot have sent an answer in a round that exceeds `lastRound[d]',
      \* which is ensured by monotonic assignment to `lastRound[d]'.
      <3>4. (~\E n \in msgs : n.type = "Answer" /\ n.cons = d /\ n.lastRound > lastRound[d])'
        BY <1>2 DEF Send, Messages, Rounds
      \* A consenter `d' must not have voted twice, which is ensured by exclusive 
      \* assignment to `lastRound[d]'. I.e. for any round `r', only one `Answer' 
      \* transition permits the assignment of `r' to `lastRound[d]'.
      <3>5. (\A m1, m2 \in msgs :
                 m1.type = "Answer" /\ m2.type = "Answer" /\ m1.cons = d /\ m2.cons = d /\ 
                 m1.lastRound = m2.lastRound 
                    => m1 = m2)'
        BY <1>2 DEF Send, Messages
      <3>6. QED
        BY <3>1, <3>2, <3>3, <3>4, <3>5
    <2>7. QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6 DEF Inv
  \* `Decided' and `Terminated' are marker pseudo-actions that do not assign to 
  \* any variables in `vars' and are only useful for bounded model checking. The
  \* efficacy of the specification clearly does not depend on their presence.
  <1>3. CASE Decided \/ Terminated
    BY <1>3, InvariantPreservedOnUnchanged DEF Decided, Terminated
  <1>4. QED
    BY <1>1, <1>2, <1>3 DEF Answer, Next

(*****************************************************************************)
(* Proves the main correctness theorem; specifically, that if a value `v' is *)
(* chosen within a run of the algorithm, no other value distinct from `v'    *)
(* may subsequently be chosen within that run. This does not imply           *)
(* that a value is only chosen once; rather, that repeat selections (if      *)
(* they do occur) converge on the same value.                                *)
(*                                                                           *)
(* The proof combines lemmas `Initial', `Inductive' and                      *)
(* `Consistent'.                                                             *)
(*****************************************************************************)
THEOREM Correctness == Spec => []Consistency  
  <1> USE DEF Spec, Consistency
  <1>1. Init => Inv
    BY Initial
  <1>2. Inv /\ [Next]_vars => Inv'
    <2>1. CASE Next
      BY Inductive, <2>1
    <2>2. CASE UNCHANGED vars
      BY <2>2, InvariantPreservedOnUnchanged
    <2>3. QED
      BY <2>1, <2>2
  <1>3. Inv => Consistency
    BY Consistent DEF Inv
  <1>4. QED
    BY <1>1, <1>2, <1>3, PTL
====