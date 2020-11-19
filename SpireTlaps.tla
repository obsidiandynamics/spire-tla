---- MODULE SpireTlaps ----
EXTENDS Spire, TLAPS, NaturalsInduction, FiniteSetTheorems

LEMMA QuorumNonEmpty == \A Q \in Quorums : Q # {}
  BY QuorumAssumption
  
LEMMA NoneNotAValue == None \notin Values
  BY NoSetContainsEverything DEF None
  
LEMMA QuorumAnswerHasConsenter ==
    \A Q \in Quorums : \A A \in QuorumAnswers(Q) : A # {} => \E a \in A : a.cons \in Q
  BY DEF QuorumAnswers, Answers
  
LEMMA AnswersNonEmpty ==
    \A Q \in Quorums : \A A \in QuorumAnswers(Q) : Q # {} <=> A # {}
  BY DEF QuorumAnswers, Answers
  
LEMMA PickRoundImage ==
    \A M \in SUBSET Messages : M # {} => PickRound(M) \in {m.lastRound : m \in M}
  BY DEF PickRound, Messages
  
LEMMA PickValueImage ==
    \A M \in SUBSET Messages : M # {} => PickValue(M) \in {m.lastVal : m \in M}
  BY DEF PickValue, Messages
  

HasMax(S) ==
    S \in SUBSET Nat /\ S # {} => \E n1 \in S : \A n2 \in S : n1 >= n2
 
LEMMA AdditionHasMax ==
    \A S \in SUBSET Nat, x \in Nat : x \notin S /\ HasMax(S)
        => HasMax(S \union {x})
  BY DEF Nat, HasMax
\*  
\*   
\*LEMMA AdditionHasMax2 ==
\*    ASSUME NEW S, NEW x, x \notin S, HasMax(S)
\*    PROVE HasMax(S \union {x}) \*/\ IsFiniteSet(S \union {x})
\*  BY DEF HasMax
\*
\*LEMMA Test ==
\*  ASSUME NEW T \in SUBSET Nat, NEW x \in Nat, HasMax(T), x \notin T \*, IsFiniteSet(T)
\*       PROVE  HasMax(T \cup {x})
\*    BY AdditionHasMax2

\*LEMMA AllHaveMax ==
\*  ASSUME NEW S \in SUBSET Nat,
\*         S # {},
\*         IsFiniteSet(S),
\*         HasMax({})
\*  PROVE  HasMax(S)
\*\*  <1> DEFINE Q(T) == T == HasMax(T)
\*  <1> DEFINE Q(T) == T \in SUBSET Nat /\ T # {} => \E n1 \in S : \A n2 \in S : n1 >= n2
\*  <1> SUFFICES Q(S)
\*    OBVIOUS
\*  <1>1 Q({})
\*    BY DEF HasMax
\*  <1>10 IsFiniteSet({})
\*  <1>2 \A x : (x \notin S /\ Q(S)) => Q(S \union {x}) \*/\ IsFiniteSet(S \union {x})
\*    BY AdditionHasMax DEF HasMax
\*  <1>3 ASSUME NEW R, NEW x, Q(R), x \notin R \*, IsFiniteSet(T)
\*       PROVE  Q(R \cup {x})
\*    BY AdditionHasMax2 DEF HasMax
\*  <1> HIDE DEF Q
\*  <1> QED
\*    BY <1>1, <1>3, FS_Induction, IsaM("blast") DEF HasMax

LEMMA AllHaveMax ==
  ASSUME NEW S \in SUBSET Nat,
         S # {},
         IsFiniteSet(S),
         HasMax({})
  PROVE  HasMax(S)
  <1> DEFINE Q(T) == T \in SUBSET Nat /\ T # {} => \E n1 \in T : \A n2 \in T : n1 >= n2
  <1> SUFFICES Q(S)
    BY DEF HasMax
  <1>1 Q({})
    OBVIOUS
  <1>3 ASSUME NEW R, NEW x, Q(R), x \notin R
       PROVE  Q(R \cup {x})
    <2> SUFFICES ASSUME (R \cup {x}) \in SUBSET Nat /\ (R \cup {x}) # {}
                 PROVE  \E n1 \in R \cup {x} : \A n2 \in R \cup {x} : n1 >= n2
      BY DEF Q
    <2>1 CASE R \in SUBSET Nat
      <3>1 \A G \in SUBSET Nat, y \in Nat : y \notin G /\ HasMax(G)
              => HasMax(G \union {y})
        BY AdditionHasMax
      <3>99 QED
        BY <1>3, <2>1, <3>1 DEF HasMax, Nat
    <2>2 CASE R \notin SUBSET Nat
      BY <2>2
    <2>99 QED
      BY <2>1, <2>2
  <1> HIDE DEF Q
  <1> QED
    BY <1>1, <1>3, FS_Induction, IsaM("blast") DEF HasMax    
    
    
\*SetMax(S) == CHOOSE t \in S : \A s \in S : t >= s    
\*
\*LEMMA MaxIntegers ==
\*  ASSUME NEW S \in SUBSET Int, S # {}, IsFiniteSet(S)
\* PROVE  /\ setMax(S) \in S
\*        /\ \A yy \in S : yy <= setMax(S)
\*<1>. DEFINE P(T) == T \in SUBSET Int /\ T # {} => \E xx \in T : \A yy \in T : yy <= xx
\*<1>1. P({})
\* OBVIOUS
\*<1>2. ASSUME NEW T, NEW xx, P(T), xx \notin T
\*     PROVE  P(T \cup {xx})
\* <2>. HAVE T \cup {xx} \in SUBSET Int
\* <2>1. CASE \A yy \in T : yy <= xx
\*   BY <2>1, Isa
\* <2>2. CASE \E yy \in T : ~(yy <= xx)
\*   <3>. T # {}
\*     BY <2>2
\*   <3>1. PICK yy \in T : \A zz \in T : zz <= yy
\*     BY <1>2
\*   <3>2. xx <= yy
\*     BY <2>2, <3>1
\*   <3>3. QED  BY <3>1, <3>2
\* <2>. QED  BY <2>1, <2>2
\*<1>. HIDE DEF P
\*<1>3. P(S)  BY <1>1, <1>2, FS_Induction, IsaM("blast")
\*<1>. QED  BY <1>3, Zenon DEF setMax, P  
    
    
  
\*LEMMA SetMaxImage ==
\*    \A S \in Nat : S # {} => SetMax(S) \in Nat
\*  <1> SUFFICES ASSUME NEW S \in Nat,
\*                      S # {}
\*               PROVE  SetMax(S) \in Nat
\*    OBVIOUS
\*  <1> QED
\*    BY AllHaveMax DEF SetMax
\*    
  
LEMMA MaxLastRoundImage ==
    \A M \in SUBSET Messages : M # {} => MaxLastRound(M) \in {m.lastRound : m \in M}
  <1> SUFFICES ASSUME NEW M \in SUBSET Messages,
                      M # {}
               PROVE  MaxLastRound(M) \in {m.lastRound : m \in M}
    OBVIOUS
  <1> USE DEF MaxLastRound
\*  <1>1 \A m \in M : m.lastRound \in Rounds
\*    BY DEF Messages, Rounds
\*  <1>2 \E m \in M : m.lastRound \in Rounds
\*    BY <1>1
\*  <1>3 \A m1, m2 \in M : m1.lastRound > m2.lastRound \/ m1.lastRound < m2.lastRound \/ m1.lastRound = m2.lastRound
\*    BY <1>1 DEF Rounds
\*  <1>9 \E m1 \in M : \A m2 \in M : m2.lastRound < m1.lastRound \/ m2.lastRound = m1.lastRound
\*    BY <1>1, <1>2, <1>3 DEF Messages, Rounds
\*  <1>10 \E m1 \in M : \A m2 \in M : m2.lastRound <= m1.lastRound
\*    BY <1>1, <1>2, <1>3, AllHaveMax DEF Messages, Rounds
\*\*  <1>11 PICK m1 \in M : \A m2 \in M : m2.lastRound <= m1.lastRound
\*\*    BY <1>10
\*\*  <1>20 QED
\*\*    BY AllHaveMax DEF MaxLastRound, Rounds
\*  <1>19 DEFINE S == {m.lastRound : m \in M}
\*\*  <1>20 MaxLastRound(M) = SetMax(S)
\*\*    BY DEF MaxLastRound
  <1>21 MaxLastRound(M) \in {m.lastRound : m \in M}
    BY AllHaveMax DEF MaxLastRound, SetMax
  <1>99 QED
    BY <1>21
  
  
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
  <1>5 \A a \in highestRoundAnswers : a \in M
    OBVIOUS
  <1>80 CASE highestRoundPrimedAnswers # {}
    <2>99 QED
      BY <1>80, PickValueImage DEF PickValue
  <1>90 CASE highestRoundPrimedAnswers = {} 
    <2>99 QED
      BY <1>90
  <1>99 QED
    BY <1>80, <1>90

\* A uniform set of answers leads to a single successor value.
LEMMA UniformAnswerSuccessorSingularity ==
    \A M \in SUBSET Messages : M # {} /\ AllIdenticalRounds(M) /\ AllIdenticalValues(M) 
        => SuccessorValues(M) = {PickValue(M)}
    BY DEF SuccessorValues, AllIdenticalRounds, AllIdenticalValues, MaxLastRound, SetMax, PickValue

LEMMA PrimedOfferFollowsDominantAnswer ==
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
  <1>1 o.round # 0
    BY DEF MsgInv
  <1>11 o.round \in Rounds
    BY DEF MsgInv, Messages, TypeOK
  <1>2 \E Q \in Quorums : \E A \in QuorumAnswers(Q) :
          /\  A # {}
          /\  AllIdenticalRounds(A) /\ AllIdenticalValues(A)
          /\  o.val = PickValue(A)
          /\  o.round = PickRound(A) + 1
    BY AnswersNonEmpty, QuorumAssumption DEF MsgInv
  <1>3 \E Q \in Quorums : \E A \in QuorumAnswers(Q) :
          /\  A # {}
          /\  AllIdenticalRounds(A) /\ AllIdenticalValues(A)
          /\  o.val = PickValue(A)
          /\  o.round - 1 = PickRound(A)
    BY <1>2, PickRoundImage DEF Messages, TypeOK, QuorumAnswers, Answers, Rounds
  <1>40 PICK R \in Quorums : \E A \in QuorumAnswers(R) :
          /\  A # {}
          /\  AllIdenticalRounds(A) /\ AllIdenticalValues(A)
          /\  o.val = PickValue(A)
          /\  o.round - 1 = PickRound(A)
    BY <1>3
  <1>400 PICK B \in QuorumAnswers(R) :
          /\  B # {}
          /\  AllIdenticalRounds(B) /\ AllIdenticalValues(B)
          /\  o.val = PickValue(B)
          /\  o.round - 1 = PickRound(B)
    BY <1>3, <1>40
  <1>401  /\  B # {}
          /\  AllIdenticalRounds(B)
          /\  o.round - 1 = PickRound(B)
          /\  PickRound(B) \in {a.lastRound : a \in B}
          /\  (o.round - 1) \in {a.lastRound : a \in B}
          /\  \A a \in B : a.lastRound = o.round - 1
    BY <1>11, <1>400, PickRoundImage DEF Rounds, AllIdenticalRounds, PickRound, Messages, TypeOK, QuorumAnswers, Answers
  <1>402  /\  B # {}
          /\  AllIdenticalValues(B)
          /\  o.val = PickValue(B)
          /\  o.val \in {a.lastVal : a \in B}
          /\  \A a \in B : a.lastVal = o.val
    BY <1>11, <1>400, PickValueImage DEF AllIdenticalValues, PickRound, Messages, TypeOK, QuorumAnswers, Answers
  <1>8 \E Q \in Quorums : \E A \in QuorumAnswers(Q): 
          /\ \A a \in A : a.lastRound = o.round - 1 
          /\ \A a \in A : a.lastVal = o.val
    BY <1>401, <1>402
  <1>99 QED
    BY <1>8
  
    
LEMMA QuorumAnswerHasConsenters ==
    \A Q \in Quorums : \A A \in QuorumAnswers(Q) : \A c \in Q : \E a \in A : a.cons = c
  BY DEF QuorumAnswers, Answers
  
\* All primed answers in a given round must refer to the same value.
LEMMA IdentityOfPrimedRoundAnswers ==
    TypeOK /\ MsgInv /\ ConsInv => 
        \A m1, m2 \in msgs : 
            m1.type = "Answer" /\ m1.lastPrimed /\ m2.type = "Answer" /\ m2.lastPrimed /\ m1.lastRound = m2.lastRound =>
                m1.lastVal = m2.lastVal
  <1> SUFFICES ASSUME TypeOK /\ MsgInv /\ ConsInv,
                      NEW m1 \in msgs,    NEW m2 \in msgs,
                      m1.type = "Answer", m2.type = "Answer",
                      m1.lastPrimed,      m2.lastPrimed,
                      m1.lastRound = m2.lastRound
               PROVE  m1.lastVal = m2.lastVal
    OBVIOUS
  <1>21 \E o \in msgs : o.type = "Offer" /\ o.round = m1.lastRound /\ o.primed /\ o.val = m1.lastVal
    BY DEF MsgInv
  <1>22 \E o \in msgs : o.type = "Offer" /\ o.round = m2.lastRound /\ o.primed /\ o.val = m2.lastVal
    BY DEF MsgInv
  <1>400 PICK o1 \in msgs : o1.type = "Offer" /\ o1.round = m1.lastRound /\ o1.primed /\ o1.val = m1.lastVal
    BY <1>21
  <1>402 PICK o2 \in msgs : o2.type = "Offer" /\ o2.round = m2.lastRound /\ o2.primed /\ o2.val = m2.lastVal
    BY <1>22
  <1>310 \E R \in Quorums : \E B \in QuorumAnswers(R) :
            \A a \in B : a.lastRound = o1.round - 1 /\ a.lastVal = o1.val
    BY <1>400, <1>21, PrimedOfferFollowsDominantAnswer
  <1>312 \E R \in Quorums : \E B \in QuorumAnswers(R) :
            \A a \in B : a.lastRound = o2.round - 1 /\ a.lastVal = o2.val
    BY <1>402, <1>22, PrimedOfferFollowsDominantAnswer
  <1>31 \E R \in Quorums : \E B \in QuorumAnswers(R) :
            \A a \in B : a.lastRound = m1.lastRound - 1 /\ a.lastVal = m1.lastVal /\ a.type = "Answer" \*/\ a.cons \in R
    BY <1>21, <1>310, <1>400 (*QuorumAnswerHasConsenters*) DEF QuorumAnswers, Answers\*, Messages, TypeOK
  <1>311 PICK R1 \in Quorums : \E B \in QuorumAnswers(R1) :
            \A a \in B : a.lastRound = m1.lastRound - 1 /\ a.lastVal = m1.lastVal /\ a.cons \in R1
    BY <1>31, QuorumAnswerHasConsenters DEF QuorumAnswers, Answers
  <1>32 \E R \in Quorums : \E B \in QuorumAnswers(R) :
            \A a \in B : a.lastRound = m1.lastRound - 1 /\ a.lastVal = m2.lastVal /\ a.type = "Answer" \*/\ a.cons \in R
    BY <1>22, <1>312, <1>402 (*QuorumAnswerHasConsenters*) DEF QuorumAnswers, Answers \*, Messages, TypeOK
  <1>321 PICK R2 \in Quorums : \E B \in QuorumAnswers(R2) :
            \A a \in B : a.lastRound = m1.lastRound - 1 /\ a.lastVal = m2.lastVal /\ a.cons \in R2
    BY <1>32, QuorumAnswerHasConsenters DEF QuorumAnswers, Answers
  <1>33 PICK c \in Consenters : c \in R1 /\ c \in R2
    BY <1>311, <1>321, QuorumAssumption
  <1>40 R1 # {} /\ R2 # {}
    BY QuorumAssumption
  <1>41 \E B \in QuorumAnswers(R1) : 
      \E a \in B : a.lastRound = m1.lastRound - 1 /\ a.lastVal = m1.lastVal /\ a.cons = c
    BY <1>40, <1>311, <1>33, QuorumAnswerHasConsenters
  <1>42 \E B \in QuorumAnswers(R2) : 
      \E a \in B : a.lastRound = m1.lastRound - 1 /\ a.lastVal = m2.lastVal /\ a.cons = c
    BY <1>40, <1>321, <1>33, QuorumAnswerHasConsenters
  <1>99 QED
    BY <1>41, <1>42 DEF QuorumAnswers, Answers, ConsInv
  
\* If all answers for a given round are primed, then they must refer to the same value.
LEMMA SingularPrimedRoundQuorumAnswer ==
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
    BY <1>1, IdentityOfPrimedRoundAnswers

ChosenIn(r, v) ==  
    \E Q \in Quorums :
        \E A \in QuorumAnswers(Q) :
            /\  AllIdenticalRounds(A) 
            /\  AllPrimed(A)
            /\  \E m \in A : m.lastVal = v /\ m.lastRound = r
            
NotOfferedIn(r, V) ==
    ~\E m \in msgs : m.type = "Offer" /\ m.round = r /\ m.val \in V

OfferedIn(r, v) ==
    \E o \in msgs : o.type = "Offer" /\ o.round = r /\ o.val = v
    
AnsweredIn(r, v) ==
    \E o \in msgs : o.type = "Answer" /\ o.lastRound = r /\ o.lastVal = v
    
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

LEMMA OfferFromPreviousRoundAnswer ==
    TypeOK /\ MsgInv =>
        \A r \in Rounds, v \in Values : r # 0 /\ OfferedIn(r, v) => AnsweredIn(r - 1, v)
  <1> SUFFICES ASSUME MsgInv, TypeOK,
                      NEW r \in Rounds, NEW v \in Values,
                      r # 0,
                      NEW o \in msgs,
                      o.type = "Offer" /\ o.round = r /\ o.val = v
               PROVE  AnsweredIn(r - 1, v)
    BY DEF OfferedIn
\*  <1>3 \A mmm \in A : mmm.type = "Answer" /\ mmm.lastRound = r /\ mmm.lastPrimed
\*    BY DEF QuorumAnswers, Answers, AllIdenticalRounds, AllPrimed
\*  <1>4 \A mmm \in A : mmm.lastVal = v
\*    BY SingularPrimedRoundQuorumAnswer DEF TypeOK, MsgInv, ConsInv
  <1>5 \A n \in msgs : n.type = "Offer" /\ n.round = r /\ n.val = v =>
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
    <2>3.CASE n.primed
      <3>1 PICK R \in Quorums : \E B \in QuorumAnswers(R) :
              /\  AllIdenticalRounds(B) /\ AllIdenticalValues(B)
              /\  n.val = PickValue(B)
              /\  n.round = PickRound(B) + 1
        BY <2>3
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
        BY <3>2, <3>4, <3>6, PickRoundImage DEF PickRound, Rounds, QuorumAnswers, Answers
      <3>8 n.round - 1 \in {mmm.lastRound : mmm \in B}
        BY <3>5, <3>2, <3>7 DEF Rounds, Messages, TypeOK
      <3>9 \A b \in B : b.lastRound = r - 1
        BY <3>2, <3>3, <3>5, <3>8 DEF Rounds, Messages, TypeOK
      <3>10 \E b \in B : b.lastVal = n.val
        BY <3>2, <3>4, PickValueImage DEF PickValue
      <3>11 QED
        BY <3>9, <3>10 DEF QuorumAnswers, Answers
    <2>4 CASE ~n.primed
      <3>1 PICK R \in Quorums : \E B \in QuorumAnswers(R) :
              /\  AllIdenticalRounds(B)
              /\  n.val \in SuccessorValues(B)
              /\  n.round = PickRound(B) + 1
        BY <2>4
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
        BY <3>2, <3>4, <3>6, PickRoundImage DEF PickRound, Rounds, QuorumAnswers, Answers
      <3>8 n.round - 1 \in {mmm.lastRound : mmm \in B}
        BY <3>5, <3>2, <3>7 DEF Rounds, Messages, TypeOK
      <3>9 \A b \in B : b.lastRound = r - 1
        BY <3>2, <3>3, <3>5, <3>8 DEF Rounds, Messages, TypeOK
      <3>9b \A b \in B : b \in Messages
        BY <3>2 DEF TypeOK, QuorumAnswers, Answers
      <3>10 n.val \in {b.lastVal : b \in B}
         BY <3>2, <3>4, <3>9b, SuccessorValuesImage DEF SuccessorValues
      <3>11 QED
        BY <3>9, <3>10 DEF QuorumAnswers, Answers
    <2>99 QED
      BY <2>3, <2>4
  <1>99 QED
    BY <1>5 DEF AnsweredIn

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
  <1>3b \A a \in msgs : a.type = "Answer" /\ a.lastRound = r => a.lastVal \notin V
    BY <1>3
  <1>4 \A o \in msgs : o.type = "Offer" /\ o.round = r + 1 => 
            \E a \in msgs : a.type = "Answer" /\ a.lastRound = r /\ a.lastVal = o.val
    BY OfferFromPreviousRoundAnswer DEF OfferedIn, AnsweredIn, Messages, TypeOK
  <1>4b \A o \in msgs : o.type = "Offer" /\ o.round = r + 1 => 
            \E a \in msgs : a.type = "Answer" /\ a.lastRound = r /\ a.lastVal = o.val /\ a.lastVal \notin V
    BY <1>4, <1>3b
  <1>8 \A o \in msgs : o.type = "Offer" /\ o.round = r + 1 => o.val \notin V
    BY <1>3, <1>4b DEF MsgInv, Rounds, Messages, TypeOK
  <1>99 QED
    BY <1>8  
  
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

LEMMA RoundAnswersOverlap ==
    ConsInv =>
        \A Q, R \in Quorums : \A A \in QuorumAnswers(Q), B \in QuorumAnswers(R) : 
            (\A a \in A, b \in B : a.lastRound = b.lastRound) => 
                \E a \in A, b \in B : a = b
  BY QuorumAssumption DEF ConsInv, QuorumAnswers, Answers

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
  <1>3 \A mmm \in A : mmm.type = "Answer" /\ mmm.lastRound = r /\ mmm.lastPrimed
    BY DEF QuorumAnswers, Answers, AllIdenticalRounds, AllPrimed
  <1>4 \A mmm \in A : mmm.lastVal = v1
    BY SingularPrimedRoundQuorumAnswer DEF TypeOK, MsgInv, ConsInv
  <1>5 \A n \in msgs : n.type = "Offer" /\ n.round = r + 1 =>
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
    <2>3.CASE n.primed
      <3>1 PICK R \in Quorums : \E B \in QuorumAnswers(R) :
              /\  AllIdenticalRounds(B) /\ AllIdenticalValues(B)
              /\  n.val = PickValue(B)
              /\  n.round = PickRound(B) + 1
        BY <2>3
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
        BY <3>2, <3>4, <3>6, PickRoundImage DEF PickRound, Rounds, QuorumAnswers, Answers
      <3>8 n.round - 1 \in {mmm.lastRound : mmm \in B}
        BY <2>3, <3>5, <3>2, <3>7 DEF Rounds, Messages, TypeOK
      <3>9 \A b \in B : b.lastRound = r
        BY <2>3, <3>2, <3>3, <3>5, <3>8 DEF Rounds, Messages, TypeOK
      <3>10 \A a \in A, b \in B : a.lastRound = b.lastRound
        BY <1>3, <3>9
      <3>11 \E a \in A, b \in B : a = b
        BY <3>9, <3>10, RoundAnswersOverlap
      <3>12 \A b \in B : b.lastVal = v1
        BY <1>4, <3>11, <3>2 DEF AllIdenticalValues
      <3>13 QED
        BY <3>12, <3>2, <3>4, PickValueImage DEF PickValue
    <2>4 CASE ~n.primed
      <3>1 PICK R \in Quorums : \E B \in QuorumAnswers(R) :
              /\  AllIdenticalRounds(B)
              /\  n.val \in SuccessorValues(B)
              /\  n.round = PickRound(B) + 1
        BY <2>4
      <3>2 PICK B \in QuorumAnswers(R) :
              /\  AllIdenticalRounds(B)
              /\  n.val \in SuccessorValues(B)
              /\  n.round = PickRound(B) + 1
        BY <3>1
      <3>3 B # {}
        BY <3>2, QuorumAssumption DEF QuorumAnswers, Answers
      <3>4 \A b \in B : b.type = "Answer" /\ b.lastRound \in Rounds
        BY <3>2 DEF QuorumAnswers, Answers, TypeOK, Messages
      <3>8 CASE AllIdenticalRounds(B)
        \* TODO Cleanup: there is only one case
        <4>1 \A m1, m2 \in B : m1.lastRound = m2.lastRound
          BY <3>8 DEF AllIdenticalRounds
        <4>5 PickRound(B) \in {mmm.lastRound : mmm \in B}
          BY <3>2, <3>3, PickRoundImage DEF PickRound
        <4>7 PickRound(B) \in Rounds
          BY <3>2, <3>3, <3>4, PickRoundImage DEF PickRound, Rounds, QuorumAnswers, Answers
        <4>8 n.round - 1 \in {mmm.lastRound : mmm \in B}
          BY <2>4, <4>5, <3>2, <3>4, <3>8 DEF Rounds, Messages, TypeOK
        <4>9 \A b \in B : b.lastRound = r
          BY <2>4, <3>2, <3>3, <4>1, <4>8 DEF Rounds, Messages, TypeOK
        <4>10 \A a \in A, b \in B : a.lastRound = b.lastRound
          BY <1>3, <4>9
        <4>11 \E a \in A, b \in B : a = b
          BY <4>9, <4>10, RoundAnswersOverlap
        <4>12 \E b \in B : b.lastVal = v1 /\ b.lastPrimed
          BY <1>4, <4>11 DEF AllPrimed
        <4>12b PICK p \in B : p.lastVal = v1 /\ p.lastPrimed
          BY <4>12
        <4>13 MaxLastRound(B) = r
          BY <3>3, <4>9 DEF MaxLastRound, SetMax, Rounds
        <4>14 DEFINE highestRoundAnswers == {b \in B : b.lastRound = MaxLastRound(B)}
        <4>15 highestRoundAnswers = B
          BY <4>13, <4>9
        <4>16a \A b \in B : b \in msgs
          BY <3>2, <3>1 DEF QuorumAnswers, Answers, Messages, TypeOK
        <4>16 \A b \in B : b.lastPrimed /\ b.lastRound = r => b.lastVal = v1
          BY <3>2, <3>4, <4>9, <4>12b, <4>16a, IdentityOfPrimedRoundAnswers
        <4>17 DEFINE highestRoundPrimedAnswers == {b \in highestRoundAnswers : b.lastPrimed}
        <4>17b highestRoundPrimedAnswers = {b \in B : b.lastPrimed}
          BY <4>15
        <4>18 highestRoundPrimedAnswers # {}
          BY <4>12, <4>16, <4>17b
        <4>19 \A mmm \in highestRoundPrimedAnswers : mmm.lastVal = v1
          BY <4>16, <4>9
        <4>20 \A v \in SuccessorValues(B) : v = v1
          BY <4>18, <4>19 DEF SuccessorValues, PickValue
        <4>99 QED
          BY <3>2, <4>20
\*      <3>9 CASE ~AllIdenticalRounds(B)
\*        <4>1 MaxLastRound(B) = r + 1
\*          BY <3>2, <3>9
\*        <4>99 QED
      <3>99 QED
        BY <3>2, <3>8
    <2>5. QED
      BY <2>3, <2>4
  <1>99 QED 
    BY <1>5
        
        
LEMMA Stable ==
    TypeOK /\ MsgInv /\ ConsInv =>
        \A r1, r2 \in Rounds, v1, v2 \in Values : r1 < r2 /\ ChosenIn(r1, v1) /\ OfferedIn(r2, v2) => v1 = v2
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

  
LEMMA Initial == Init => Inv
  BY DEF Init, Inv, MsgInv, ConsInv
  
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
    BY SingularPrimedRoundQuorumAnswer DEF TypeOK
  <1>10 CASE m.lastRound = n.lastRound  \*TODO cleanup
    <2>4 \E ma \in A, mb \in B : ma.lastVal = mb.lastVal
      BY <1>10, QuorumAssumption DEF QuorumAnswers, Answers, Messages, ConsInv, AllIdenticalRounds
    <2>5 QED
      BY <1>10, <1>2, <2>4
  <1>20 CASE m.lastRound < n.lastRound
    <2>99 QED
      BY <1>1, <1>20, Stable, ChosenFromOffer DEF ChosenIn, OfferedIn, Rounds, MsgInv, TypeOK
  <1>30 CASE m.lastRound > n.lastRound
    <2>99 QED
      BY <1>1, <1>30, Stable, ChosenFromOffer DEF ChosenIn, OfferedIn, Rounds, MsgInv, TypeOK
  <1>9 QED
    BY <1>1, <1>10, <1>20, <1>30 DEF Rounds

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
            <6>1 PICK v \in SuccessorValues(A) : TrySend([type |-> "Offer", val |-> v, round |-> PickRound(A) + 1, primed |-> FALSE])
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
          <5>4 PICK v \in SuccessorValues(A) : TrySend([type |-> "Offer", val |-> v, round |-> MaxLastRound(A), primed |-> FALSE])
             BY <3>1, <4>4, <4>5
          <5>5 DEFINE n == [type |-> "Offer", val |-> v, round |-> MaxLastRound(A), primed |-> FALSE]
          <5>6 n \in Messages
            BY <4>3, <5>4, <5>3 DEF Messages, Rounds
          <5>7 QED
            BY <1>1, <3>1, <4>5, <5>6, <5>4 DEF TrySend, Send
        <4>6 QED
          BY <1>1, <3>1, <4>4, <4>5
      <3>2. ASSUME NEW v \in Values,
                   TrySend([type |-> "Offer", val |-> v, round |-> 0, primed |-> FALSE])
            PROVE  (msgs \in SUBSET Messages)'
        <4>1 DEFINE n == [type |-> "Offer", val |-> v, round |-> 0, primed |-> FALSE]
        <4>2 n \in Messages
          BY DEF Messages, Rounds
        <4>4 QED
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
                                                     \E Q_1 \in Quorums : \E A_1 \in QuorumAnswers(Q_1) :
                                                         /\  AllIdenticalRounds(A_1) /\ AllIdenticalValues(A_1)
                                                         /\  m.val = PickValue(A_1)
                                                         /\  m.round = PickRound(A_1) + 1
                                                 /\ ~m.primed =>
                                                     \E Q_1 \in Quorums : \E A_1 \in QuorumAnswers(Q_1) :
                                                         /\  AllIdenticalRounds(A_1)
                                                         /\  m.val \in SuccessorValues(A_1)
                                                         /\  m.round = PickRound(A_1) + 1
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
                                   \E Q_1 \in Quorums : \E A_1 \in QuorumAnswers(Q_1) :
                                       /\  AllIdenticalRounds(A_1) /\ AllIdenticalValues(A_1)
                                       /\  m.val = PickValue(A_1)
                                       /\  m.round = PickRound(A_1) + 1
                               /\ ~m.primed =>
                                   \E Q_1 \in Quorums : \E A_1 \in QuorumAnswers(Q_1) :
                                       /\  AllIdenticalRounds(A_1)
                                       /\  m.val \in SuccessorValues(A_1)
                                       /\  m.round = PickRound(A_1) + 1)'
              <7> SUFFICES ASSUME (m.type = "Offer")'
                           PROVE  (/\  m.round = 0 => ~m.primed
                                   /\  m.round # 0 =>
                                           /\ m.primed => 
                                               \E Q_1 \in Quorums : \E A_1 \in QuorumAnswers(Q_1) :
                                                   /\  AllIdenticalRounds(A_1) /\ AllIdenticalValues(A_1)
                                                   /\  m.val = PickValue(A_1)
                                                   /\  m.round = PickRound(A_1) + 1
                                           /\ ~m.primed =>
                                               \E Q_1 \in Quorums : \E A_1 \in QuorumAnswers(Q_1) :
                                                   /\  AllIdenticalRounds(A_1)
                                                   /\  m.val \in SuccessorValues(A_1)
                                                   /\  m.round = PickRound(A_1) + 1)'
                OBVIOUS
              <7>1. (m.round = 0 => ~m.primed)'
                <8>1 CASE m \in msgs
                  BY <8>1
                <8>2 CASE m \notin msgs
                  <9>1 m = [type |-> "Offer", val |-> PickValue(A), round |-> PickRound(A) + 1, primed |-> TRUE]
                    BY <3>1, <4>4, <5>1, <8>2 DEF TrySend, Send
                  <9>2 A \in SUBSET Messages /\ A # {} /\ \A a \in A : a.lastRound \in Rounds
                    BY <3>1, QuorumAssumption DEF QuorumAnswers, Answers, Messages
                  <9>3 PickRound(A) \in Rounds
                    BY <9>2, PickRoundImage
                  <9>4 PickRound(A) + 1 > 0
                    BY <9>3 DEF Rounds
                  <9>5 QED
                    BY <9>1, <9>4
                <8>3 QED
                  BY <8>1, <8>2
              <7>2. (m.round # 0 =>
                         /\ m.primed => 
                             \E Q_1 \in Quorums : \E A_1 \in QuorumAnswers(Q_1) :
                                 /\  AllIdenticalRounds(A_1) /\ AllIdenticalValues(A_1)
                                 /\  m.val = PickValue(A_1)
                                 /\  m.round = PickRound(A_1) + 1
                         /\ ~m.primed =>
                             \E Q_1 \in Quorums : \E A_1 \in QuorumAnswers(Q_1) :
                                 /\  AllIdenticalRounds(A_1)
                                 /\  m.val \in SuccessorValues(A_1)
                                 /\  m.round = PickRound(A_1) + 1)'
                <8> SUFFICES ASSUME (m.round # 0)'
                             PROVE  (/\ m.primed => 
                                         \E Q_1 \in Quorums : \E A_1 \in QuorumAnswers(Q_1) :
                                             /\  AllIdenticalRounds(A_1) /\ AllIdenticalValues(A_1)
                                             /\  m.val = PickValue(A_1)
                                             /\  m.round = PickRound(A_1) + 1
                                     /\ ~m.primed =>
                                         \E Q_1 \in Quorums : \E A_1 \in QuorumAnswers(Q_1) :
                                             /\  AllIdenticalRounds(A_1)
                                             /\  m.val \in SuccessorValues(A_1)
                                             /\  m.round = PickRound(A_1) + 1)'
                  OBVIOUS
                <8>1. (m.primed => 
                        \E Q_1 \in Quorums : \E A_1 \in QuorumAnswers(Q_1) :
                            /\  AllIdenticalRounds(A_1) /\ AllIdenticalValues(A_1)
                            /\  m.val = PickValue(A_1)
                            /\  m.round = PickRound(A_1) + 1)'
                  \* TODO too many SUFFICES steps - rewrite using CASE statements (as shown below)
                  <9> SUFFICES ASSUME (m.primed)'
                               PROVE  (\E Q_1 \in Quorums : \E A_1 \in QuorumAnswers(Q_1) :
                                           /\  AllIdenticalRounds(A_1) /\ AllIdenticalValues(A_1)
                                           /\  m.val = PickValue(A_1)
                                           /\  m.round = PickRound(A_1) + 1)'
                    OBVIOUS
                  <9>1 CASE m \in msgs
                    <10>1 msgs' = msgs \union {[type |-> "Offer", val |-> PickValue(A), round |-> PickRound(A) + 1, primed |-> TRUE]}
                      BY <3>1, <4>4, <5>1 DEF TrySend, Send
                    <10>2 QED
                      BY <10>1, <9>1 DEF QuorumAnswers, Answers, AllIdenticalRounds, AllIdenticalValues, PickValue, PickRound
                  <9>2 CASE m \notin msgs
                    <10>1 m = [type |-> "Offer", val |-> PickValue(A), round |-> PickRound(A) + 1, primed |-> TRUE]
                      BY <3>1, <4>4, <5>1, <9>2 DEF TrySend, Send
                    <10>99 QED
                      BY <3>1, <4>4, <5>1, <10>1, <9>2 DEF TrySend, Send, QuorumAnswers, Answers
                  <9>3 QED
                    BY <9>1, <9>2
                <8>2. (~m.primed =>
                        \E Q_1 \in Quorums : \E A_1 \in QuorumAnswers(Q_1) :
                            /\  AllIdenticalRounds(A_1)
                            /\  m.val \in SuccessorValues(A_1)
                            /\  m.round = PickRound(A_1) + 1)'
                  <9>1 CASE m.primed
                    BY <9>1
                  <9>2 CASE ~m.primed /\ m \in msgs
                    <10>1 msgs' = msgs \union {[type |-> "Offer", val |-> PickValue(A), round |-> PickRound(A) + 1, primed |-> TRUE]}
                      BY <3>1, <4>4, <5>1 DEF TrySend, Send
                    <10>2 QED
                      BY <10>1, <9>2 DEF QuorumAnswers, Answers
                  <9>3 CASE ~m.primed /\ m \notin msgs
                    <10>1 m = [type |-> "Offer", val |-> PickValue(A), round |-> PickRound(A) + 1, primed |-> TRUE]
                      BY <3>1, <4>4, <5>1, <9>3 DEF TrySend, Send
                    <10>99 QED
                      BY <3>1, <4>4, <5>1, <10>1, <9>3 DEF TrySend, Send, QuorumAnswers, Answers
                  <9>4 QED
                    BY <9>1, <9>2, <9>3
                <8>3. QED
                  BY <8>1, <8>2
              <7>3. QED
                BY <7>1, <7>2
            <6>2. (m.type = "Answer" =>
                       \E o \in msgs : 
                             /\  o.type = "Offer"
                             /\  o.round = m.lastRound
                             /\  o.val = m.lastVal
                             /\  o.primed = m.lastPrimed)'
              BY <1>1, <3>1, <4>4, <5>1 DEF TrySend, Send
            <6>3. QED
              BY <6>1, <6>2
          <5>2 CASE ~AllIdenticalValues(A)
            <6> SUFFICES ASSUME NEW m \in msgs'
                         PROVE  (/\  m.type = "Offer" =>
                                         /\  m.round = 0 => ~m.primed
                                         /\  m.round # 0 =>
                                                 /\ m.primed => 
                                                     \E Q_1 \in Quorums : \E A_1 \in QuorumAnswers(Q_1) :
                                                         /\  AllIdenticalRounds(A_1) /\ AllIdenticalValues(A_1)
                                                         /\  m.val = PickValue(A_1)
                                                         /\  m.round = PickRound(A_1) + 1
                                                 /\ ~m.primed =>
                                                     \E Q_1 \in Quorums : \E A_1 \in QuorumAnswers(Q_1) :
                                                         /\  AllIdenticalRounds(A_1)
                                                         /\  m.val \in SuccessorValues(A_1)
                                                         /\  m.round = PickRound(A_1) + 1
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
                                   \E Q_1 \in Quorums : \E A_1 \in QuorumAnswers(Q_1) :
                                       /\  AllIdenticalRounds(A_1) /\ AllIdenticalValues(A_1)
                                       /\  m.val = PickValue(A_1)
                                       /\  m.round = PickRound(A_1) + 1
                               /\ ~m.primed =>
                                   \E Q_1 \in Quorums : \E A_1 \in QuorumAnswers(Q_1) :
                                       /\  AllIdenticalRounds(A_1)
                                       /\  m.val \in SuccessorValues(A_1)
                                       /\  m.round = PickRound(A_1) + 1)'
              <7> SUFFICES ASSUME (m.type = "Offer")'
                           PROVE  (/\  m.round = 0 => ~m.primed
                                   /\  m.round # 0 =>
                                           /\ m.primed => 
                                               \E Q_1 \in Quorums : \E A_1 \in QuorumAnswers(Q_1) :
                                                   /\  AllIdenticalRounds(A_1) /\ AllIdenticalValues(A_1)
                                                   /\  m.val = PickValue(A_1)
                                                   /\  m.round = PickRound(A_1) + 1
                                           /\ ~m.primed =>
                                               \E Q_1 \in Quorums : \E A_1 \in QuorumAnswers(Q_1) :
                                                   /\  AllIdenticalRounds(A_1)
                                                   /\  m.val \in SuccessorValues(A_1)
                                                   /\  m.round = PickRound(A_1) + 1)'
                OBVIOUS
              <7>1. (m.round = 0 => ~m.primed)'
                <8>1 CASE m \in msgs
                  BY <8>1
                <8>2 CASE m \notin msgs
                  <9>1 \E v \in SuccessorValues(A) : 
                            m = [type |-> "Offer", val |-> v, round |-> PickRound(A) + 1, primed |-> FALSE]
                    BY <3>1, <4>4, <5>2, <8>2 DEF TrySend, Send
                  <9>2 A \in SUBSET Messages /\ A # {} /\ \A a \in A : a.lastRound \in Rounds
                    BY <3>1, QuorumAssumption DEF QuorumAnswers, Answers, Messages
                  <9>3 PickRound(A) \in Rounds
                    BY <9>2, PickRoundImage
                  <9>4 PickRound(A) + 1 > 0
                    BY <9>3 DEF Rounds
                  <9>5 QED
                    BY <9>1, <9>4
                <8>3 QED
                  BY <8>1, <8>2
              <7>2. (m.round # 0 =>
                         /\ m.primed => 
                             \E Q_1 \in Quorums : \E A_1 \in QuorumAnswers(Q_1) :
                                 /\  AllIdenticalRounds(A_1) /\ AllIdenticalValues(A_1)
                                 /\  m.val = PickValue(A_1)
                                 /\  m.round = PickRound(A_1) + 1
                         /\ ~m.primed =>
                             \E Q_1 \in Quorums : \E A_1 \in QuorumAnswers(Q_1) :
                                 /\  AllIdenticalRounds(A_1)
                                 /\  m.val \in SuccessorValues(A_1)
                                 /\  m.round = PickRound(A_1) + 1)'
                <8> SUFFICES ASSUME (m.round # 0)'
                             PROVE  (/\ m.primed => 
                                         \E Q_1 \in Quorums : \E A_1 \in QuorumAnswers(Q_1) :
                                             /\  AllIdenticalRounds(A_1) /\ AllIdenticalValues(A_1)
                                             /\  m.val = PickValue(A_1)
                                             /\  m.round = PickRound(A_1) + 1
                                     /\ ~m.primed =>
                                         \E Q_1 \in Quorums : \E A_1 \in QuorumAnswers(Q_1) :
                                             /\  AllIdenticalRounds(A_1)
                                             /\  m.val \in SuccessorValues(A_1)
                                             /\  m.round = PickRound(A_1) + 1)'
                  OBVIOUS
                <8>1. (m.primed => 
                        \E Q_1 \in Quorums : \E A_1 \in QuorumAnswers(Q_1) :
                            /\  AllIdenticalRounds(A_1) /\ AllIdenticalValues(A_1)
                            /\  m.val = PickValue(A_1)
                            /\  m.round = PickRound(A_1) + 1)'
\*                  <9>1 CASE ~m.primed
\*                    BY <9>1
                  <9>2 CASE m.primed /\ m \in msgs
                    <10>1 \E v \in SuccessorValues(A) : 
                              msgs' = msgs \union {[type |-> "Offer", val |-> v, round |-> PickRound(A) + 1, primed |-> FALSE]}
                      BY <3>1, <4>4, <5>2 DEF TrySend, Send
                    <10>2 QED
                      BY <10>1, <9>2 DEF QuorumAnswers, Answers   
                  <9>3 CASE m.primed /\ m \notin msgs
                    <10>1 \E v \in SuccessorValues(A) : 
                              m = [type |-> "Offer", val |-> v, round |-> PickRound(A) + 1, primed |-> FALSE]
                      BY <3>1, <4>4, <5>2, <9>3 DEF TrySend, Send
                    <10>2 QED
                      BY <10>1, <9>3          
                  <9>4 QED
                    BY <9>2, <9>3
                <8>2. (~m.primed =>
                        \E Q_1 \in Quorums : \E A_1 \in QuorumAnswers(Q_1) :
                            /\  AllIdenticalRounds(A_1)
                            /\  m.val \in SuccessorValues(A_1)
                            /\  m.round = PickRound(A_1) + 1)'
                  <9>4 CASE ~m.primed /\ m \in msgs
                    <10>1 \E v \in SuccessorValues(A) : 
                              msgs' = msgs \union {[type |-> "Offer", val |-> v, round |-> PickRound(A) + 1, primed |-> FALSE]}
                      BY <3>1, <4>4, <5>2 DEF TrySend, Send
                    <10>2 QED
                      BY <10>1, <9>4 DEF QuorumAnswers, Answers  
                  <9>5 CASE ~m.primed /\ m \notin msgs
                    <10>1 \E v \in SuccessorValues(A) : 
                              m = [type |-> "Offer", val |-> v, round |-> PickRound(A) + 1, primed |-> FALSE]
                      BY <3>1, <4>4, <5>2, <9>5 DEF TrySend, Send
                    <10>3 msgs \subseteq msgs'
                      BY <3>1 DEF TrySend, Send
                    <10>31 (Q \in Quorums /\ A \in QuorumAnswers(Q) /\ AllIdenticalRounds(A))'
                      BY <3>1, <4>4, <5>2, <9>5, <10>3 DEF QuorumAnswers, Answers, AllIdenticalRounds, Rounds, Messages
                    <10>4 (m.val \in SuccessorValues(A))'
                      BY <3>1, <4>4, <5>2, <9>5, <10>1
                    <10>5 (m.round = PickRound(A) + 1)'
                      BY <3>1, <4>4, <5>2, <9>5, <10>1
                    <10>6 QED
                      BY <10>31, <10>4, <10>5
                  <9>6 QED
                    BY <9>4, <9>5
                <8>3. QED
                  BY <8>1, <8>2
              <7>3. QED
                BY <7>1, <7>2
            <6>2. (m.type = "Answer" =>
                       \E o \in msgs : 
                             /\  o.type = "Offer"
                             /\  o.round = m.lastRound
                             /\  o.val = m.lastVal
                             /\  o.primed = m.lastPrimed)'
              <7>1 CASE m \in msgs
                BY <1>1, <3>1, <4>4, <5>2, <7>1 DEF TrySend, Send
              <7>2 CASE m \notin msgs
                \* If `m' is not in msgs, then it must be an answer type.
                <8>1 \E v \in SuccessorValues(A) : 
                          m = [type |-> "Offer", val |-> v, round |-> PickRound(A) + 1, primed |-> FALSE]
                  BY <3>1, <4>4, <5>2, <7>2 DEF TrySend, Send
                <8>2 QED
                  BY <8>1
              <7>3 QED
                BY <7>1, <7>2
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
                                                   \E Q_1 \in Quorums : \E A_1 \in QuorumAnswers(Q_1) :
                                                         /\  AllIdenticalRounds(A_1) /\ AllIdenticalValues(A_1)
                                                       /\  m.val = PickValue(A_1)
                                                       /\  m.round = PickRound(A_1) + 1
                                               /\ ~m.primed =>
                                                   \E Q_1 \in Quorums : \E A_1 \in QuorumAnswers(Q_1) :
                                                         /\  AllIdenticalRounds(A_1)
                                                       /\  m.val \in SuccessorValues(A_1)
                                                       /\  m.round = PickRound(A_1) + 1
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
                                 \E Q_1 \in Quorums : \E A_1 \in QuorumAnswers(Q_1) :
                                     /\  AllIdenticalRounds(A_1) /\ AllIdenticalValues(A_1)
                                     /\  m.val = PickValue(A_1)
                                     /\  m.round = PickRound(A_1) + 1
                             /\ ~m.primed =>
                                 \E Q_1 \in Quorums : \E A_1 \in QuorumAnswers(Q_1) :
                                     /\  AllIdenticalRounds(A_1)
                                     /\  m.val \in SuccessorValues(A_1)
                                     /\  m.round = PickRound(A_1) + 1)'
            <6>1 CASE m.round = 0
              <8>1 CASE m \in msgs
                  BY <6>1, <8>1
              <8>2 CASE m \notin msgs
                <9>1 \E v \in SuccessorValues(A) : 
                          m = [type |-> "Offer", val |-> v, round |-> MaxLastRound(A), primed |-> FALSE]
                  BY <3>1, <4>5, <6>1, <8>2 DEF TrySend, Send
                <9>2 A \in SUBSET Messages /\ A # {} /\ \A a \in A : a.lastRound \in Rounds
                  BY <3>1, QuorumAssumption DEF QuorumAnswers, Answers, Messages
                <9>3 PickRound(A) \in Rounds
                  BY <9>2, PickRoundImage
                <9>4 PickRound(A) + 1 > 0
                  BY <9>3 DEF Rounds
                <9>5 QED
                  BY <6>1, <8>2, <9>1, <9>4
              <8>3 QED
                BY <8>1, <8>2
            <6>2 CASE m.round # 0 /\ m.primed
              <8>1 CASE m.type = "Offer" /\ m \in msgs
                <10>1 \E v \in SuccessorValues(A) : 
                          msgs' = msgs \union {[type |-> "Offer", val |-> v, round |-> MaxLastRound(A), primed |-> FALSE]}
                  BY <3>1, <4>5, <6>2 DEF TrySend, Send
                <10>2 \E Q_1 \in Quorums : \E A_1 \in QuorumAnswers(Q_1) :
                                     /\  AllIdenticalRounds(A_1) /\ AllIdenticalValues(A_1)
                                     /\  m.val = PickValue(A_1)
                                     /\  m.round = PickRound(A_1) + 1
                  BY <3>1, <4>5, <6>2, <8>1
                <10>99 QED
                  BY <6>2, <8>1, <10>1, <10>2 DEF QuorumAnswers, Answers 
              <8>2 CASE m.type = "Offer" /\ m \notin msgs
                <10>1 \E v \in SuccessorValues(A) : 
                          m = [type |-> "Offer", val |-> v, round |-> MaxLastRound(A), primed |-> FALSE]
                   BY <3>1, <4>5, <6>2, <8>2 DEF TrySend, Send
                <10>99 QED
                   BY <6>2, <8>2, <10>1
              <8>3
                QED BY <8>1, <8>2
            <6>3 CASE m.round # 0 /\ ~m.primed
              <8>1 CASE m.type = "Offer" /\ m \in msgs
                <10>1 \E v \in SuccessorValues(A) : 
                          msgs' = msgs \union {[type |-> "Offer", val |-> v, round |-> MaxLastRound(A), primed |-> FALSE]}
                  BY <3>1, <4>5, <6>3 DEF TrySend, Send
                <10>2 \E Q_1 \in Quorums : \E A_1 \in QuorumAnswers(Q_1) :
                                     /\  AllIdenticalRounds(A_1)
                                     /\  m.val \in SuccessorValues(A_1)
                                     /\  m.round = PickRound(A_1) + 1
                  BY <3>1, <4>5, <6>3, <8>1
                <10>99 QED
                  BY <6>3, <8>1, <10>1, <10>2 DEF QuorumAnswers, Answers 
              <8>2 CASE m.type = "Offer" /\ m \notin msgs
                <10>1 \E v \in SuccessorValues(A) : 
                          m = [type |-> "Offer", val |-> v, round |-> MaxLastRound(A), primed |-> FALSE]
                   BY <3>1, <4>5, <6>3, <8>2 DEF TrySend, Send
                <10>2 MaxLastRound(A) = m.round
                   BY <10>1
                <10>3 A # {}
                   BY <3>1, QuorumAssumption DEF QuorumAnswers, Answers
                <10>4 SuccessorValues(A) # {}
                  BY <10>1
                <10>a DEFINE highestRoundAnswers == {a \in A : a.lastRound = MaxLastRound(A)}
                <10>b DEFINE highestRoundPrimedAnswers == {a \in highestRoundAnswers : a.lastPrimed}
                <10>5 SuccessorValues(A) = IF highestRoundPrimedAnswers # {} THEN 
                                              {PickValue(highestRoundPrimedAnswers)}
                                           ELSE
                                              {a.lastVal : a \in highestRoundAnswers}
                   BY <3>1 DEF SuccessorValues
                <10>6 \A v \in SuccessorValues(A) : \E a \in A : a.lastVal = v /\ a.lastRound = MaxLastRound(A)
                  BY <10>5 DEF PickValue
                <10>7 \E a \in A : a.lastRound = MaxLastRound(A) /\ a.lastVal \in SuccessorValues(A)
                  BY <10>6, <10>4
                <10>9 PICK a \in A : a.lastRound = m.round /\ a.lastVal = m.val
                  BY <10>1, <10>6
                <10>10 a \in msgs /\ a.type = "Answer"
                  BY <3>1 DEF QuorumAnswers, Answers
                <10>11 PICK o \in msgs : o.type = "Offer" /\ o.round = a.lastRound /\ o.val = a.lastVal /\ o.primed = a.lastPrimed
                  BY <3>1, <10>9, <10>10
                <10>12 o.round # 0 /\ o.val = m.val /\ o.round = m.round
                  BY <6>3, <10>11, <10>9
                <10>13 msgs \subseteq msgs'
                  BY <3>1 DEF TrySend, Send
                <10>14 m.type = "Offer" /\ m.round # 0 /\ ~m.primed
                  BY <10>1, <10>12
                <10>20 o.primed => \E R \in Quorums : \E B \in QuorumAnswers(R) :
                                         /\  AllIdenticalRounds(B) /\ AllIdenticalValues(B)
                                         /\  o.val = PickValue(B)
                                         /\  o.round = PickRound(B) + 1
                  BY <3>1, <10>9, <10>11, <10>12
                <10>30 ~o.primed => \E R \in Quorums : \E B \in QuorumAnswers(R) :
                                         /\  AllIdenticalRounds(B)
                                         /\  o.val \in SuccessorValues(B)
                                         /\  o.round = PickRound(B) + 1
                  BY <3>1, <10>9, <10>11, <10>12
                <10>21 CASE o.primed
                  \* TODO easiest thing is to prove that AllIdenticalRounds(M) /\ AllIdenticalValues(M) => SuccessorValues(M) = {PickValue(M)}
\*                  <11>0 \A B \in SUBSET Messages : AllIdenticalRounds(B) /\ AllIdenticalValues(B) => SuccessorValues(B) = {PickValue(B)}
                  <11>1 (\E R \in Quorums : \E B \in QuorumAnswers(R) :
                                         /\  AllIdenticalRounds(B) /\ AllIdenticalValues(B)
                                         /\  m.val = PickValue(B)
                                         /\  m.round = PickRound(B) + 1)
                     BY <10>20, <10>21, <10>12
                  <11>2 (\E R \in Quorums : \E B \in QuorumAnswers(R) :
                                         /\  AllIdenticalRounds(B)
                                         /\  m.val \in SuccessorValues(B)
                                         /\  m.round = PickRound(B) + 1)'
                     BY <10>13, <11>1, UniformAnswerSuccessorSingularity, QuorumAssumption DEF QuorumAnswers, Answers
                  <11>4 QED
                    BY <11>2, <10>14
                <10>31 CASE ~o.primed
                  <11>1 (\E R \in Quorums : \E B \in QuorumAnswers(R) :
                                         /\  AllIdenticalRounds(B)
                                         /\  m.val \in SuccessorValues(B)
                                         /\  m.round = PickRound(B) + 1)'
                     BY <10>30, <10>31, <10>12, <10>13 DEF QuorumAnswers, Answers
                  <11>3 QED
                    BY <11>1, <10>14
                <10>99 QED
                  BY <10>21, <10>31
              <8>3
                QED BY <8>1, <8>2
            <6>4 QED 
              BY <6>1, <6>2, <6>3
          <5>2. (m.type = "Answer" =>
                     \E o \in msgs : 
                           /\  o.type = "Offer"
                           /\  o.round = m.lastRound
                           /\  o.val = m.lastVal
                           /\  o.primed = m.lastPrimed)'
              <7>1 CASE m \in msgs
                BY <1>1, <3>1, <4>5, <7>1 DEF TrySend, Send
              <7>2 CASE m \notin msgs
                \* If `m' is not in msgs, then it must be an answer type.
                <8>1 \E v \in SuccessorValues(A) : 
                          m = [type |-> "Offer", val |-> v, round |-> MaxLastRound(A), primed |-> FALSE]
                  BY <3>1, <4>5, <7>2 DEF TrySend, Send
                <8>2 QED
                  BY <8>1
              <7>3 QED
                BY <7>1, <7>2
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
        <4>1. (m.type = "Offer" =>
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
            <8>1 CASE m \in msgs
              <10>1 msgs' = msgs \union {[type |-> "Offer", val |-> v, round |-> 0, primed |-> FALSE]}
                BY <3>2 DEF TrySend, Send
              <10>2 QED
                BY <3>2, <8>1, <10>1 DEF QuorumAnswers, Answers, AllIdenticalRounds, AllIdenticalValues
            <8>2 CASE m \notin msgs
              <9>1 m = [type |-> "Offer", val |-> v, round |-> 0, primed |-> FALSE]
                BY <3>2, <8>2 DEF TrySend, Send
              <9>5 QED
                BY <9>1
            <8>3 QED
              BY <8>1, <8>2
        <4>2. (m.type = "Answer" =>
                   \E o \in msgs : 
                         /\  o.type = "Offer"
                         /\  o.round = m.lastRound
                         /\  o.val = m.lastVal
                         /\  o.primed = m.lastPrimed)'
          <7>1 CASE m \in msgs
            BY <3>2, <7>1 DEF TrySend, Send
          <7>2 CASE m \notin msgs
            \* If `m' is not in msgs, then it must be an answer type.
            <8>1 m = [type |-> "Offer", val |-> v, round |-> 0, primed |-> FALSE]
              BY <3>2, <7>2 DEF TrySend, Send
            <8>2 QED
              BY <8>1
          <7>3 QED
            BY <7>1, <7>2
        <4>3. QED
          BY <4>1, <4>2
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
                           \* no answer may exist for a round above lastRound[c]
                           /\  ~\E m \in msgs : m.type = "Answer" /\ m.cons = c /\ m.lastRound > lastRound[c]
                           \* a consenter answers at most once for any given lastRound
                           /\  \A m1, m2 \in msgs :
                                   m1.type = "Answer" /\ m2.type = "Answer" /\ m1.cons = c /\ m2.cons = c /\ m1.lastRound = m2.lastRound => m1 = m2)'
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
          <5>1 \/ msgs' = msgs \union {[type |-> "Offer", val |-> PickValue(A), round |-> PickRound(A) + 1, primed |-> TRUE]}
               \/ \E v \in SuccessorValues(A) :
                     msgs' = msgs \union {[type |-> "Offer", val |-> v, round |-> PickRound(A) + 1, primed |-> FALSE]}
               \/ \E v \in SuccessorValues(A) :
                     msgs' = msgs \union {[type |-> "Offer", val |-> v, round |-> MaxLastRound(A), primed |-> FALSE]}
            BY <4>1 DEF TrySend, Send
          <5>2 \A m \in msgs' \ msgs : m.type = "Offer"
            BY <5>1
          <5>3 QED
            BY <1>1, <4>1, <5>2
        <4>2. ASSUME NEW v \in Values,
                     TrySend([type |-> "Offer", val |-> v, round |-> 0, primed |-> FALSE])
              PROVE  (~\E m \in msgs : m.type = "Answer" /\ m.cons = c /\ m.lastRound > lastRound[c])'
          <5>1 msgs' = msgs \union {[type |-> "Offer", val |-> v, round |-> 0, primed |-> FALSE]}
            BY <4>2 DEF TrySend, Send
          <5>2 QED
            BY <1>1, <4>1, <5>1
        <4>3. QED
          BY <1>1, <4>1, <4>2
      <3>5. (\A m1, m2 \in msgs :
                 m1.type = "Answer" /\ m2.type = "Answer" /\ m1.cons = c /\ m2.cons = c /\ m1.lastRound = m2.lastRound => m1 = m2)'
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
                          m1.type = "Answer" /\ m2.type = "Answer" /\ m1.cons = c /\ m2.cons = c /\ m1.lastRound = m2.lastRound => m1 = m2)'
          <5>1 \/ msgs' = msgs \union {[type |-> "Offer", val |-> PickValue(A), round |-> PickRound(A) + 1, primed |-> TRUE]}
               \/ \E v \in SuccessorValues(A) :
                     msgs' = msgs \union {[type |-> "Offer", val |-> v, round |-> PickRound(A) + 1, primed |-> FALSE]}
               \/ \E v \in SuccessorValues(A) :
                     msgs' = msgs \union {[type |-> "Offer", val |-> v, round |-> MaxLastRound(A), primed |-> FALSE]}
            BY <4>1 DEF TrySend, Send
          <5>2 \A m \in msgs' \ msgs : m.type = "Offer"
            BY <5>1
          <5>3 QED
            BY <1>1, <4>1, <5>2
        <4>2. ASSUME NEW v \in Values,
                     TrySend([type |-> "Offer", val |-> v, round |-> 0, primed |-> FALSE])
              PROVE  (\A m1, m2 \in msgs :
                          m1.type = "Answer" /\ m2.type = "Answer" /\ m1.cons = c /\ m2.cons = c /\ m1.lastRound = m2.lastRound => m1 = m2)'
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
         <4>1 CASE n \notin msgs
           BY <1>2, <4>1 DEF Send
         <4>2 CASE n \in msgs
           BY <1>2, <4>2 DEF Send, Messages, QuorumAnswers, Answers
         <4>3 QED
           BY <4>1, <4>2
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
                           /\  lastRound[d] # -1 => \E m_1 \in msgs : 
                                   /\  m_1.type = "Answer" 
                                   /\  m_1.cons = d 
                                   /\  m_1.lastRound = lastRound[d]
                                   /\  m_1.lastVal = lastVal[d]
                                   /\  m_1.lastPrimed = lastPrimed[d]
                           /\  ~\E m_1 \in msgs : m_1.type = "Answer" /\ m_1.cons = d /\ m_1.lastRound > lastRound[d]
                           /\  \A m1, m2 \in msgs :
                                   m1.type = "Answer" /\ m2.type = "Answer" /\ m1.cons = d /\ m2.cons = d /\ m1.lastRound = m2.lastRound => m1 = m2)'
        BY DEF ConsInv
      <3> USE DEF ConsInv
      <3>1. (lastRound[d] = -1 <=> lastVal[d] = None)'
        <4>1 CASE d # c
          BY <1>2, <4>1
        <4>2 CASE d = c
          <5>1 lastRound[d]' = m.round /\ lastRound[d]' # -1
            BY <1>2, <4>2 DEF Rounds
          <5>2 lastVal[d]' = m.val /\ lastVal[d]' # None
            BY <1>2, <4>2, NoneNotAValue DEF Messages
          <5>99 QED
            BY <5>1, <5>2
        <4>3 QED
          BY <4>1, <4>2
      <3>2. (lastRound[d] = -1 => ~lastPrimed[d])'
        <4>1 CASE d # c
          BY <1>2, <4>1
        <4>2 CASE d = c
          BY <1>2, <4>2 DEF Rounds
        <4>3 QED
          BY <4>1, <4>2
      <3>3. (lastRound[d] # -1 => \E m_1 \in msgs : 
                 /\  m_1.type = "Answer" 
                 /\  m_1.cons = d 
                 /\  m_1.lastRound = lastRound[d]
                 /\  m_1.lastVal = lastVal[d]
                 /\  m_1.lastPrimed = lastPrimed[d])'
        <4>1 CASE d # c
          BY <1>2, <4>1 DEF Send
        <4>2 CASE d = c
          <5>1 lastRound[d]' = m.round /\ lastRound[d]' # -1
            BY <1>2, <4>2 DEF Rounds
          <5>2 lastVal[d]' = m.val /\ lastPrimed[d]' = m.primed
            BY <1>2, <4>2
          <5>2b \E mmm \in msgs' : mmm = [type |-> "Answer", cons |-> c, lastVal |-> m.val, lastRound |-> m.round, lastPrimed |-> m.primed]
            BY <1>2 DEF Send
          <5>99 QED
            BY <1>2, <4>2, <5>2b DEF Send
        <4>3 QED
          BY <4>1, <4>2
      <3>4. (~\E n \in msgs : n.type = "Answer" /\ n.cons = d /\ n.lastRound > lastRound[d])'
        BY <1>2 DEF Send, Messages, Rounds
      <3>5. (\A m1, m2 \in msgs :
                 m1.type = "Answer" /\ m2.type = "Answer" /\ m1.cons = d /\ m2.cons = d /\ m1.lastRound = m2.lastRound 
                      => m1 = m2)'
        BY <1>2 DEF Send, Messages
      <3>6. QED
        BY <3>1, <3>2, <3>3, <3>4, <3>5
    <2>7. QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6 DEF Inv
  <1>3. CASE Decided
    BY <1>3, InvariantPreservedOnUnchanged DEF Decided
  <1>4. CASE Terminated
    BY <1>4, InvariantPreservedOnUnchanged DEF Terminated
  <1>5. QED
    BY <1>1, <1>2, <1>3, <1>4 DEF Answer, Next

THEOREM Correctness == Spec => []Consistency  
  <1> USE DEF Spec, Consistency
  <1>1 Init => Inv
    BY Initial
  <1>2 Inv /\ [Next]_vars => Inv'
    <2>1 CASE Next
      BY Inductive, <2>1
    <2>2 CASE UNCHANGED vars
      BY <2>2, InvariantPreservedOnUnchanged
    <2>3 QED
      BY <2>1, <2>2
  <1>3 Inv => Consistency
    BY Consistent DEF Inv
  <1>4 QED
    BY <1>1, <1>2, <1>3, PTL
====