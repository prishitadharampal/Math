--------------------------- MODULE MCS_Proofs ---------------------------

EXTENDS MCS, TLAPS


TypeOK ==
  /\ mem    \in [Nodes -> MemVals]
  /\ goVal  \in [ProcSet -> BOOLEAN]
  /\ tail   \in Nodes
  /\ mynode \in [ProcSet -> Nodes]
  /\ mypred \in [ProcSet -> Nodes]
  /\ nxtgo  \in [ProcSet -> MemVals]
  /\ pc     \in [ProcSet -> Lines]



InQ(p)     == pc[p] \in {"T4", "T5", "E1"}
Own(p)     == IF pc[p] \in {"E2", "E3"} THEN mypred[p] ELSE mynode[p]
Owned(n)   == \E q \in ProcSet : Own(q) = n
Head(p)    == InQ(p) /\ ~Owned(mypred[p])   \* first process in the queue
Pred(q, p) == InQ(q) /\ InQ(p) /\ mypred[p] = mynode[q]

OwnInj      == \A p, q \in ProcSet : p # q => Own(p) # Own(q)
OneHead     == \A p, q \in ProcSet : p # q => ~(Head(p) /\ Head(q))
PredOwned   == \A p, q \in ProcSet : InQ(p) /\ mypred[p] = Own(q) => InQ(q)
PredInj     == \A p, q \in ProcSet : p # q /\ InQ(p) /\ InQ(q) => mypred[p] # mypred[q]
CSHead      == \A p \in ProcSet : pc[p] = "E1" => Head(p)
Handoff     == \A p, q \in ProcSet : Pred(q, p) =>
                 \/ pc[p] = "T4" /\ mem[mynode[q]] = NIL
                 \/ pc[p] = "T5" /\ mem[mynode[q]] = p
NodeNil     == \A q \in ProcSet :
                 (/\ pc[q] \in {"T2", "T3", "T4", "T5", "E1"}
                  /\ ~(\E p \in ProcSet : Pred(q, p)))
                 => mem[mynode[q]] = NIL
FlagState   == \A p \in ProcSet : goVal[p] /\ pc[p] \in {"T3", "T4", "T5"} =>
                 /\ pc[p] = "T5" /\ Head(p)
                 /\ \A r \in ProcSet : pc[r] = "E2" => nxtgo[r] # p
Waker       == \A r \in ProcSet : pc[r] = "E2" /\ nxtgo[r] # NIL =>
                 LET t == nxtgo[r] IN
                 /\ t \in ProcSet /\ Head(t) /\ pc[t] = "T5"
                 /\ \A s \in ProcSet : pc[s] = "E2" /\ nxtgo[s] = t => s = r
PredNotTail == \A p \in ProcSet : InQ(p) => mypred[p] # tail
TailState   == IF Owned(tail)
               THEN \E r \in ProcSet : InQ(r) /\ tail = mynode[r]
               ELSE \A p \in ProcSet : ~Head(p)

Inv == OwnInj /\ OneHead /\ PredOwned /\ PredInj /\ CSHead /\ Handoff
       /\ NodeNil /\ FlagState /\ Waker /\ PredNotTail /\ TailState

LEMMA SpecTypeOK == Spec => []TypeOK
  <1>1. Init => TypeOK
    <2> SUFFICES ASSUME Init
                 PROVE  TypeOK
      OBVIOUS
    <2> QED
      BY ConstAssump DEF Init, TypeOK, Nodes, MemVals, Lines
  <1>2. TypeOK /\ [Next]_vars => TypeOK'
    <2> SUFFICES ASSUME TypeOK /\ [Next]_vars
                 PROVE  TypeOK'
      OBVIOUS
    <2> USE DEF TypeOK
    <2>1. ASSUME NEW p \in ProcSet,
                 NEW LineAct \in LineActs(p),
                 LineAct
          PROVE  TypeOK'
      <3>1. CASE Try(p)
        <4> USE <3>1 DEF Try
        <4> QED
          BY DEF Lines
      <3>2. CASE T1(p)
        <4> USE <3>2 DEF T1
        <4> QED
          BY DEF Nodes, MemVals, Lines
      <3>3. CASE T2(p)
        <4> USE <3>3 DEF T2
        <4> QED
          BY DEF Lines
      <3>4. CASE T3(p)
        <4> USE <3>4 DEF T3
        <4> QED
          BY DEF Nodes, Lines
      <3>5. CASE T4(p)
        <4> USE <3>5 DEF T4
        <4> QED
          BY DEF Nodes, MemVals, Lines
      <3>6. CASE T5(p)
        <4> USE <3>6 DEF T5
        <4> QED
          BY DEF Lines
      <3>7. CASE E1(p)
        <4> USE <3>7 DEF E1
        <4> QED
          BY DEF Nodes, MemVals, Lines
      <3>8. CASE E2(p)
        <4> USE <3>8 DEF E2
        <4> QED
          BY DEF Lines
      <3>9. CASE E3(p)
        <4> USE <3>9 DEF E3
        <4> QED
          BY DEF Nodes, Lines
      <3> QED
        BY <2>1, <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF LineActs
    <2>2. CASE UNCHANGED vars
      BY <2>2 DEF vars
    <2> QED
      BY <2>1, <2>2 DEF Next, LineActs
  <1> QED
    BY <1>1, <1>2, PTL DEF Spec

 \* a step of process p changes only p's entries of pc, mynode and mypred, so Own(q) and InQ(q) are unchanged for every q # p 
 
LEMMA OthersFrame ==
  ASSUME TypeOK,
         NEW p \in ProcSet,
         NEW LineAct \in LineActs(p),
         LineAct,
         NEW q \in ProcSet,
         q # p
  PROVE  Own(q)' = Own(q) /\ InQ(q)' = InQ(q)
  <1>1. pc'[q] = pc[q] /\ mynode'[q] = mynode[q] /\ mypred'[q] = mypred[q]
    <2> USE DEF TypeOK
    <2>1. CASE Try(p)
      BY <2>1 DEF Try
    <2>2. CASE T1(p)
      BY <2>2 DEF T1
    <2>3. CASE T2(p)
      BY <2>3 DEF T2
    <2>4. CASE T3(p)
      BY <2>4 DEF T3
    <2>5. CASE T4(p)
      BY <2>5 DEF T4
    <2>6. CASE T5(p)
      BY <2>6 DEF T5
    <2>7. CASE E1(p)
      BY <2>7 DEF E1
    <2>8. CASE E2(p)
      BY <2>8 DEF E2
    <2>9. CASE E3(p)
      BY <2>9 DEF E3
    <2> QED
      BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9 DEF LineActs
  <1> QED
    BY <1>1 DEF Own, InQ


LEMMA SpecInv == Spec => []Inv
  <1>1. Init /\ TypeOK => Inv
    <2> SUFFICES ASSUME Init, TypeOK
                 PROVE  Inv
      OBVIOUS
    <2>1. \A q \in ProcSet : ~InQ(q) /\ Own(q) = q
      BY DEF Init, InQ, Own
    <2>2. ~Owned(tail)
      BY <2>1, ConstAssump DEF Init, Owned
    <2> QED
      BY <2>1, <2>2 DEF Init, Inv, OwnInj, OneHead, PredOwned, PredInj, CSHead, Handoff,
           NodeNil, FlagState, Waker, PredNotTail, TailState,
                        Head, Pred, InQ
  <1>2. Inv /\ TypeOK /\ [Next /\ TypeOK']_vars => Inv'
    <2> SUFFICES ASSUME Inv /\ TypeOK /\ [Next /\ TypeOK']_vars
                 PROVE  Inv'
      OBVIOUS
    <2>1. ASSUME NEW p \in ProcSet,
                 NEW LineAct \in LineActs(p),
                 LineAct, TypeOK'
          PROVE  Inv'
      <3>1. CASE Try(p)
        <4> USE <3>1 DEF Try
        <4>1. \A q \in ProcSet : Own(q)' = Own(q) /\ InQ(q)' = InQ(q)
          <5> SUFFICES ASSUME NEW q \in ProcSet
                       PROVE  Own(q)' = Own(q) /\ InQ(q)' = InQ(q)
            OBVIOUS
          <5>1. CASE q = p
            BY <5>1 DEF Own, InQ, TypeOK
          <5>2. CASE q # p
            BY <5>2, <2>1, OthersFrame
          <5> QED
            BY <5>1, <5>2
        <4>2. pc'[p] = "T1" /\ \A x \in ProcSet : x # p => pc'[x] = pc[x]
          BY DEF TypeOK
        <4>3. ~InQ(p) /\ \A q \in ProcSet : ~Pred(q, p) /\ ~Pred(p, q)
          BY DEF InQ, Pred
        <4>4. \A q, r \in ProcSet : Head(q)' = Head(q) /\ Pred(q, r)' = Pred(q, r)
          BY <4>1 DEF Head, Pred, Owned
        <4>5. OwnInj' /\ PredOwned' /\ PredInj' /\ PredNotTail'
          BY <4>1 DEF Inv, OwnInj, PredOwned, PredInj, PredNotTail
        <4>6. OneHead' /\ CSHead'
          BY <4>2, <4>4 DEF Inv, OneHead, CSHead
        <4>7. Handoff' /\ NodeNil'
          BY <4>2, <4>3, <4>4 DEF Inv, Handoff, NodeNil
        <4>8. FlagState' /\ Waker'
          BY <4>2, <4>4 DEF Inv, FlagState, Waker
        <4>9. TailState'
          BY <4>1, <4>4 DEF Inv, TailState, Owned
        <4> QED
          BY <4>5, <4>6, <4>7, <4>8, <4>9 DEF Inv

      <3>2. CASE T1(p)
        <4> USE <3>2 DEF T1
        <4>1. \A q \in ProcSet : Own(q)' = Own(q) /\ InQ(q)' = InQ(q)
          <5> SUFFICES ASSUME NEW q \in ProcSet
                       PROVE  Own(q)' = Own(q) /\ InQ(q)' = InQ(q)
            OBVIOUS
          <5>1. CASE q = p
            BY <5>1 DEF Own, InQ, TypeOK
          <5>2. CASE q # p
            BY <5>2, <2>1, OthersFrame
          <5> QED
            BY <5>1, <5>2
        <4>2. /\ pc'[p] = "T2"
              /\ \A x \in ProcSet : x # p => pc'[x] = pc[x]
              /\ mem'[mynode[p]] = NIL
              /\ \A n \in Nodes : n # mynode[p] => mem'[n] = mem[n]
          BY DEF TypeOK
        <4>3. ~InQ(p) /\ \A q \in ProcSet : ~Pred(q, p) /\ ~Pred(p, q)
          BY DEF InQ, Pred
        <4>4. \A q, r \in ProcSet : Head(q)' = Head(q) /\ Pred(q, r)' = Pred(q, r)
          BY <4>1 DEF Head, Pred, Owned
        <4>5. \A q \in ProcSet : q # p /\ pc[q] \in {"T2", "T3", "T4", "T5", "E1"}
                                 => mynode[q] # mynode[p]
          BY DEF Inv, OwnInj, Own
        <4>6. \A q, x \in ProcSet : Pred(q, x) => q # p /\ pc[q] \in {"T2", "T3", "T4", "T5", "E1"}
          BY <4>3 DEF Pred, InQ
        <4>7. OwnInj' /\ PredOwned' /\ PredInj' /\ PredNotTail'
          BY <4>1 DEF Inv, OwnInj, PredOwned, PredInj, PredNotTail
        <4>8. OneHead' /\ CSHead'
          BY <4>2, <4>4 DEF Inv, OneHead, CSHead
        <4>9. Handoff'
          BY <4>2, <4>3, <4>4, <4>5, <4>6 DEF Inv, Handoff, TypeOK
        <4>10. NodeNil'
          BY <4>2, <4>4, <4>5 DEF Inv, NodeNil, TypeOK
        <4>11. FlagState' /\ Waker'
          BY <4>2, <4>4 DEF Inv, FlagState, Waker
        <4>12. TailState'
          BY <4>1, <4>4 DEF Inv, TailState, Owned
        <4> QED
          BY <4>7, <4>8, <4>9, <4>10, <4>11, <4>12 DEF Inv

      <3>3. CASE T2(p)
        <4> USE <3>3 DEF T2
        <4>1. \A q \in ProcSet : Own(q)' = Own(q) /\ InQ(q)' = InQ(q)
          <5> SUFFICES ASSUME NEW q \in ProcSet
                       PROVE  Own(q)' = Own(q) /\ InQ(q)' = InQ(q)
            OBVIOUS
          <5>1. CASE q = p
            BY <5>1 DEF Own, InQ, TypeOK
          <5>2. CASE q # p
            BY <5>2, <2>1, OthersFrame
          <5> QED
            BY <5>1, <5>2
        <4>2. /\ pc'[p] = "T3" /\ goVal'[p] = FALSE
              /\ \A x \in ProcSet : x # p => pc'[x] = pc[x] /\ goVal'[x] = goVal[x]
          BY DEF TypeOK
        <4>3. ~InQ(p) /\ \A q \in ProcSet : ~Pred(q, p) /\ ~Pred(p, q)
          BY DEF InQ, Pred
        <4>4. \A q, r \in ProcSet : Head(q)' = Head(q) /\ Pred(q, r)' = Pred(q, r)
          BY <4>1 DEF Head, Pred, Owned
        <4>5. OwnInj' /\ PredOwned' /\ PredInj' /\ PredNotTail'
          BY <4>1 DEF Inv, OwnInj, PredOwned, PredInj, PredNotTail
        <4>6. OneHead' /\ CSHead'
          BY <4>2, <4>4 DEF Inv, OneHead, CSHead
        <4>7. Handoff' /\ NodeNil'
          BY <4>2, <4>3, <4>4 DEF Inv, Handoff, NodeNil
        <4>8. FlagState' /\ Waker'
          BY <4>2, <4>4 DEF Inv, FlagState, Waker
        <4>9. TailState'
          BY <4>1, <4>4 DEF Inv, TailState, Owned
        <4> QED
          BY <4>5, <4>6, <4>7, <4>8, <4>9 DEF Inv

      <3>4. CASE T3(p)
        <4> USE <3>4 DEF T3
        <4>1. \A q \in ProcSet : Own(q)' = Own(q)
          <5> SUFFICES ASSUME NEW q \in ProcSet
                       PROVE  Own(q)' = Own(q)
            OBVIOUS
          <5>1. CASE q = p
            BY <5>1 DEF Own, TypeOK
          <5>2. CASE q # p
            BY <5>2, <2>1, OthersFrame
          <5> QED
            BY <5>1, <5>2
        <4>2. /\ pc'[p] = "T4" /\ mypred'[p] = tail /\ tail' = mynode[p]
              /\ \A x \in ProcSet : x # p => /\ pc'[x] = pc[x]
                                              /\ mypred'[x] = mypred[x]
                                              /\ InQ(x)' = InQ(x)
          BY DEF TypeOK, InQ
        <4>3. ~InQ(p) /\ InQ(p)' /\ Own(p) = mynode[p]
          BY <4>2 DEF InQ, Own
        <4>4. \A x \in ProcSet : x # p => Head(x)' = Head(x)
          BY <4>1, <4>2 DEF Head, Owned
        <4>5. Head(p)' = ~Owned(tail)
          BY <4>1, <4>2, <4>3 DEF Head, Owned
        <4>6. \A x \in ProcSet : InQ(x) => mypred[x] # mynode[p]
          BY <4>3 DEF Inv, PredOwned
        <4>7. Owned(tail) => \E r \in ProcSet : r # p /\ InQ(r) /\ tail = mynode[r]
          BY <4>3 DEF Inv, TailState
        <4>8. tail # mynode[p]
          <5>1. CASE Owned(tail)
            <6>1. PICK r \in ProcSet : r # p /\ InQ(r) /\ tail = mynode[r]
              BY <5>1, <4>7
            <6>2. Own(r) = mynode[r]
              BY <6>1 DEF InQ, Own
            <6> QED
              BY <6>1, <6>2, <4>3 DEF Inv, OwnInj
          <5>2. CASE ~Owned(tail)
            BY <5>2, <4>3 DEF Owned
          <5> QED
            BY <5>1, <5>2
        <4>9. ~goVal[p]
          BY DEF Inv, FlagState
        <4>10. OwnInj'
          BY <4>1 DEF Inv, OwnInj
        <4>11. OneHead'
          <5> SUFFICES ASSUME NEW x \in ProcSet, NEW y \in ProcSet, x # y,
                              Head(x)', Head(y)'
                       PROVE  FALSE
            BY DEF OneHead
          <5>1. CASE x # p /\ y # p
            BY <5>1, <4>4 DEF Inv, OneHead
          <5>2. CASE x = p
            BY <5>2, <4>4, <4>5 DEF Inv, TailState
          <5>3. CASE y = p
            BY <5>3, <4>4, <4>5 DEF Inv, TailState
          <5> QED
            BY <5>1, <5>2, <5>3
        <4>12. PredOwned'
          <5> SUFFICES ASSUME NEW x \in ProcSet, NEW q \in ProcSet,
                              InQ(x)', mypred'[x] = Own(q)'
                       PROVE  InQ(q)'
            BY DEF PredOwned
          <5>1. CASE q = p
            BY <5>1, <4>3
          <5>2. CASE q # p /\ x # p
            BY <5>2, <4>1, <4>2 DEF Inv, PredOwned
          <5>3. CASE q # p /\ x = p
            <6>1. Owned(tail)
              BY <5>3, <4>1, <4>2 DEF Owned
            <6>2. PICK r \in ProcSet : r # p /\ InQ(r) /\ tail = mynode[r]
              BY <6>1, <4>7
            <6>3. Own(r) = mynode[r]
              BY <6>2 DEF InQ, Own
            <6>4. q = r
              BY <5>3, <4>1, <4>2, <6>2, <6>3 DEF Inv, OwnInj
            <6> QED
              BY <5>3, <6>2, <6>4, <4>2
          <5> QED
            BY <5>1, <5>2, <5>3
        <4>13. PredInj'
          <5> SUFFICES ASSUME NEW x \in ProcSet, NEW y \in ProcSet, x # y,
                              InQ(x)', InQ(y)'
                       PROVE  mypred'[x] # mypred'[y]
            BY DEF PredInj
          <5>1. CASE x # p /\ y # p
            BY <5>1, <4>2 DEF Inv, PredInj
          <5>2. CASE x = p
            BY <5>2, <4>2 DEF Inv, PredNotTail
          <5>3. CASE y = p
            BY <5>3, <4>2 DEF Inv, PredNotTail
          <5> QED
            BY <5>1, <5>2, <5>3
        <4>14. CSHead'
          BY <4>2, <4>4 DEF Inv, CSHead
        <4>15. Handoff'
          <5> SUFFICES ASSUME NEW x \in ProcSet, NEW q \in ProcSet, Pred(q, x)'
                       PROVE  \/ pc'[x] = "T4" /\ mem'[mynode'[q]] = NIL
                              \/ pc'[x] = "T5" /\ mem'[mynode'[q]] = x
            BY DEF Handoff
          <5>1. InQ(q)' /\ InQ(x)' /\ mypred'[x] = mynode[q]
            BY DEF Pred
          <5>2. CASE x # p /\ q # p
            BY <5>1, <5>2, <4>2 DEF Inv, Handoff, Pred
          <5>3. CASE x # p /\ q = p
            BY <5>1, <5>3, <4>2, <4>6
          <5>4. CASE x = p /\ q = p
            BY <5>1, <5>4, <4>2, <4>8
          <5>5. CASE x = p /\ q # p
            <6>1. InQ(q) /\ tail = mynode[q]
              BY <5>1, <5>5, <4>2
            <6>2. ~\E y \in ProcSet : Pred(q, y)
              BY <6>1 DEF Inv, PredNotTail, Pred
            <6>3. pc[q] \in {"T2", "T3", "T4", "T5", "E1"}
              BY <6>1 DEF InQ
            <6>4. mem[mynode[q]] = NIL
              BY <6>2, <6>3 DEF Inv, NodeNil
            <6> QED
              BY <5>5, <6>4, <4>2
          <5> QED
            BY <5>2, <5>3, <5>4, <5>5
        <4>16. NodeNil'
          <5> SUFFICES ASSUME NEW q \in ProcSet,
                              pc'[q] \in {"T2", "T3", "T4", "T5", "E1"},
                              ~\E x \in ProcSet : Pred(q, x)'
                       PROVE  mem'[mynode'[q]] = NIL
            BY DEF NodeNil
          <5>1. CASE q = p
            BY <5>1, <4>3 DEF Inv, NodeNil, Pred
          <5>2. CASE q # p
            <6>1. ~\E x \in ProcSet : Pred(q, x)
              BY <5>2, <4>2, <4>3 DEF Pred
            <6> QED
              BY <5>2, <6>1, <4>2 DEF Inv, NodeNil
          <5> QED
            BY <5>1, <5>2
        <4>17. PredNotTail'
          BY <4>2, <4>3, <4>6, <4>8 DEF PredNotTail
        <4>18. TailState'
          <5>1. Owned(tail)'
            BY <4>1, <4>2, <4>3 DEF Owned
          <5>2. \E r \in ProcSet : InQ(r)' /\ tail' = mynode'[r]
            BY <4>2, <4>3
          <5> QED
            BY <5>1, <5>2 DEF TailState
        <4>19. FlagState' /\ Waker'
          BY <4>2, <4>4, <4>9 DEF Inv, FlagState, Waker
        <4> QED
          BY <4>10, <4>11, <4>12, <4>13, <4>14, <4>15, <4>16, <4>17, <4>18, <4>19
          DEF Inv
        
      <3>5. CASE T4(p)
        <4> USE <3>5 DEF T4
        <4>1. \A q \in ProcSet : Own(q)' = Own(q) /\ InQ(q)' = InQ(q)
          <5> SUFFICES ASSUME NEW q \in ProcSet
                       PROVE  Own(q)' = Own(q) /\ InQ(q)' = InQ(q)
            OBVIOUS
          <5>1. CASE q = p
            BY <5>1 DEF Own, InQ, TypeOK
          <5>2. CASE q # p
            BY <5>2, <2>1, OthersFrame
          <5> QED
            BY <5>1, <5>2
        <4>2. /\ pc'[p] = IF mem[mypred[p]] = NIL THEN "T5" ELSE "E1"
              /\ \A x \in ProcSet : x # p => pc'[x] = pc[x]
              /\ mem'[mypred[p]] = p
              /\ \A n \in Nodes : n # mypred[p] => mem'[n] = mem[n]
          BY DEF TypeOK
        <4>3. \A q, r \in ProcSet : Head(q)' = Head(q) /\ Pred(q, r)' = Pred(q, r)
          BY <4>1 DEF Head, Pred, Owned
        <4>4. ~goVal[p]
          BY DEF Inv, FlagState
        <4>5. \A q \in ProcSet : pc[q] \in {"T2", "T3", "T4", "T5", "E1"} /\ mynode[q] = mypred[p]
                                 => Pred(q, p)
          <5> SUFFICES ASSUME NEW q \in ProcSet,
                              pc[q] \in {"T2", "T3", "T4", "T5", "E1"},
                              mynode[q] = mypred[p]
                       PROVE  Pred(q, p)
            OBVIOUS
          <5>1. Own(q) = mynode[q] /\ InQ(p)
            BY DEF Own, InQ
          <5>2. InQ(q)
            BY <5>1 DEF Inv, PredOwned
          <5> QED
            BY <5>1, <5>2 DEF Pred
        <4>6. \A q \in ProcSet : Pred(q, p) => mem[mypred[p]] = NIL /\ pc'[p] = "T5"
          BY <4>2 DEF Inv, Handoff, Pred
        <4>7. ~Head(p) => \E q \in ProcSet : Pred(q, p)
          <5> SUFFICES ASSUME ~Head(p)
                       PROVE  \E q \in ProcSet : Pred(q, p)
            OBVIOUS
          <5>1. InQ(p)
            BY DEF InQ
          <5>2. PICK q \in ProcSet : Own(q) = mypred[p]
            BY <5>1 DEF Head, Owned
          <5>3. InQ(q)
            BY <5>1, <5>2 DEF Inv, PredOwned
          <5>4. Own(q) = mynode[q]
            BY <5>3 DEF InQ, Own
          <5> QED
            BY <5>1, <5>2, <5>3, <5>4 DEF Pred
        <4>8. OwnInj' /\ PredOwned' /\ PredInj' /\ PredNotTail'
          BY <4>1 DEF Inv, OwnInj, PredOwned, PredInj, PredNotTail
        <4>9. OneHead'
          BY <4>3 DEF Inv, OneHead
        <4>10. CSHead'
          <5> SUFFICES ASSUME NEW x \in ProcSet, pc'[x] = "E1"
                       PROVE  Head(x)'
            BY DEF CSHead
          <5>1. CASE x = p
            <6>1. Head(p)
              BY <5>1, <4>6, <4>7
            <6> QED
              BY <5>1, <6>1, <4>3
          <5>2. CASE x # p
            BY <5>2, <4>2, <4>3 DEF Inv, CSHead
          <5> QED
            BY <5>1, <5>2
        <4>11. Handoff'
          <5> SUFFICES ASSUME NEW x \in ProcSet, NEW q \in ProcSet, Pred(q, x)'
                       PROVE  \/ pc'[x] = "T4" /\ mem'[mynode'[q]] = NIL
                              \/ pc'[x] = "T5" /\ mem'[mynode'[q]] = x
            BY DEF Handoff
          <5>1. Pred(q, x)
            BY <4>3
          <5>2. CASE x = p
            <6>1. mynode[q] = mypred[p]
              BY <5>1, <5>2 DEF Pred
            <6> QED
              BY <5>1, <5>2, <6>1, <4>2, <4>6
          <5>3. CASE x # p
            <6>1. InQ(x) /\ InQ(p) /\ mypred[x] = mynode[q]
              BY <5>1 DEF Pred, InQ
            <6>2. mynode[q] # mypred[p]
              BY <5>3, <6>1 DEF Inv, PredInj
            <6> QED
              BY <5>1, <5>3, <6>2, <4>2 DEF Inv, Handoff, TypeOK
          <5> QED
            BY <5>2, <5>3
        <4>12. NodeNil'
          <5> SUFFICES ASSUME NEW q \in ProcSet,
                              pc'[q] \in {"T2", "T3", "T4", "T5", "E1"},
                              ~\E x \in ProcSet : Pred(q, x)'
                       PROVE  mem'[mynode'[q]] = NIL
            BY DEF NodeNil
          <5>1. pc[q] \in {"T2", "T3", "T4", "T5", "E1"}
            BY <4>2
          <5>2. ~\E x \in ProcSet : Pred(q, x)
            BY <4>3
          <5>3. mem[mynode[q]] = NIL
            BY <5>1, <5>2 DEF Inv, NodeNil
          <5>4. mynode[q] # mypred[p]
            BY <5>1, <5>2, <4>5
          <5> QED
            BY <5>3, <5>4, <4>2 DEF TypeOK
        <4>13. FlagState' /\ Waker'
          BY <4>2, <4>3, <4>4 DEF Inv, FlagState, Waker
        <4>14. TailState'
          BY <4>1, <4>3 DEF Inv, TailState, Owned
        <4> QED
          BY <4>8, <4>9, <4>10, <4>11, <4>12, <4>13, <4>14 DEF Inv

      <3>6. CASE T5(p)
        <4> USE <3>6 DEF T5
        <4>1. \A q \in ProcSet : Own(q)' = Own(q) /\ InQ(q)' = InQ(q)
          <5> SUFFICES ASSUME NEW q \in ProcSet
                       PROVE  Own(q)' = Own(q) /\ InQ(q)' = InQ(q)
            OBVIOUS
          <5>1. CASE q = p
            BY <5>1 DEF Own, InQ, TypeOK
          <5>2. CASE q # p
            BY <5>2, <2>1, OthersFrame
          <5> QED
            BY <5>1, <5>2
        <4>2. pc'[p] = "E1" /\ \A x \in ProcSet : x # p => pc'[x] = pc[x]
          BY DEF TypeOK
        <4>3. \A q, r \in ProcSet : Head(q)' = Head(q) /\ Pred(q, r)' = Pred(q, r)
          BY <4>1 DEF Head, Pred, Owned
        <4>4. Head(p) /\ \A r \in ProcSet : pc[r] = "E2" => nxtgo[r] # p
          BY DEF Inv, FlagState
        <4>5. \A q \in ProcSet : ~Pred(q, p)
          BY <4>4 DEF Head, Pred, Owned, Own, InQ
        <4>6. OwnInj' /\ PredOwned' /\ PredInj' /\ PredNotTail'
          BY <4>1 DEF Inv, OwnInj, PredOwned, PredInj, PredNotTail
        <4>7. OneHead' /\ CSHead'
          BY <4>2, <4>3, <4>4 DEF Inv, OneHead, CSHead
        <4>8. Handoff' /\ NodeNil'
          BY <4>2, <4>3, <4>5 DEF Inv, Handoff, NodeNil
        <4>9. FlagState' /\ Waker'
          BY <4>2, <4>3, <4>4 DEF Inv, FlagState, Waker
        <4>10. TailState'
          BY <4>1, <4>3 DEF Inv, TailState, Owned
        <4> QED
          BY <4>6, <4>7, <4>8, <4>9, <4>10 DEF Inv
      
      <3>7. CASE E1(p)
        <4> USE <3>7 DEF E1
        <4>1. Head(p)
          BY DEF Inv, CSHead
        <4>2. /\ pc'[p] = "E2"
              /\ \A x \in ProcSet : x # p => pc'[x] = pc[x] /\ nxtgo'[x] = nxtgo[x]
              /\ nxtgo'[p] = mem[mynode[p]]
              /\ \A n \in Nodes : n # mynode[p] => mem'[n] = mem[n]
          BY DEF TypeOK
        <4>3. \A q \in ProcSet : q # p => Own(q)' = Own(q) /\ InQ(q)' = InQ(q)
          BY <2>1, OthersFrame
        <4>4. /\ Own(p) = mynode[p] /\ Own(p)' = mypred[p]
              /\ InQ(p) /\ ~InQ(p)'
          BY <4>2 DEF Own, InQ
        <4>5. ~Owned(mypred[p])
          BY <4>1 DEF Head
        <4>6. \A q \in ProcSet : q # p => Own(q) # mypred[p] /\ Own(q) # mynode[p]
          BY <4>4, <4>5 DEF Inv, OwnInj, Owned
        <4>7. \A q \in ProcSet : q # p /\ InQ(q) =>
                /\ mypred[q] # mypred[p] /\ ~Head(q) /\ Own(q) = mynode[q]
          BY <4>1, <4>4 DEF Inv, PredInj, OneHead, InQ, Own
        <4>8. \A q \in ProcSet : Head(q)' <=> (q # p /\ Pred(p, q))
          <5> SUFFICES ASSUME NEW q \in ProcSet
                       PROVE  Head(q)' <=> (q # p /\ Pred(p, q))
            OBVIOUS
          <5>1. CASE q = p
            BY <5>1, <4>4 DEF Head
          <5>2. CASE q # p /\ ~InQ(q)
            BY <5>2, <4>3 DEF Head, Pred
          <5>3. CASE q # p /\ InQ(q)
            <6>1. Owned(mypred[q])
              BY <5>3, <4>7 DEF Head
            <6>2. Head(q)' <=> ~\E z \in ProcSet : Own(z)' = mypred[q]
              BY <5>3, <4>3 DEF Head, Owned
            <6>3. (\E z \in ProcSet : Own(z)' = mypred[q]) <=> mypred[q] # mynode[p]
              BY <6>1, <5>3, <4>3, <4>4, <4>6, <4>7 DEF Owned
            <6> QED
              BY <6>2, <6>3, <5>3, <4>4 DEF Pred
          <5> QED
            BY <5>1, <5>2, <5>3
        <4>9. \A q, r \in ProcSet : Pred(p, q) /\ Pred(p, r) => q = r
          BY DEF Inv, PredInj, Pred
        <4>10. \A q \in ProcSet : Pred(p, q) => q # p
          BY <4>4, <4>5 DEF Pred, Owned
        <4>11. \/ nxtgo'[p] = NIL
               \/ \E s \in ProcSet : Pred(p, s) /\ pc[s] = "T5" /\ nxtgo'[p] = s
          <5>1. CASE \E s \in ProcSet : Pred(p, s)
            BY <5>1, <4>2 DEF Inv, Handoff
          <5>2. CASE ~\E s \in ProcSet : Pred(p, s)
            BY <5>2, <4>2 DEF Inv, NodeNil
          <5> QED
            BY <5>1, <5>2
        <4>12. \A r \in ProcSet : r # p /\ pc[r] = "E2" => nxtgo[r] = NIL
          BY <4>1 DEF Inv, Waker, OneHead
        <4>13. OwnInj'
          BY <4>3, <4>4, <4>6 DEF Inv, OwnInj
        <4>14. OneHead'
          BY <4>8, <4>9 DEF OneHead
        <4>15. PredOwned'
          BY <4>3, <4>4, <4>7 DEF Inv, PredOwned
        <4>16. PredInj' /\ PredNotTail'
          BY <4>3, <4>4 DEF Inv, PredInj, PredNotTail
        <4>17. CSHead'
          BY <4>2, <4>7 DEF Inv, CSHead, InQ
        <4>18. Handoff'
          <5> SUFFICES ASSUME NEW x \in ProcSet, NEW q \in ProcSet, Pred(q, x)'
                       PROVE  \/ pc'[x] = "T4" /\ mem'[mynode'[q]] = NIL
                              \/ pc'[x] = "T5" /\ mem'[mynode'[q]] = x
            BY DEF Handoff
          <5>1. x # p /\ q # p /\ Pred(q, x)
            BY <4>3, <4>4 DEF Pred
          <5>2. mynode[q] # mynode[p]
            BY <5>1, <4>6, <4>7 DEF Pred
          <5> QED
            BY <5>1, <5>2, <4>2 DEF Inv, Handoff, TypeOK
        <4>19. NodeNil'
          <5> SUFFICES ASSUME NEW q \in ProcSet,
                              pc'[q] \in {"T2", "T3", "T4", "T5", "E1"},
                              ~\E x \in ProcSet : Pred(q, x)'
                       PROVE  mem'[mynode'[q]] = NIL
            BY DEF NodeNil
          <5>1. q # p /\ pc[q] \in {"T2", "T3", "T4", "T5", "E1"}
            BY <4>2
          <5>2. Own(q) = mynode[q]
            BY <5>1 DEF Own
          <5>3. ~\E x \in ProcSet : Pred(q, x)
            BY <5>1, <5>2, <4>3, <4>6 DEF Pred
          <5>4. mynode[q] # mynode[p]
            BY <5>1, <5>2, <4>6
          <5> QED
            BY <5>1, <5>3, <5>4, <4>2 DEF Inv, NodeNil, TypeOK
        <4>20. FlagState'
          BY <4>2, <4>7 DEF Inv, FlagState, InQ
        <4>21. Waker'
          <5>1. \A r \in ProcSet : pc'[r] = "E2" /\ nxtgo'[r] # NIL => r = p
            BY <4>2, <4>12
          <5>2. CASE nxtgo'[p] = NIL
            BY <5>1, <5>2 DEF Waker
          <5>3. CASE nxtgo'[p] # NIL
            <6>1. PICK s \in ProcSet : Pred(p, s) /\ pc[s] = "T5" /\ nxtgo'[p] = s
              BY <5>3, <4>11
            <6>2. Head(s)' /\ pc'[s] = "T5"
              BY <6>1, <4>2, <4>8, <4>10
            <6>3. \A z \in ProcSet : pc'[z] = "E2" /\ nxtgo'[z] = s => z = p
              BY <6>1, <4>2, <4>12, ConstAssump
            <6> QED
              BY <5>1, <6>1, <6>2, <6>3 DEF Waker
          <5> QED
            BY <5>2, <5>3
        <4>22. TailState'
          <5>1. tail # mypred[p]
            BY <4>4 DEF Inv, PredNotTail
          <5>2. CASE tail = mynode[p]
            <6>1. ~Owned(tail)'
              BY <5>1, <5>2, <4>3, <4>4, <4>6 DEF Owned
            <6>2. \A q \in ProcSet : ~Pred(p, q)
              BY <5>2 DEF Inv, PredNotTail, Pred
            <6>3. \A q \in ProcSet : ~Head(q)'
              BY <6>2, <4>8
            <6> QED
              BY <6>1, <6>3 DEF TailState
          <5>3. CASE tail # mynode[p]
            <6>1. PICK r \in ProcSet : InQ(r) /\ tail = mynode[r]
              BY <4>1 DEF Inv, TailState
            <6>2. r # p
              BY <6>1, <5>3
            <6>3. Owned(tail)'
              BY <6>1, <6>2, <4>3, <4>7 DEF Owned
            <6>4. InQ(r)'
              BY <6>1, <6>2, <4>3
            <6> QED
              BY <6>1, <6>3, <6>4 DEF TailState
          <5> QED
            BY <5>2, <5>3
        <4> QED
          BY <4>13, <4>14, <4>15, <4>16, <4>17, <4>18, <4>19, <4>20, <4>21, <4>22
          DEF Inv
      
      <3>8. CASE E2(p)
        <4> USE <3>8 DEF E2
        <4>1. \A q \in ProcSet : Own(q)' = Own(q) /\ InQ(q)' = InQ(q)
          <5> SUFFICES ASSUME NEW q \in ProcSet
                       PROVE  Own(q)' = Own(q) /\ InQ(q)' = InQ(q)
            OBVIOUS
          <5>1. CASE q = p
            BY <5>1 DEF Own, InQ, TypeOK
          <5>2. CASE q # p
            BY <5>2, <2>1, OthersFrame
          <5> QED
            BY <5>1, <5>2
        <4>2. pc'[p] = "E3" /\ \A x \in ProcSet : x # p => pc'[x] = pc[x]
          BY DEF TypeOK
        <4>3. ~InQ(p) /\ \A q \in ProcSet : ~Pred(q, p) /\ ~Pred(p, q)
          BY DEF InQ, Pred
        <4>4. \A q, r \in ProcSet : Head(q)' = Head(q) /\ Pred(q, r)' = Pred(q, r)
          BY <4>1 DEF Head, Pred, Owned
        <4>5. OwnInj' /\ PredOwned' /\ PredInj' /\ PredNotTail'
          BY <4>1 DEF Inv, OwnInj, PredOwned, PredInj, PredNotTail
        <4>6. OneHead' /\ CSHead'
          BY <4>2, <4>4 DEF Inv, OneHead, CSHead
        <4>7. Handoff' /\ NodeNil'
          BY <4>2, <4>3, <4>4 DEF Inv, Handoff, NodeNil
        <4>8. Waker'
          BY <4>2, <4>4 DEF Inv, Waker
        <4>9. FlagState'
          <5> SUFFICES ASSUME NEW x \in ProcSet, goVal'[x],
                              pc'[x] \in {"T3", "T4", "T5"}
                       PROVE  /\ pc'[x] = "T5" /\ Head(x)'
                              /\ \A r \in ProcSet : pc'[r] = "E2" => nxtgo'[r] # x
            BY DEF FlagState
          <5>1. x # p /\ pc'[x] = pc[x]
            BY <4>2
          <5>2. CASE goVal[x]
            BY <5>1, <5>2, <4>2, <4>4 DEF Inv, FlagState
          <5>3. CASE ~goVal[x]
            <6>1. nxtgo[p] # NIL /\ x = nxtgo[p]
              BY <5>3 DEF TypeOK
            <6>2. /\ Head(x) /\ pc[x] = "T5"
                  /\ \A s \in ProcSet : pc[s] = "E2" /\ nxtgo[s] = x => s = p
              BY <6>1 DEF Inv, Waker
            <6> QED
              BY <5>1, <6>2, <4>2, <4>4
          <5> QED
            BY <5>2, <5>3
        <4>10. TailState'
          BY <4>1, <4>4 DEF Inv, TailState, Owned
        <4> QED
          BY <4>5, <4>6, <4>7, <4>8, <4>9, <4>10 DEF Inv
      
      <3>9. CASE E3(p)
        <4> USE <3>9 DEF E3
        <4>1. \A q \in ProcSet : Own(q)' = Own(q) /\ InQ(q)' = InQ(q)
          <5> SUFFICES ASSUME NEW q \in ProcSet
                       PROVE  Own(q)' = Own(q) /\ InQ(q)' = InQ(q)
            OBVIOUS
          <5>1. CASE q = p
            BY <5>1 DEF Own, InQ, TypeOK
          <5>2. CASE q # p
            BY <5>2, <2>1, OthersFrame
          <5> QED
            BY <5>1, <5>2
        <4>2. /\ pc'[p] = "RM"
              /\ \A x \in ProcSet : x # p => pc'[x] = pc[x] /\ mynode'[x] = mynode[x]
          BY DEF TypeOK
        <4>3. ~InQ(p) /\ \A q \in ProcSet : ~Pred(q, p) /\ ~Pred(p, q)
          BY DEF InQ, Pred
        <4>4. \A q, r \in ProcSet : Head(q)' = Head(q) /\ Pred(q, r)' = Pred(q, r)
          BY <4>1, <4>2, <4>3 DEF Head, Pred, Owned
        <4>5. OwnInj' /\ PredOwned' /\ PredInj' /\ PredNotTail'
          BY <4>1 DEF Inv, OwnInj, PredOwned, PredInj, PredNotTail
        <4>6. OneHead' /\ CSHead'
          BY <4>2, <4>4 DEF Inv, OneHead, CSHead
        <4>7. Handoff' /\ NodeNil'
          BY <4>2, <4>3, <4>4 DEF Inv, Handoff, NodeNil
        <4>8. FlagState' /\ Waker'
          BY <4>2, <4>4 DEF Inv, FlagState, Waker
        <4>9. TailState'
          BY <4>1, <4>2, <4>3, <4>4 DEF Inv, TailState, Owned
        <4> QED
          BY <4>5, <4>6, <4>7, <4>8, <4>9 DEF Inv
      <3> QED
        BY <2>1, <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9 DEF LineActs
    <2>2. CASE UNCHANGED vars
      BY <2>2 DEF vars, Inv, OwnInj, OneHead, PredOwned, PredInj, CSHead, Handoff,
           NodeNil, FlagState, Waker, PredNotTail, TailState,
                  InQ, Own, Owned, Head, Pred
    <2> QED
      BY <2>1, <2>2 DEF Next, LineActs
  <1> QED
    BY <1>1, <1>2, PTL, SpecTypeOK DEF Spec


LEMMA InvImpliesMutex == Inv => Mutex
  <1> SUFFICES ASSUME Inv,
                      NEW p \in ProcSet, NEW q \in ProcSet,
                      pc[p] = "E1", pc[q] = "E1"
               PROVE  p = q
    BY DEF Mutex
  <1>1. Head(p) /\ Head(q)
    BY DEF Inv, CSHead
  <1> QED
    BY <1>1 DEF Inv, OneHead

THEOREM MutualExclusion == Spec => []Mutex
  <1> SUFFICES Spec => []Inv
    BY PTL, InvImpliesMutex
  <1> QED
    BY SpecInv

=============================================================================
