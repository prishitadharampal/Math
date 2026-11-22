--------------------------- MODULE MCSLiveness ---------------------------

EXTENDS MCS_Proofs, NaturalsInduction, TLAPS

VARIABLES ticket, nxtTicket, serving, ahead, rmrCC, rmrDSM, goCached

ghostvars == <<ticket, nxtTicket, serving, ahead, rmrCC, rmrDSM, goCached>>
varsA == <<vars, ghostvars>>


ATry(p) ==
  /\ Try(p)
  /\ ahead'  = [ahead EXCEPT ![p] = {q \in ProcSet : pc[q] \in {"T4", "T5"}}]
  /\ rmrCC'  = [rmrCC EXCEPT ![p] = 0]
  /\ rmrDSM' = [rmrDSM EXCEPT ![p] = 0]
  /\ UNCHANGED <<ticket, nxtTicket, serving, goCached>>

AT1(p) ==
  /\ T1(p)
  /\ rmrCC'  = [rmrCC EXCEPT ![p] = @ + 1]
  /\ rmrDSM' = [rmrDSM EXCEPT ![p] = @ + 1]
  /\ UNCHANGED <<ticket, nxtTicket, serving, ahead, goCached>>

AT2(p) ==
  /\ T2(p)
  /\ rmrCC'    = [rmrCC EXCEPT ![p] = @ + 1]
  /\ goCached' = [goCached EXCEPT ![p] = FALSE]
  /\ UNCHANGED <<ticket, nxtTicket, serving, ahead, rmrDSM>>

AT3(p) ==
  /\ T3(p)
  /\ ticket'    = [ticket EXCEPT ![p] = nxtTicket]
  /\ nxtTicket' = nxtTicket + 1
  /\ rmrCC'     = [rmrCC EXCEPT ![p] = @ + 1]
  /\ rmrDSM'    = [rmrDSM EXCEPT ![p] = @ + 1]
  /\ UNCHANGED <<serving, ahead, goCached>>

AT4(p) ==
  /\ T4(p)
  /\ ahead'  = IF mem[mypred[p]] = NIL                 \* p goes to T5
               THEN ahead
               ELSE [q \in ProcSet |-> ahead[q] \ {p}] \* p goes to E1
  /\ rmrCC'  = [rmrCC EXCEPT ![p] = @ + 1]
  /\ rmrDSM' = [rmrDSM EXCEPT ![p] = @ + 1]
  /\ UNCHANGED <<ticket, nxtTicket, serving, goCached>>

AT5(p) ==
  /\ T5(p)
  /\ ahead'    = [q \in ProcSet |-> ahead[q] \ {p}]
  /\ rmrCC'    = [rmrCC EXCEPT ![p] = IF goCached[p] THEN @ ELSE @ + 1]
  /\ goCached' = [goCached EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<ticket, nxtTicket, serving, rmrDSM>>

AT5Fail(p) ==
  /\ pc[p] = "T5"
  /\ ~goVal[p]
  /\ rmrCC'    = [rmrCC EXCEPT ![p] = IF goCached[p] THEN @ ELSE @ + 1]
  /\ goCached' = [goCached EXCEPT ![p] = TRUE]
  /\ UNCHANGED vars
  /\ UNCHANGED <<ticket, nxtTicket, serving, ahead, rmrDSM>>

AE1(p) ==
  /\ E1(p)
  /\ serving' = serving + 1
  /\ rmrCC'   = [rmrCC EXCEPT ![p] = @ + 1]
  /\ rmrDSM'  = [rmrDSM EXCEPT ![p] = @ + 1]
  /\ UNCHANGED <<ticket, nxtTicket, ahead, goCached>>

AE2(p) ==
  /\ E2(p)
  /\ rmrCC'    = IF nxtgo[p] # NIL THEN [rmrCC EXCEPT ![p] = @ + 1] ELSE rmrCC
  /\ rmrDSM'   = IF nxtgo[p] # NIL THEN [rmrDSM EXCEPT ![p] = @ + 1] ELSE rmrDSM
  /\ goCached' = IF nxtgo[p] # NIL THEN [goCached EXCEPT ![nxtgo[p]] = FALSE]
                                   ELSE goCached
  /\ UNCHANGED <<ticket, nxtTicket, serving, ahead>>

AE3(p) ==
  /\ E3(p)
  /\ UNCHANGED ghostvars

ALineActs(p) == {ATry(p), AT1(p), AT2(p), AT3(p), AT4(p), AT5(p), AT5Fail(p),
                 AE1(p), AE2(p), AE3(p)}

AInit ==
  /\ Init
  /\ ticket    = [p \in ProcSet |-> 0]
  /\ nxtTicket = 0
  /\ serving   = 0
  /\ ahead     = [p \in ProcSet |-> {}]
  /\ rmrCC     = [p \in ProcSet |-> 0]
  /\ rmrDSM    = [p \in ProcSet |-> 0]
  /\ goCached  = [p \in ProcSet |-> FALSE]

ANext == \E p \in ProcSet : \E LineAct \in ALineActs(p) : LineAct

ASpec == AInit /\ [][ANext]_varsA

(* if A stays enabled from now on, it eventually happens.  For one action, [](FairAt(A)) is equivalent to Fair(A), and PTL proves this  *)

FairAt(A) == [](ENABLED <<A>>_vars) => <><<A>>_vars

FairProc(p) == /\ FairAt(AT1(p)) /\ FairAt(AT2(p)) /\ FairAt(AT3(p))
               /\ FairAt(AT4(p)) /\ FairAt(AT5(p)) /\ FairAt(AE1(p))
               /\ FairAt(AE2(p)) /\ FairAt(AE3(p))

AllFair == \A p \in ProcSet : FairProc(p)

AFairness == [](AllFair)

AFairSpec == ASpec /\ AFairness

THEOREM ASpecImpliesSpec == ASpec => Spec
  <1>1. AInit => Init
    BY DEF AInit
  <1>2. [ANext]_varsA => [Next]_vars
    <2> SUFFICES ASSUME [ANext]_varsA
                 PROVE  [Next]_vars
      OBVIOUS
    <2>1. ASSUME NEW p \in ProcSet,
                 NEW LineAct \in ALineActs(p),
                 LineAct
          PROVE  [Next]_vars
      <3>1. CASE ATry(p)
        BY <3>1 DEF ATry, Next
      <3>2. CASE AT1(p)
        BY <3>2 DEF AT1, Next
      <3>3. CASE AT2(p)
        BY <3>3 DEF AT2, Next
      <3>4. CASE AT3(p)
        BY <3>4 DEF AT3, Next
      <3>5. CASE AT4(p)
        BY <3>5 DEF AT4, Next
      <3>6. CASE AT5(p)
        BY <3>6 DEF AT5, Next
      <3>7. CASE AT5Fail(p)
        BY <3>7 DEF AT5Fail
      <3>8. CASE AE1(p)
        BY <3>8 DEF AE1, Next
      <3>9. CASE AE2(p)
        BY <3>9 DEF AE2, Next
      <3>10. CASE AE3(p)
        BY <3>10 DEF AE3, Next
      <3> QED
        BY <2>1, <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9, <3>10
        DEF ALineActs
    <2>2. CASE UNCHANGED varsA
      BY <2>2 DEF varsA
    <2> QED
      BY <2>1, <2>2 DEF ANext
  <1> QED
    BY <1>1, <1>2, PTL DEF ASpec, Spec

ATypeOK ==
  /\ TypeOK
  /\ ticket    \in [ProcSet -> Nat]
  /\ nxtTicket \in Nat
  /\ serving   \in Nat
  /\ ahead     \in [ProcSet -> SUBSET ProcSet]
  /\ rmrCC     \in [ProcSet -> Nat]
  /\ rmrDSM    \in [ProcSet -> Nat]
  /\ goCached  \in [ProcSet -> BOOLEAN]

LEMMA ASpecTypeOK == ASpec => []ATypeOK
  <1>1. AInit => ATypeOK
    <2> SUFFICES ASSUME AInit
                 PROVE  ATypeOK
      OBVIOUS
    <2> QED
      BY ConstAssump DEF AInit, Init, ATypeOK, TypeOK, Nodes, MemVals, Lines
  <1>2. ATypeOK /\ [ANext]_varsA => ATypeOK'
    <2> SUFFICES ASSUME ATypeOK /\ [ANext]_varsA
                 PROVE  ATypeOK'
      OBVIOUS
    <2> USE DEF ATypeOK, TypeOK
    <2>1. ASSUME NEW p \in ProcSet,
                 NEW LineAct \in ALineActs(p),
                 LineAct
          PROVE  ATypeOK'
      <3>1. CASE ATry(p)
        <4> USE <3>1 DEF ATry, Try
        <4> QED
          BY DEF Lines
      <3>2. CASE AT1(p)
        <4> USE <3>2 DEF AT1, T1
        <4> QED
          BY DEF Nodes, MemVals, Lines
      <3>3. CASE AT2(p)
        <4> USE <3>3 DEF AT2, T2
        <4> QED
          BY DEF Lines
      <3>4. CASE AT3(p)
        <4> USE <3>4 DEF AT3, T3
        <4> QED
          BY DEF Nodes, Lines
      <3>5. CASE AT4(p)
        <4> USE <3>5 DEF AT4, T4
        <4> QED
          BY DEF Nodes, MemVals, Lines
      <3>6. CASE AT5(p)
        <4> USE <3>6 DEF AT5, T5
        <4> QED
          BY DEF Lines
      <3>7. CASE AT5Fail(p)
        <4> USE <3>7 DEF AT5Fail
        <4> QED
          BY DEF vars
      <3>8. CASE AE1(p)
        <4> USE <3>8 DEF AE1, E1
        <4> QED
          BY DEF Nodes, MemVals, Lines
      <3>9. CASE AE2(p)
        <4> USE <3>9 DEF AE2, E2
        <4> QED
          BY DEF Lines
      <3>10. CASE AE3(p)
        <4> USE <3>10 DEF AE3, E3
        <4> QED
          BY DEF Nodes, Lines, ghostvars
      <3> QED
        BY <2>1, <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9, <3>10
        DEF ALineActs
    <2>2. CASE UNCHANGED varsA
      BY <2>2 DEF varsA, vars, ghostvars
    <2> QED
      BY <2>1, <2>2 DEF ANext
  <1> QED
    BY <1>1, <1>2, PTL DEF ASpec

TicketRange    == /\ serving <= nxtTicket
                  /\ \A q \in ProcSet : InQ(q) => serving <= ticket[q] /\ ticket[q] < nxtTicket
TicketInj      == \A q, r \in ProcSet : q # r /\ InQ(q) /\ InQ(r) => ticket[q] # ticket[r]
TicketFull     == \A k \in Nat : serving <= k /\ k < nxtTicket =>
                    \E q \in ProcSet : InQ(q) /\ ticket[q] = k
PredTicket     == \A q, r \in ProcSet : Pred(q, r) => ticket[r] = ticket[q] + 1
HeadTicket     == \A q \in ProcSet : Head(q) => ticket[q] = serving
TailTicket     == \A r \in ProcSet : InQ(r) /\ tail = mynode[r] => ticket[r] + 1 = nxtTicket
EmptyServing   == ~Owned(tail) => serving = nxtTicket
WakeHead       == \A q \in ProcSet : Head(q) /\ pc[q] = "T5" =>
                    \/ goVal[q]
                    \/ \E r \in ProcSet : pc[r] = "E2" /\ nxtgo[r] = q
HeadNotNil     == \A q \in ProcSet : Head(q) /\ pc[q] = "T4" => mem[mypred[q]] # NIL
FreeTailNotNil == ~Owned(tail) => mem[tail] # NIL

LiveInv == /\ TicketRange /\ TicketInj /\ TicketFull /\ PredTicket /\ HeadTicket
           /\ TailTicket /\ EmptyServing /\ WakeHead /\ HeadNotNil /\ FreeTailNotNil

LEMMA ASpecLiveInv == ASpec => []LiveInv
  <1>1. AInit => LiveInv
    <2> SUFFICES ASSUME AInit
                 PROVE  LiveInv
      OBVIOUS
    <2>1. \A q \in ProcSet : ~InQ(q) /\ ~Head(q) /\ Own(q) = q
      BY DEF AInit, Init, InQ, Head, Own
    <2>2. ~Owned(tail)
      BY <2>1, ConstAssump DEF AInit, Init, Owned
    <2> QED
      BY <2>1, <2>2, ConstAssump DEF AInit, Init, LiveInv, TicketRange, TicketInj, TicketFull, PredTicket, HeadTicket,
               TailTicket, EmptyServing, WakeHead, HeadNotNil, FreeTailNotNil, Pred
  <1>2. LiveInv /\ Inv /\ ATypeOK /\ [ANext]_varsA => LiveInv'
    <2> SUFFICES ASSUME LiveInv, Inv, ATypeOK, [ANext]_varsA
                 PROVE  LiveInv'
      OBVIOUS
    <2>1. ASSUME NEW p \in ProcSet,
                 NEW LineAct \in ALineActs(p),
                 LineAct
          PROVE  LiveInv'
      <3>1. CASE ATry(p)
        <4> USE <3>1 DEF ATry, Try
        <4>1. \A q \in ProcSet : Own(q)' = Own(q) /\ InQ(q)' = InQ(q)
          <5> SUFFICES ASSUME NEW q \in ProcSet
                       PROVE  Own(q)' = Own(q) /\ InQ(q)' = InQ(q)
            OBVIOUS
          <5>1. CASE q = p
            BY <5>1 DEF Own, InQ, ATypeOK, TypeOK
          <5>2. CASE q # p
            BY <5>2 DEF Own, InQ, ATypeOK, TypeOK
          <5> QED
            BY <5>1, <5>2
        <4>2. pc'[p] = "T1" /\ \A x \in ProcSet : x # p => pc'[x] = pc[x]
          BY DEF ATypeOK, TypeOK
        <4>3. \A q, r \in ProcSet : Head(q)' = Head(q) /\ Pred(q, r)' = Pred(q, r)
          BY <4>1 DEF Head, Pred, Owned
        <4>4. TicketRange' /\ TicketInj' /\ TicketFull'
          BY <4>1 DEF LiveInv, TicketRange, TicketInj, TicketFull
        <4>5. PredTicket' /\ HeadTicket' /\ TailTicket' /\ EmptyServing'
          BY <4>1, <4>3 DEF LiveInv, PredTicket, HeadTicket, TailTicket, EmptyServing, Owned
        <4>6. WakeHead' /\ HeadNotNil' /\ FreeTailNotNil'
          BY <4>1, <4>2, <4>3 DEF LiveInv, WakeHead, HeadNotNil, FreeTailNotNil, Owned
        <4> QED
          BY <4>4, <4>5, <4>6 DEF LiveInv
      <3>2. CASE AT1(p)
        <4> USE <3>2 DEF AT1, T1
        <4>1. \A q \in ProcSet : Own(q)' = Own(q) /\ InQ(q)' = InQ(q)
          <5> SUFFICES ASSUME NEW q \in ProcSet
                       PROVE  Own(q)' = Own(q) /\ InQ(q)' = InQ(q)
            OBVIOUS
          <5>1. CASE q = p
            BY <5>1 DEF Own, InQ, ATypeOK, TypeOK
          <5>2. CASE q # p
            BY <5>2 DEF Own, InQ, ATypeOK, TypeOK
          <5> QED
            BY <5>1, <5>2
        <4>2. /\ pc'[p] = "T2" /\ \A x \in ProcSet : x # p => pc'[x] = pc[x]
              /\ \A n \in Nodes : n # mynode[p] => mem'[n] = mem[n]
          BY DEF ATypeOK, TypeOK
        <4>3. \A q, r \in ProcSet : Head(q)' = Head(q) /\ Pred(q, r)' = Pred(q, r)
          BY <4>1 DEF Head, Pred, Owned
        <4>4. Own(p) = mynode[p]
          BY DEF Own
        <4>5. \A q \in ProcSet : Head(q) => mypred[q] # mynode[p]
          BY <4>4 DEF Head, Owned
        <4>6. ~Owned(tail) => tail # mynode[p]
          BY <4>4 DEF Owned
        <4>7. TicketRange' /\ TicketInj' /\ TicketFull'
          BY <4>1 DEF LiveInv, TicketRange, TicketInj, TicketFull
        <4>8. PredTicket' /\ HeadTicket' /\ TailTicket' /\ EmptyServing'
          BY <4>1, <4>3 DEF LiveInv, PredTicket, HeadTicket, TailTicket, EmptyServing, Owned
        <4>9. WakeHead'
          BY <4>2, <4>3 DEF LiveInv, WakeHead
        <4>10. HeadNotNil'
          BY <4>2, <4>3, <4>5 DEF LiveInv, HeadNotNil, ATypeOK, TypeOK
        <4>11. FreeTailNotNil'
          BY <4>1, <4>2, <4>6 DEF LiveInv, FreeTailNotNil, Owned, ATypeOK, TypeOK
        <4> QED
          BY <4>7, <4>8, <4>9, <4>10, <4>11 DEF LiveInv
      <3>3. CASE AT2(p)
        <4> USE <3>3 DEF AT2, T2
        <4>1. \A q \in ProcSet : Own(q)' = Own(q) /\ InQ(q)' = InQ(q)
          <5> SUFFICES ASSUME NEW q \in ProcSet
                       PROVE  Own(q)' = Own(q) /\ InQ(q)' = InQ(q)
            OBVIOUS
          <5>1. CASE q = p
            BY <5>1 DEF Own, InQ, ATypeOK, TypeOK
          <5>2. CASE q # p
            BY <5>2 DEF Own, InQ, ATypeOK, TypeOK
          <5> QED
            BY <5>1, <5>2
        <4>2. /\ pc'[p] = "T3"
              /\ \A x \in ProcSet : x # p => pc'[x] = pc[x] /\ goVal'[x] = goVal[x]
          BY DEF ATypeOK, TypeOK
        <4>3. \A q, r \in ProcSet : Head(q)' = Head(q) /\ Pred(q, r)' = Pred(q, r)
          BY <4>1 DEF Head, Pred, Owned
        <4>4. TicketRange' /\ TicketInj' /\ TicketFull'
          BY <4>1 DEF LiveInv, TicketRange, TicketInj, TicketFull
        <4>5. PredTicket' /\ HeadTicket' /\ TailTicket' /\ EmptyServing'
          BY <4>1, <4>3 DEF LiveInv, PredTicket, HeadTicket, TailTicket, EmptyServing, Owned
        <4>6. WakeHead' /\ HeadNotNil' /\ FreeTailNotNil'
          BY <4>1, <4>2, <4>3 DEF LiveInv, WakeHead, HeadNotNil, FreeTailNotNil, Owned
        <4> QED
          BY <4>4, <4>5, <4>6 DEF LiveInv
      <3>4. CASE AT3(p)
        <4> USE <3>4 DEF AT3, T3
        <4>1. \A q \in ProcSet : Own(q)' = Own(q)
          BY DEF Own, ATypeOK, TypeOK
        <4>2. /\ pc'[p] = "T4" /\ mypred'[p] = tail /\ tail' = mynode[p]
              /\ ticket'[p] = nxtTicket /\ nxtTicket' = nxtTicket + 1
              /\ \A x \in ProcSet : x # p => /\ pc'[x] = pc[x]
                                              /\ mypred'[x] = mypred[x]
                                              /\ ticket'[x] = ticket[x]
                                              /\ InQ(x)' = InQ(x)
          BY DEF ATypeOK, TypeOK, InQ
        <4>3. ~InQ(p) /\ InQ(p)' /\ Own(p) = mynode[p]
          BY <4>2 DEF InQ, Own
        <4>4. \A x \in ProcSet : x # p => Head(x)' = Head(x)
          BY <4>1, <4>2 DEF Head, Owned
        <4>5. Head(p)' = ~Owned(tail)
          BY <4>1, <4>2, <4>3 DEF Head, Owned
        <4>6. \A x \in ProcSet : InQ(x) => mypred[x] # mynode[p]
          BY <4>3 DEF Inv, PredOwned
        <4>7. tail # mynode[p]
          <5>1. CASE Owned(tail)
            <6>1. PICK r \in ProcSet : InQ(r) /\ tail = mynode[r]
              BY <5>1 DEF Inv, TailState
            <6>2. r # p /\ Own(r) = mynode[r]
              BY <6>1, <4>3 DEF InQ, Own
            <6> QED
              BY <6>1, <6>2, <4>3 DEF Inv, OwnInj
          <5>2. CASE ~Owned(tail)
            BY <5>2, <4>3 DEF Owned
          <5> QED
            BY <5>1, <5>2
        <4>8. \A q, x \in ProcSet :
                Pred(q, x)' <=> \/ q # p /\ x # p /\ Pred(q, x)
                                \/ q # p /\ x = p /\ InQ(q) /\ tail = mynode[q]
          BY <4>2, <4>3, <4>6, <4>7 DEF Pred
        <4>9. TicketRange'
          BY <4>2, <4>3 DEF LiveInv, TicketRange, ATypeOK
        <4>10. TicketInj'
          BY <4>2, <4>3 DEF LiveInv, TicketRange, TicketInj, ATypeOK
        <4>11. TicketFull'
          <5> SUFFICES ASSUME NEW k \in Nat, serving' <= k, k < nxtTicket'
                       PROVE  \E q \in ProcSet : InQ(q)' /\ ticket'[q] = k
            BY DEF TicketFull
          <5>1. CASE k < nxtTicket
            <6>1. PICK q \in ProcSet : InQ(q) /\ ticket[q] = k
              BY <5>1 DEF LiveInv, TicketFull
            <6> QED
              BY <6>1, <4>2, <4>3
          <5>2. CASE k = nxtTicket
            BY <5>2, <4>2, <4>3
          <5> QED
            BY <5>1, <5>2, <4>2 DEF ATypeOK
        <4>12. PredTicket'
          <5> SUFFICES ASSUME NEW q \in ProcSet, NEW x \in ProcSet, Pred(q, x)'
                       PROVE  ticket'[x] = ticket'[q] + 1
            BY DEF PredTicket
          <5>1. CASE x # p
            BY <5>1, <4>2, <4>8 DEF LiveInv, PredTicket
          <5>2. CASE x = p
            BY <5>2, <4>2, <4>8 DEF LiveInv, TailTicket
          <5> QED
            BY <5>1, <5>2
        <4>13. HeadTicket'
          BY <4>2, <4>4, <4>5 DEF LiveInv, HeadTicket, EmptyServing
        <4>14. TailTicket'
          <5> SUFFICES ASSUME NEW r \in ProcSet, InQ(r)', tail' = mynode'[r]
                       PROVE  ticket'[r] + 1 = nxtTicket'
            BY DEF TailTicket
          <5>1. r = p
            <6>1. CASE r # p
              <7>1. InQ(r) /\ Own(r) = mynode[r]
                BY <6>1, <4>2 DEF InQ, Own
              <7> QED
                BY <6>1, <7>1, <4>2, <4>3 DEF Inv, OwnInj
            <6> QED
              BY <6>1
          <5> QED
            BY <5>1, <4>2
        <4>15. EmptyServing' /\ FreeTailNotNil'
          <5>1. Owned(tail)'
            BY <4>1, <4>2, <4>3 DEF Owned
          <5> QED
            BY <5>1 DEF EmptyServing, FreeTailNotNil
        <4>16. WakeHead'
          BY <4>2, <4>4 DEF LiveInv, WakeHead
        <4>17. HeadNotNil'
          BY <4>2, <4>4, <4>5 DEF LiveInv, HeadNotNil, FreeTailNotNil
        <4> QED
          BY <4>9, <4>10, <4>11, <4>12, <4>13, <4>14, <4>15, <4>16, <4>17 DEF LiveInv
      <3>5. CASE AT4(p)
        <4> USE <3>5 DEF AT4, T4
        <4>1. \A q \in ProcSet : Own(q)' = Own(q) /\ InQ(q)' = InQ(q)
          <5> SUFFICES ASSUME NEW q \in ProcSet
                       PROVE  Own(q)' = Own(q) /\ InQ(q)' = InQ(q)
            OBVIOUS
          <5>1. CASE q = p
            BY <5>1 DEF Own, InQ, ATypeOK, TypeOK
          <5>2. CASE q # p
            BY <5>2 DEF Own, InQ, ATypeOK, TypeOK
          <5> QED
            BY <5>1, <5>2
        <4>2. /\ pc'[p] = IF mem[mypred[p]] = NIL THEN "T5" ELSE "E1"
              /\ \A x \in ProcSet : x # p => pc'[x] = pc[x]
              /\ \A n \in Nodes : mem[n] # NIL => mem'[n] # NIL
          BY ConstAssump DEF ATypeOK, TypeOK
        <4>3. \A q, r \in ProcSet : Head(q)' = Head(q) /\ Pred(q, r)' = Pred(q, r)
          BY <4>1 DEF Head, Pred, Owned
        <4>4. TicketRange' /\ TicketInj' /\ TicketFull'
          BY <4>1 DEF LiveInv, TicketRange, TicketInj, TicketFull
        <4>5. PredTicket' /\ HeadTicket' /\ TailTicket' /\ EmptyServing'
          BY <4>1, <4>3 DEF LiveInv, PredTicket, HeadTicket, TailTicket, EmptyServing, Owned
        <4>6. WakeHead'
          BY <4>2, <4>3 DEF LiveInv, WakeHead, HeadNotNil
        <4>7. HeadNotNil'
          BY <4>2, <4>3 DEF LiveInv, HeadNotNil, ATypeOK, TypeOK
        <4>8. FreeTailNotNil'
          BY <4>1, <4>2 DEF LiveInv, FreeTailNotNil, Owned, ATypeOK, TypeOK
        <4> QED
          BY <4>4, <4>5, <4>6, <4>7, <4>8 DEF LiveInv
      <3>6. CASE AT5(p)
        <4> USE <3>6 DEF AT5, T5
        <4>1. \A q \in ProcSet : Own(q)' = Own(q) /\ InQ(q)' = InQ(q)
          <5> SUFFICES ASSUME NEW q \in ProcSet
                       PROVE  Own(q)' = Own(q) /\ InQ(q)' = InQ(q)
            OBVIOUS
          <5>1. CASE q = p
            BY <5>1 DEF Own, InQ, ATypeOK, TypeOK
          <5>2. CASE q # p
            BY <5>2 DEF Own, InQ, ATypeOK, TypeOK
          <5> QED
            BY <5>1, <5>2
        <4>2. pc'[p] = "E1" /\ \A x \in ProcSet : x # p => pc'[x] = pc[x]
          BY DEF ATypeOK, TypeOK
        <4>3. \A q, r \in ProcSet : Head(q)' = Head(q) /\ Pred(q, r)' = Pred(q, r)
          BY <4>1 DEF Head, Pred, Owned
        <4>4. TicketRange' /\ TicketInj' /\ TicketFull'
          BY <4>1 DEF LiveInv, TicketRange, TicketInj, TicketFull
        <4>5. PredTicket' /\ HeadTicket' /\ TailTicket' /\ EmptyServing'
          BY <4>1, <4>3 DEF LiveInv, PredTicket, HeadTicket, TailTicket, EmptyServing, Owned
        <4>6. WakeHead'
          BY <4>2, <4>3 DEF LiveInv, WakeHead
        <4>7. HeadNotNil'
          BY <4>2, <4>3 DEF LiveInv, HeadNotNil
        <4>8. FreeTailNotNil'
          BY <4>1 DEF LiveInv, FreeTailNotNil, Owned
        <4> QED
          BY <4>4, <4>5, <4>6, <4>7, <4>8 DEF LiveInv
      <3>7. CASE AT5Fail(p)
        BY <3>7 DEF AT5Fail, vars, LiveInv, TicketRange, TicketInj, TicketFull, PredTicket, HeadTicket,
               TailTicket, EmptyServing, WakeHead, HeadNotNil, FreeTailNotNil,
                   InQ, Own, Owned, Head, Pred
      <3>8. CASE AE1(p)
        <4> USE <3>8 DEF AE1, E1
        <4>1. Head(p)
          BY DEF Inv, CSHead
        <4>2. /\ pc'[p] = "E2"
              /\ \A x \in ProcSet : x # p => pc'[x] = pc[x]
              /\ nxtgo'[p] = mem[mynode[p]]
              /\ mem'[mynode[p]] = NONNIL
              /\ \A n \in Nodes : n # mynode[p] => mem'[n] = mem[n]
              /\ serving' = serving + 1
          BY DEF ATypeOK, TypeOK
        <4>3. \A q \in ProcSet : q # p => Own(q)' = Own(q) /\ InQ(q)' = InQ(q)
          BY DEF Own, InQ, ATypeOK, TypeOK
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
        <4>9. ticket[p] = serving
          BY <4>1 DEF LiveInv, HeadTicket
        <4>10. \A q \in ProcSet : q # p /\ InQ(q) => serving + 1 <= ticket[q]
          BY <4>4, <4>9 DEF LiveInv, TicketRange, TicketInj, ATypeOK
        <4>11. \A q, x \in ProcSet : Pred(q, x)' => q # p /\ x # p /\ Pred(q, x)
          BY <4>3, <4>4 DEF Pred
        <4>12. tail # mypred[p]
          BY <4>4 DEF Inv, PredNotTail
        <4>13. tail # mynode[p] => \E z \in ProcSet : z # p /\ Own(z) = tail
          BY <4>1, <4>4 DEF Inv, TailState, Owned
        <4>14. Owned(tail)' <=> tail # mynode[p]
          BY <4>3, <4>4, <4>6, <4>12, <4>13 DEF Owned
        <4>15. TicketRange'
          BY <4>2, <4>3, <4>4, <4>9, <4>10 DEF LiveInv, TicketRange, ATypeOK
        <4>16. TicketInj'
          BY <4>3, <4>4 DEF LiveInv, TicketInj
        <4>17. TicketFull'
          <5> SUFFICES ASSUME NEW k \in Nat, serving' <= k, k < nxtTicket'
                       PROVE  \E q \in ProcSet : InQ(q)' /\ ticket'[q] = k
            BY DEF TicketFull
          <5>1. PICK q \in ProcSet : InQ(q) /\ ticket[q] = k
            BY <4>2 DEF LiveInv, TicketFull, ATypeOK
          <5>2. q # p
            BY <5>1, <4>2, <4>9 DEF ATypeOK
          <5> QED
            BY <5>1, <5>2, <4>3
        <4>18. PredTicket'
          BY <4>11 DEF LiveInv, PredTicket
        <4>19. HeadTicket'
          BY <4>2, <4>8, <4>9 DEF LiveInv, PredTicket, HeadTicket
        <4>20. TailTicket'
          BY <4>3, <4>4 DEF LiveInv, TailTicket
        <4>21. EmptyServing'
          BY <4>2, <4>4, <4>9, <4>14 DEF LiveInv, EmptyServing, TailTicket
        <4>22. FreeTailNotNil'
          BY <4>2, <4>14, ConstAssump DEF FreeTailNotNil
        <4>23. WakeHead'
          <5> SUFFICES ASSUME NEW q \in ProcSet, Head(q)', pc'[q] = "T5"
                       PROVE  \E r \in ProcSet : pc'[r] = "E2" /\ nxtgo'[r] = q
            BY DEF WakeHead
          <5>1. q # p /\ Pred(p, q) /\ pc[q] = "T5"
            BY <4>2, <4>8
          <5>2. mem[mynode[p]] = q
            BY <5>1 DEF Inv, Handoff
          <5> QED
            BY <5>2, <4>2
        <4>24. HeadNotNil'
          BY <4>2, <4>8, ConstAssump DEF HeadNotNil, Pred
        <4> QED
          BY <4>15, <4>16, <4>17, <4>18, <4>19, <4>20, <4>21, <4>22, <4>23, <4>24
          DEF LiveInv
      <3>9. CASE AE2(p)
        <4> USE <3>9 DEF AE2, E2
        <4>1. \A q \in ProcSet : Own(q)' = Own(q) /\ InQ(q)' = InQ(q)
          <5> SUFFICES ASSUME NEW q \in ProcSet
                       PROVE  Own(q)' = Own(q) /\ InQ(q)' = InQ(q)
            OBVIOUS
          <5>1. CASE q = p
            BY <5>1 DEF Own, InQ, ATypeOK, TypeOK
          <5>2. CASE q # p
            BY <5>2 DEF Own, InQ, ATypeOK, TypeOK
          <5> QED
            BY <5>1, <5>2
        <4>2. /\ pc'[p] = "E3" /\ \A x \in ProcSet : x # p => pc'[x] = pc[x]
              /\ \A x \in ProcSet : goVal[x] => goVal'[x]
              /\ \A x \in ProcSet : x = nxtgo[p] => goVal'[x]
          BY ConstAssump DEF ATypeOK, TypeOK
        <4>3. \A q, r \in ProcSet : Head(q)' = Head(q) /\ Pred(q, r)' = Pred(q, r)
          BY <4>1 DEF Head, Pred, Owned
        <4>4. TicketRange' /\ TicketInj' /\ TicketFull'
          BY <4>1 DEF LiveInv, TicketRange, TicketInj, TicketFull
        <4>5. PredTicket' /\ HeadTicket' /\ TailTicket' /\ EmptyServing'
          BY <4>1, <4>3 DEF LiveInv, PredTicket, HeadTicket, TailTicket, EmptyServing, Owned
        <4>6. WakeHead'
          BY <4>2, <4>3 DEF LiveInv, WakeHead
        <4>7. HeadNotNil'
          BY <4>2, <4>3 DEF LiveInv, HeadNotNil
        <4>8. FreeTailNotNil'
          BY <4>1 DEF LiveInv, FreeTailNotNil, Owned
        <4> QED
          BY <4>4, <4>5, <4>6, <4>7, <4>8 DEF LiveInv
      <3>10. CASE AE3(p)
        <4> USE <3>10 DEF AE3, E3, ghostvars
        <4>1. \A q \in ProcSet : Own(q)' = Own(q) /\ InQ(q)' = InQ(q)
          <5> SUFFICES ASSUME NEW q \in ProcSet
                       PROVE  Own(q)' = Own(q) /\ InQ(q)' = InQ(q)
            OBVIOUS
          <5>1. CASE q = p
            BY <5>1 DEF Own, InQ, ATypeOK, TypeOK
          <5>2. CASE q # p
            BY <5>2 DEF Own, InQ, ATypeOK, TypeOK
          <5> QED
            BY <5>1, <5>2
        <4>2. /\ pc'[p] = "RM"
              /\ \A x \in ProcSet : x # p => pc'[x] = pc[x] /\ mynode'[x] = mynode[x]
          BY DEF ATypeOK, TypeOK
        <4>3. \A q, r \in ProcSet : Head(q)' = Head(q) /\ Pred(q, r)' = Pred(q, r)
          <5>1. ~InQ(p)
            BY DEF InQ
          <5> QED
            BY <5>1, <4>1, <4>2 DEF Head, Pred, Owned
        <4>4. ~InQ(p)
          BY DEF InQ
        <4>5. TicketRange' /\ TicketInj' /\ TicketFull'
          BY <4>1 DEF LiveInv, TicketRange, TicketInj, TicketFull
        <4>6. PredTicket' /\ HeadTicket' /\ TailTicket' /\ EmptyServing'
          BY <4>1, <4>2, <4>3, <4>4 DEF LiveInv, PredTicket, HeadTicket, TailTicket, EmptyServing, Owned
        <4>7. WakeHead' /\ HeadNotNil' /\ FreeTailNotNil'
          BY <4>1, <4>2, <4>3 DEF LiveInv, WakeHead, HeadNotNil, FreeTailNotNil, Owned
        <4> QED
          BY <4>5, <4>6, <4>7 DEF LiveInv
      <3> QED
        BY <2>1, <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9, <3>10
        DEF ALineActs
    <2>2. CASE UNCHANGED varsA
      BY <2>2 DEF varsA, vars, ghostvars, LiveInv, TicketRange, TicketInj, TicketFull, PredTicket, HeadTicket,
               TailTicket, EmptyServing, WakeHead, HeadNotNil, FreeTailNotNil,
                  InQ, Own, Owned, Head, Pred
    <2> QED
      BY <2>1, <2>2 DEF ANext
  <1> QED
    BY <1>1, <1>2, ASpecTypeOK, ASpecImpliesSpec, SpecInv, PTL DEF ASpec

LEMMA ArithStep ==
  ASSUME NEW a \in Nat, NEW b \in Nat, NEW n \in Nat,
         a <= b + (n+1), ~(a <= b + n)
  PROVE  a = b + (n+1)
  BY SMT

LEMMA AStepFacts ==
  ASSUME ATypeOK,
         NEW x \in ProcSet,
         NEW LineAct \in ALineActs(x),
         LineAct
  PROVE  /\ \A y \in ProcSet : y # x => /\ pc'[y] = pc[y]
                                         /\ ticket'[y] = ticket[y]
                                         /\ nxtgo'[y] = nxtgo[y]
                                         /\ (goVal[y] => goVal'[y])
         /\ serving' # serving => pc[x] = "E1"
         /\ pc[x] = "T4" => AT4(x)
         /\ pc[x] = "T5" => AT5(x) \/ AT5Fail(x)
         /\ pc[x] = "E1" => AE1(x)
         /\ pc[x] = "E2" => AE2(x)
  <1> USE DEF ATypeOK, TypeOK
  <1>1. CASE ATry(x)
    BY <1>1 DEF ATry, Try
  <1>2. CASE AT1(x)
    BY <1>2 DEF AT1, T1
  <1>3. CASE AT2(x)
    BY <1>3 DEF AT2, T2
  <1>4. CASE AT3(x)
    BY <1>4 DEF AT3, T3
  <1>5. CASE AT4(x)
    BY <1>5 DEF AT4, T4
  <1>6. CASE AT5(x)
    BY <1>6 DEF AT5, T5
  <1>7. CASE AT5Fail(x)
    BY <1>7 DEF AT5Fail, vars
  <1>8. CASE AE1(x)
    BY <1>8 DEF AE1, E1
  <1>9. CASE AE2(x)
    BY <1>9 DEF AE2, E2
  <1>10. CASE AE3(x)
    BY <1>10 DEF AE3, E3, ghostvars
  <1> QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10 DEF ALineActs

LEMMA WaitToE1 ==
  ASSUME NEW p \in ProcSet
  PROVE  AFairSpec => [](pc[p] = "T4" \/ pc[p] = "T5" => <>(pc[p] = "E1"))
  <1> DEFINE F == /\ [][ANext]_varsA /\ []ATypeOK /\ []Inv /\ []LiveInv
                  /\ AFairness
             I == ATypeOK /\ Inv /\ LiveInv
             EvE1(q) == <>(pc[q] = "E1")
             EvS(k) == <>(k < serving)
  <1> HIDE DEF EvE1, EvS
  <1>1. AFairSpec => F
    BY ASpecTypeOK, ASpecImpliesSpec, SpecInv, ASpecLiveInv, PTL DEF AFairSpec, ASpec, F
  <1>2. F => []F
    BY PTL DEF F, AFairness
  <1>3. F => I
    BY PTL DEF F, I
  <1>4. \A q \in ProcSet : I /\ InQ(q) /\ ticket[q] = serving => Head(q)
    <2> SUFFICES ASSUME NEW q \in ProcSet, I, InQ(q), ticket[q] = serving
                 PROVE  Head(q)
      OBVIOUS
    <2> SUFFICES ASSUME Owned(mypred[q])
                 PROVE  FALSE
      BY DEF Head
    <2>1. PICK z \in ProcSet : Own(z) = mypred[q]
      BY DEF Owned
    <2>2. InQ(z)
      BY <2>1 DEF I, Inv, PredOwned
    <2>3. Own(z) = mynode[z]
      BY <2>2 DEF InQ, Own
    <2>4. Pred(z, q)
      BY <2>1, <2>2, <2>3 DEF Pred
    <2>5. ticket[q] = ticket[z] + 1 /\ serving <= ticket[z]
      BY <2>2, <2>4 DEF I, LiveInv, PredTicket, TicketRange
    <2> QED
      BY <2>5 DEF I, ATypeOK
  <1>5. \A x \in ProcSet : I /\ pc[x] = "E1" => ticket[x] = serving /\ InQ(x)
    BY DEF I, Inv, CSHead, LiveInv, HeadTicket, InQ
  <1>6. \A x, y \in ProcSet : I /\ pc[x] = "E1" /\ pc[y] = "E1" => x = y
    BY DEF I, Inv, CSHead, OneHead
  <1>7. \A q \in ProcSet :
          F /\ (pc[q] = "T4" \/ pc[q] = "T5") /\ ticket[q] = serving => EvE1(q)
    <2> SUFFICES ASSUME NEW q \in ProcSet
                 PROVE  F /\ (pc[q] = "T4" \/ pc[q] = "T5") /\ ticket[q] = serving => EvE1(q)
      OBVIOUS
    <2> USE DEF EvE1
    <2>1. F => [](pc[q] = "T4" /\ ticket[q] = serving => <>(pc[q] = "E1"))
      <3>1. I /\ (pc[q] = "T4" /\ ticket[q] = serving) /\ [ANext]_varsA
              => (pc[q] = "T4" /\ ticket[q] = serving)' \/ (pc[q] = "E1")'
        <4> SUFFICES ASSUME I, pc[q] = "T4", ticket[q] = serving, [ANext]_varsA
                     PROVE  (pc[q] = "T4" /\ ticket[q] = serving)' \/ (pc[q] = "E1")'
          OBVIOUS
        <4>1. Head(q) /\ mem[mypred[q]] # NIL
          BY <1>4 DEF InQ, I, LiveInv, HeadNotNil
        <4>2. CASE UNCHANGED varsA
          BY <4>2 DEF varsA, vars, ghostvars
        <4>3. ASSUME NEW x \in ProcSet,
                     NEW LineAct \in ALineActs(x),
                     LineAct
              PROVE  (pc[q] = "T4" /\ ticket[q] = serving)' \/ (pc[q] = "E1")'
          <5>1. CASE x = q
            BY <5>1, <4>1, <4>3, AStepFacts DEF I, AT4, T4, ATypeOK, TypeOK
          <5>2. CASE x # q
            BY <5>2, <4>3, <1>5, AStepFacts DEF I, LiveInv, TicketInj, InQ
          <5> QED
            BY <5>1, <5>2
        <4> QED
          BY <4>2, <4>3 DEF ANext
      <3>2. I /\ (pc[q] = "T4" /\ ticket[q] = serving) /\ <<AT4(q)>>_vars => (pc[q] = "E1")'
        BY <1>4 DEF I, LiveInv, HeadNotNil, InQ, AT4, T4, ATypeOK, TypeOK
      <3>3. ATypeOK /\ (pc[q] = "T4" /\ ticket[q] = serving) => ENABLED <<AT4(q)>>_vars
        BY ExpandENABLED DEF ATypeOK, TypeOK, AT4, T4, vars
      <3>4. F => Fair(AT4(q))
        <4>1. AllFair => FairProc(q)
          BY DEF AllFair
        <4>2. FairProc(q) => FairAt(AT4(q))
          BY DEF FairProc
        <4> QED
          BY <4>1, <4>2, PTL DEF F, AFairness, FairAt, Fair
      <3> QED
        BY <3>1, <3>2, <3>3, <3>4, PTL DEF F, I, Fair
    <2>2. F => [](pc[q] = "T5" /\ goVal[q] => <>(pc[q] = "E1"))
      <3>1. I /\ (pc[q] = "T5" /\ goVal[q]) /\ [ANext]_varsA
              => (pc[q] = "T5" /\ goVal[q])' \/ (pc[q] = "E1")'
        <4> SUFFICES ASSUME I, pc[q] = "T5", goVal[q], [ANext]_varsA
                     PROVE  (pc[q] = "T5" /\ goVal[q])' \/ (pc[q] = "E1")'
          OBVIOUS
        <4>1. CASE UNCHANGED varsA
          BY <4>1 DEF varsA, vars
        <4>2. ASSUME NEW x \in ProcSet,
                     NEW LineAct \in ALineActs(x),
                     LineAct
              PROVE  (pc[q] = "T5" /\ goVal[q])' \/ (pc[q] = "E1")'
          <5>1. CASE x = q
            BY <5>1, <4>2, AStepFacts DEF I, AT5, T5, AT5Fail, ATypeOK, TypeOK
          <5>2. CASE x # q
            BY <5>2, <4>2, AStepFacts DEF I
          <5> QED
            BY <5>1, <5>2
        <4> QED
          BY <4>1, <4>2 DEF ANext
      <3>2. ATypeOK /\ (pc[q] = "T5" /\ goVal[q]) /\ <<AT5(q)>>_vars => (pc[q] = "E1")'
        BY DEF ATypeOK, TypeOK, AT5, T5
      <3>3. ATypeOK /\ (pc[q] = "T5" /\ goVal[q]) => ENABLED <<AT5(q)>>_vars
        BY ExpandENABLED DEF ATypeOK, TypeOK, AT5, T5, vars
      <3>4. F => Fair(AT5(q))
        <4>1. AllFair => FairProc(q)
          BY DEF AllFair
        <4>2. FairProc(q) => FairAt(AT5(q))
          BY DEF FairProc
        <4> QED
          BY <4>1, <4>2, PTL DEF F, AFairness, FairAt, Fair
      <3> QED
        BY <3>1, <3>2, <3>3, <3>4, PTL DEF F, I, Fair
    <2>3. ASSUME NEW r \in ProcSet
          PROVE  F => [](pc[q] = "T5" /\ pc[r] = "E2" /\ nxtgo[r] = q
                           => <>((pc[q] = "T5" /\ goVal[q]) \/ pc[q] = "E1"))
      <3>1. I /\ (pc[q] = "T5" /\ pc[r] = "E2" /\ nxtgo[r] = q) /\ [ANext]_varsA
              => \/ (pc[q] = "T5" /\ pc[r] = "E2" /\ nxtgo[r] = q)'
                 \/ ((pc[q] = "T5" /\ goVal[q]) \/ pc[q] = "E1")'
        <4> SUFFICES ASSUME I, pc[q] = "T5", pc[r] = "E2", nxtgo[r] = q, [ANext]_varsA
                     PROVE  \/ (pc[q] = "T5" /\ pc[r] = "E2" /\ nxtgo[r] = q)'
                            \/ ((pc[q] = "T5" /\ goVal[q]) \/ pc[q] = "E1")'
          OBVIOUS
        <4>1. CASE UNCHANGED varsA
          BY <4>1 DEF varsA, vars
        <4>2. ASSUME NEW x \in ProcSet,
                     NEW LineAct \in ALineActs(x),
                     LineAct
              PROVE  \/ (pc[q] = "T5" /\ pc[r] = "E2" /\ nxtgo[r] = q)'
                     \/ ((pc[q] = "T5" /\ goVal[q]) \/ pc[q] = "E1")'
          <5>1. CASE x = q
            BY <5>1, <4>2, AStepFacts DEF I, AT5, T5, AT5Fail, vars, ATypeOK, TypeOK
          <5>2. CASE x = r
            BY <5>2, <4>2, AStepFacts, ConstAssump DEF I, AE2, E2, ATypeOK, TypeOK
          <5>3. CASE x # q /\ x # r
            BY <5>3, <4>2, AStepFacts DEF I
          <5> QED
            BY <5>1, <5>2, <5>3
        <4> QED
          BY <4>1, <4>2 DEF ANext
      <3>2. ATypeOK /\ (pc[q] = "T5" /\ pc[r] = "E2" /\ nxtgo[r] = q) /\ <<AE2(r)>>_vars
              => ((pc[q] = "T5" /\ goVal[q]) \/ pc[q] = "E1")'
        BY ConstAssump DEF ATypeOK, TypeOK, AE2, E2
      <3>3. ATypeOK /\ (pc[q] = "T5" /\ pc[r] = "E2" /\ nxtgo[r] = q)
              => ENABLED <<AE2(r)>>_vars
        BY ExpandENABLED DEF ATypeOK, TypeOK, AE2, E2, vars
      <3>4. F => Fair(AE2(r))
        <4>1. AllFair => FairProc(r)
          BY DEF AllFair
        <4>2. FairProc(r) => FairAt(AE2(r))
          BY DEF FairProc
        <4> QED
          BY <4>1, <4>2, PTL DEF F, AFairness, FairAt, Fair
      <3> QED
        BY <3>1, <3>2, <3>3, <3>4, PTL DEF F, I, Fair
    <2>4. ASSUME NEW r \in ProcSet
          PROVE  F /\ pc[q] = "T5" /\ pc[r] = "E2" /\ nxtgo[r] = q => <>(pc[q] = "E1")
      BY <2>2, <2>3, <1>2, PTL
    <2>5. F /\ pc[q] = "T5" /\ ~goVal[q] /\ ticket[q] = serving => <>(pc[q] = "E1")
      <3>1. I /\ pc[q] = "T5" /\ ~goVal[q] /\ ticket[q] = serving
              => \E r \in ProcSet : pc[r] = "E2" /\ nxtgo[r] = q
        BY <1>4 DEF I, LiveInv, WakeHead, InQ
      <3> QED
        BY <3>1, <2>4, <1>3
    <2> QED
      BY <2>1, <2>2, <2>5, PTL
  <1>8. \A h \in ProcSet : \A k \in Nat :
          F /\ (pc[h] = "T4" \/ pc[h] = "T5" \/ pc[h] = "E1") /\ ticket[h] = k /\ serving = k
            => EvS(k)
    <2> SUFFICES ASSUME NEW h \in ProcSet, NEW k \in Nat
                 PROVE  F /\ (pc[h] = "T4" \/ pc[h] = "T5" \/ pc[h] = "E1")
                          /\ ticket[h] = k /\ serving = k => EvS(k)
      OBVIOUS
    <2> USE DEF EvS
    <2>1. I /\ ((pc[h] = "T4" \/ pc[h] = "T5" \/ pc[h] = "E1") /\ ticket[h] = k /\ serving = k)
            /\ [ANext]_varsA
            => \/ ((pc[h] = "T4" \/ pc[h] = "T5" \/ pc[h] = "E1") /\ ticket[h] = k /\ serving = k)'
               \/ (k < serving)'
      <3> SUFFICES ASSUME I, pc[h] = "T4" \/ pc[h] = "T5" \/ pc[h] = "E1",
                          ticket[h] = k, serving = k, [ANext]_varsA
                   PROVE  \/ ((pc[h] = "T4" \/ pc[h] = "T5" \/ pc[h] = "E1")
                                /\ ticket[h] = k /\ serving = k)'
                          \/ (k < serving)'
        OBVIOUS
      <3>1. CASE UNCHANGED varsA
        BY <3>1 DEF varsA, vars, ghostvars
      <3>2. ASSUME NEW x \in ProcSet,
                   NEW LineAct \in ALineActs(x),
                   LineAct
            PROVE  \/ ((pc[h] = "T4" \/ pc[h] = "T5" \/ pc[h] = "E1")
                         /\ ticket[h] = k /\ serving = k)'
                   \/ (k < serving)'
        <4>1. CASE x = h
          BY <4>1, <3>2, AStepFacts DEF I, ATypeOK, TypeOK, AT4, T4, AT5, T5, AT5Fail,
                                        AE1, E1, vars
        <4>2. CASE x # h
          BY <4>2, <3>2, <1>5, AStepFacts DEF I, LiveInv, TicketInj, InQ
        <4> QED
          BY <4>1, <4>2
      <3> QED
        BY <3>1, <3>2 DEF ANext
    <2>2. F => [](pc[h] = "E1" /\ serving = k => <>(k < serving))
      <3>1. I /\ (pc[h] = "E1" /\ serving = k) /\ [ANext]_varsA
              => (pc[h] = "E1" /\ serving = k)' \/ (k < serving)'
        <4> SUFFICES ASSUME I, pc[h] = "E1", serving = k, [ANext]_varsA
                     PROVE  (pc[h] = "E1" /\ serving = k)' \/ (k < serving)'
          OBVIOUS
        <4>1. CASE UNCHANGED varsA
          BY <4>1 DEF varsA, vars, ghostvars
        <4>2. ASSUME NEW x \in ProcSet,
                     NEW LineAct \in ALineActs(x),
                     LineAct
              PROVE  (pc[h] = "E1" /\ serving = k)' \/ (k < serving)'
          <5>1. CASE x = h
            BY <5>1, <4>2, AStepFacts DEF I, AE1, E1, ATypeOK
          <5>2. CASE x # h
            BY <5>2, <4>2, <1>6, AStepFacts DEF I
          <5> QED
            BY <5>1, <5>2
        <4> QED
          BY <4>1, <4>2 DEF ANext
      <3>2. ATypeOK /\ (pc[h] = "E1" /\ serving = k) /\ <<AE1(h)>>_vars => (k < serving)'
        BY DEF ATypeOK, AE1
      <3>3. ATypeOK /\ (pc[h] = "E1" /\ serving = k) => ENABLED <<AE1(h)>>_vars
        BY ExpandENABLED DEF ATypeOK, TypeOK, AE1, E1, vars
      <3>4. F => Fair(AE1(h))
        <4>1. AllFair => FairProc(h)
          BY DEF AllFair
        <4>2. FairProc(h) => FairAt(AE1(h))
          BY DEF FairProc
        <4> QED
          BY <4>1, <4>2, PTL DEF F, AFairness, FairAt, Fair
      <3> QED
        BY <3>1, <3>2, <3>3, <3>4, PTL DEF F, I, Fair
    <2>3. F => []((pc[h] = "T4" \/ pc[h] = "T5") /\ ticket[h] = serving => <>(pc[h] = "E1"))
      <3>1. F /\ (pc[h] = "T4" \/ pc[h] = "T5") /\ ticket[h] = serving => EvE1(h)
        BY <1>7
      <3> QED
        BY <3>1, <1>2, PTL DEF EvE1
    <2>4. ticket[h] = k /\ serving = k => ticket[h] = serving
      OBVIOUS
    <2> QED
      BY <2>1, <2>2, <2>3, <2>4, PTL DEF F, I
  <1> DEFINE BoxE(q, n) == []((pc[q] = "T4" \/ pc[q] = "T5") /\ ticket[q] <= serving + n
                                => <>(pc[q] = "E1"))
             Prop(n) == \A q \in ProcSet : F => BoxE(q, n)
  <1> HIDE DEF BoxE
  <1>9. Prop(0)
    <2> SUFFICES ASSUME NEW q \in ProcSet
                 PROVE  F => BoxE(q, 0)
      BY DEF Prop
    <2>1. I /\ (pc[q] = "T4" \/ pc[q] = "T5") /\ ticket[q] <= serving + 0 => ticket[q] = serving
      BY DEF I, LiveInv, TicketRange, InQ, ATypeOK
    <2>2. F /\ (pc[q] = "T4" \/ pc[q] = "T5") /\ ticket[q] <= serving + 0 => EvE1(q)
      BY <2>1, <1>3, <1>7
    <2>3. F /\ (pc[q] = "T4" \/ pc[q] = "T5") /\ ticket[q] <= serving + 0 => <>(pc[q] = "E1")
      BY <2>2 DEF EvE1
    <2> QED
      BY <2>3, <1>2, PTL DEF BoxE
  <1>10. \A n \in Nat : Prop(n) => Prop(n+1)
    <2> SUFFICES ASSUME NEW n \in Nat
                 PROVE  Prop(n) => Prop(n+1)
      OBVIOUS
    <2>1. ASSUME NEW q \in ProcSet
          PROVE  (F => BoxE(q, n)) => (F => BoxE(q, n+1))
      <3>1. F /\ (pc[q] = "T4" \/ pc[q] = "T5") /\ ticket[q] <= serving + (n+1)
              => <>(pc[q] = "E1" \/ ((pc[q] = "T4" \/ pc[q] = "T5") /\ ticket[q] <= serving + n))
        <4>1. F /\ (pc[q] = "T4" \/ pc[q] = "T5") /\ ticket[q] <= serving + n
                => <>(pc[q] = "E1" \/ ((pc[q] = "T4" \/ pc[q] = "T5") /\ ticket[q] <= serving + n))
          BY PTL
        <4>2. \A k \in Nat :
                F /\ (pc[q] = "T4" \/ pc[q] = "T5") /\ serving = k /\ ticket[q] = k + (n+1)
                  => <>(pc[q] = "E1" \/ ((pc[q] = "T4" \/ pc[q] = "T5") /\ ticket[q] <= serving + n))
          <5> SUFFICES ASSUME NEW k \in Nat
                       PROVE  F /\ (pc[q] = "T4" \/ pc[q] = "T5") /\ serving = k
                                /\ ticket[q] = k + (n+1)
                                => <>(pc[q] = "E1" \/ ((pc[q] = "T4" \/ pc[q] = "T5")
                                                        /\ ticket[q] <= serving + n))
            OBVIOUS
          <5>1. I /\ (pc[q] = "T4" \/ pc[q] = "T5") /\ serving = k /\ ticket[q] = k + (n+1)
                  => \E h \in ProcSet : (pc[h] = "T4" \/ pc[h] = "T5" \/ pc[h] = "E1")
                                        /\ ticket[h] = k
            BY DEF I, LiveInv, TicketRange, TicketFull, InQ, ATypeOK
          <5>2. F /\ (pc[q] = "T4" \/ pc[q] = "T5") /\ serving = k /\ ticket[q] = k + (n+1)
                  => EvS(k)
            BY <5>1, <1>3, <1>8
          <5>3. F /\ (pc[q] = "T4" \/ pc[q] = "T5") /\ serving = k /\ ticket[q] = k + (n+1)
                  => <>(k < serving)
            BY <5>2 DEF EvS
          <5>4. I /\ ((pc[q] = "T4" \/ pc[q] = "T5") /\ ticket[q] = k + (n+1)) /\ [ANext]_varsA
                  => ((pc[q] = "T4" \/ pc[q] = "T5") /\ ticket[q] = k + (n+1))'
                     \/ (pc[q] = "E1")'
            <6> SUFFICES ASSUME I, pc[q] = "T4" \/ pc[q] = "T5", ticket[q] = k + (n+1),
                                [ANext]_varsA
                         PROVE  ((pc[q] = "T4" \/ pc[q] = "T5") /\ ticket[q] = k + (n+1))'
                                \/ (pc[q] = "E1")'
              OBVIOUS
            <6>1. CASE UNCHANGED varsA
              BY <6>1 DEF varsA, vars, ghostvars
            <6>2. ASSUME NEW x \in ProcSet,
                         NEW LineAct \in ALineActs(x),
                         LineAct
                  PROVE  ((pc[q] = "T4" \/ pc[q] = "T5") /\ ticket[q] = k + (n+1))'
                         \/ (pc[q] = "E1")'
              <7>1. CASE x = q
                BY <7>1, <6>2, AStepFacts DEF I, ATypeOK, TypeOK, AT4, T4, AT5, T5,
                                              AT5Fail, vars
              <7>2. CASE x # q
                BY <7>2, <6>2, AStepFacts DEF I
              <7> QED
                BY <7>1, <7>2
            <6> QED
              BY <6>1, <6>2 DEF ANext
          <5>5. I /\ ((pc[q] = "T4" \/ pc[q] = "T5") /\ ticket[q] = k + (n+1)) /\ k < serving
                  => (pc[q] = "T4" \/ pc[q] = "T5") /\ ticket[q] <= serving + n
            BY DEF I, ATypeOK
          <5> QED
            BY <5>3, <5>4, <5>5, PTL DEF F, I
        <4>3. I /\ (pc[q] = "T4" \/ pc[q] = "T5") /\ ticket[q] <= serving + (n+1)
                /\ ~(ticket[q] <= serving + n)
                => \E k \in Nat : serving = k /\ ticket[q] = k + (n+1)
          <5> SUFFICES ASSUME I, ticket[q] <= serving + (n+1), ~(ticket[q] <= serving + n)
                       PROVE  \E k \in Nat : serving = k /\ ticket[q] = k + (n+1)
            OBVIOUS
          <5>1. serving \in Nat /\ ticket[q] \in Nat
            BY DEF I, ATypeOK
          <5> HIDE DEF I
          <5>2. ticket[q] = serving + (n+1)
            BY <5>1, ArithStep
          <5> QED
            BY <5>1, <5>2
        <4> QED
          BY <4>1, <4>2, <4>3, <1>3
      <3> QED
        BY <3>1, <1>2, PTL DEF BoxE
    <2> QED
      BY <2>1 DEF Prop
  <1> HIDE DEF Prop
  <1>11. \A n \in Nat : Prop(n)
    BY ONLY <1>9, <1>10, NatInduction, Isa
  <1>12. F /\ (pc[p] = "T4" \/ pc[p] = "T5") => <>(pc[p] = "E1")
    <2>1. \A n \in Nat : BoxE(p, n) =>
            ((pc[p] = "T4" \/ pc[p] = "T5") /\ ticket[p] <= serving + n => <>(pc[p] = "E1"))
      <3> SUFFICES ASSUME NEW n \in Nat
                   PROVE  BoxE(p, n) =>
                            ((pc[p] = "T4" \/ pc[p] = "T5") /\ ticket[p] <= serving + n
                               => <>(pc[p] = "E1"))
        OBVIOUS
      <3> QED
        BY PTL DEF BoxE
    <2>2. I /\ (pc[p] = "T4" \/ pc[p] = "T5") => \E n \in Nat : ticket[p] <= serving + n
      BY DEF I, ATypeOK
    <2> QED
      BY <2>1, <2>2, <1>3, <1>11 DEF Prop
  <1> QED
    BY <1>1, <1>2, <1>12, PTL

THEOREM StarvationFreedom == AFairSpec => StarvationFree
  <1> SUFFICES ASSUME NEW p \in ProcSet
               PROVE  AFairSpec => [](pc[p] = "T1" => <>(pc[p] = "E1"))
    BY DEF StarvationFree
  <1> DEFINE At(l) == pc[p] = l
  <1>1. AFairSpec => [](At("T1") => <>At("T2"))
    <2>1. ATypeOK /\ At("T1") /\ [ANext]_varsA => At("T1")' \/ At("T2")'
      <3> SUFFICES ASSUME ATypeOK, At("T1"), [ANext]_varsA
                   PROVE  At("T1")' \/ At("T2")'
        OBVIOUS
      <3> USE DEF At, ATypeOK, TypeOK
      <3>1. ASSUME NEW q \in ProcSet,
                   NEW LineAct \in ALineActs(q),
                   LineAct
            PROVE  At("T1")' \/ At("T2")'
        <4>1. CASE ATry(q)
          BY <4>1 DEF ATry, Try
        <4>2. CASE AT1(q)
          BY <4>2 DEF AT1, T1
        <4>3. CASE AT2(q)
          BY <4>3 DEF AT2, T2
        <4>4. CASE AT3(q)
          BY <4>4 DEF AT3, T3
        <4>5. CASE AT4(q)
          BY <4>5 DEF AT4, T4
        <4>6. CASE AT5(q)
          BY <4>6 DEF AT5, T5
        <4>7. CASE AT5Fail(q)
          BY <4>7 DEF AT5Fail, vars
        <4>8. CASE AE1(q)
          BY <4>8 DEF AE1, E1
        <4>9. CASE AE2(q)
          BY <4>9 DEF AE2, E2
        <4>10. CASE AE3(q)
          BY <4>10 DEF AE3, E3
        <4> QED
          BY <3>1, <4>1, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, <4>10
          DEF ALineActs
      <3>2. CASE UNCHANGED varsA
        BY <3>2 DEF varsA, vars
      <3> QED
        BY <3>1, <3>2 DEF ANext
    <2>2. ATypeOK /\ At("T1") /\ <<AT1(p)>>_vars => At("T2")'
      BY DEF At, ATypeOK, TypeOK, AT1, T1
    <2>3. ATypeOK /\ At("T1") => ENABLED <<AT1(p)>>_vars
      BY ExpandENABLED DEF At, ATypeOK, TypeOK, AT1, T1, vars
    <2>4. AFairSpec => Fair(AT1(p))
      <3>1. AllFair => FairAt(AT1(p))
        BY DEF AllFair, FairProc
      <3> QED
        BY <3>1, PTL DEF AFairSpec, AFairness, FairAt, Fair
    <2> QED
      BY <2>1, <2>2, <2>3, <2>4, ASpecTypeOK, PTL DEF AFairSpec, ASpec, Fair
  <1>2. AFairSpec => [](At("T2") => <>At("T3"))
    <2>1. ATypeOK /\ At("T2") /\ [ANext]_varsA => At("T2")' \/ At("T3")'
      <3> SUFFICES ASSUME ATypeOK, At("T2"), [ANext]_varsA
                   PROVE  At("T2")' \/ At("T3")'
        OBVIOUS
      <3> USE DEF At, ATypeOK, TypeOK
      <3>1. ASSUME NEW q \in ProcSet,
                   NEW LineAct \in ALineActs(q),
                   LineAct
            PROVE  At("T2")' \/ At("T3")'
        <4>1. CASE ATry(q)
          BY <4>1 DEF ATry, Try
        <4>2. CASE AT1(q)
          BY <4>2 DEF AT1, T1
        <4>3. CASE AT2(q)
          BY <4>3 DEF AT2, T2
        <4>4. CASE AT3(q)
          BY <4>4 DEF AT3, T3
        <4>5. CASE AT4(q)
          BY <4>5 DEF AT4, T4
        <4>6. CASE AT5(q)
          BY <4>6 DEF AT5, T5
        <4>7. CASE AT5Fail(q)
          BY <4>7 DEF AT5Fail, vars
        <4>8. CASE AE1(q)
          BY <4>8 DEF AE1, E1
        <4>9. CASE AE2(q)
          BY <4>9 DEF AE2, E2
        <4>10. CASE AE3(q)
          BY <4>10 DEF AE3, E3
        <4> QED
          BY <3>1, <4>1, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, <4>10
          DEF ALineActs
      <3>2. CASE UNCHANGED varsA
        BY <3>2 DEF varsA, vars
      <3> QED
        BY <3>1, <3>2 DEF ANext
    <2>2. ATypeOK /\ At("T2") /\ <<AT2(p)>>_vars => At("T3")'
      BY DEF At, ATypeOK, TypeOK, AT2, T2
    <2>3. ATypeOK /\ At("T2") => ENABLED <<AT2(p)>>_vars
      BY ExpandENABLED DEF At, ATypeOK, TypeOK, AT2, T2, vars
    <2>4. AFairSpec => Fair(AT2(p))
      <3>1. AllFair => FairAt(AT2(p))
        BY DEF AllFair, FairProc
      <3> QED
        BY <3>1, PTL DEF AFairSpec, AFairness, FairAt, Fair
    <2> QED
      BY <2>1, <2>2, <2>3, <2>4, ASpecTypeOK, PTL DEF AFairSpec, ASpec, Fair
  <1>3. AFairSpec => [](At("T3") => <>At("T4"))
    <2>1. ATypeOK /\ At("T3") /\ [ANext]_varsA => At("T3")' \/ At("T4")'
      <3> SUFFICES ASSUME ATypeOK, At("T3"), [ANext]_varsA
                   PROVE  At("T3")' \/ At("T4")'
        OBVIOUS
      <3> USE DEF At, ATypeOK, TypeOK
      <3>1. ASSUME NEW q \in ProcSet,
                   NEW LineAct \in ALineActs(q),
                   LineAct
            PROVE  At("T3")' \/ At("T4")'
        <4>1. CASE ATry(q)
          BY <4>1 DEF ATry, Try
        <4>2. CASE AT1(q)
          BY <4>2 DEF AT1, T1
        <4>3. CASE AT2(q)
          BY <4>3 DEF AT2, T2
        <4>4. CASE AT3(q)
          BY <4>4 DEF AT3, T3
        <4>5. CASE AT4(q)
          BY <4>5 DEF AT4, T4
        <4>6. CASE AT5(q)
          BY <4>6 DEF AT5, T5
        <4>7. CASE AT5Fail(q)
          BY <4>7 DEF AT5Fail, vars
        <4>8. CASE AE1(q)
          BY <4>8 DEF AE1, E1
        <4>9. CASE AE2(q)
          BY <4>9 DEF AE2, E2
        <4>10. CASE AE3(q)
          BY <4>10 DEF AE3, E3
        <4> QED
          BY <3>1, <4>1, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, <4>10
          DEF ALineActs
      <3>2. CASE UNCHANGED varsA
        BY <3>2 DEF varsA, vars
      <3> QED
        BY <3>1, <3>2 DEF ANext
    <2>2. ATypeOK /\ At("T3") /\ <<AT3(p)>>_vars => At("T4")'
      BY DEF At, ATypeOK, TypeOK, AT3, T3
    <2>3. ATypeOK /\ At("T3") => ENABLED <<AT3(p)>>_vars
      BY ExpandENABLED DEF At, ATypeOK, TypeOK, AT3, T3, vars
    <2>4. AFairSpec => Fair(AT3(p))
      <3>1. AllFair => FairAt(AT3(p))
        BY DEF AllFair, FairProc
      <3> QED
        BY <3>1, PTL DEF AFairSpec, AFairness, FairAt, Fair
    <2> QED
      BY <2>1, <2>2, <2>3, <2>4, ASpecTypeOK, PTL DEF AFairSpec, ASpec, Fair
  <1>4. AFairSpec => [](At("T4") \/ At("T5") => <>At("E1"))
    BY WaitToE1 DEF At
  <1> QED
    BY <1>1, <1>2, <1>3, <1>4, PTL DEF At


AheadWaiting == \A q, x \in ProcSet : x \in ahead[q] => pc[x] \in {"T4", "T5"}
AheadTicket  == \A q, x \in ProcSet :
                  x \in ahead[q] /\ pc[q] \in {"T4", "T5", "E1"} => ticket[x] < ticket[q]
FCFSInv == AheadWaiting /\ AheadTicket

FCFS == \A q \in ProcSet : pc[q] = "E1" => ahead[q] = {}

LEMMA ASpecFCFSInv == ASpec => []FCFSInv
  <1>1. AInit => FCFSInv
    BY DEF AInit, FCFSInv, AheadWaiting, AheadTicket
  <1>2. FCFSInv /\ LiveInv /\ ATypeOK /\ [ANext]_varsA => FCFSInv'
    <2> SUFFICES ASSUME FCFSInv, LiveInv, ATypeOK, [ANext]_varsA
                 PROVE  FCFSInv'
      OBVIOUS
    <2>1. ASSUME NEW p \in ProcSet,
                 NEW LineAct \in ALineActs(p),
                 LineAct
          PROVE  FCFSInv'
      <3>1. CASE ATry(p)
        BY <3>1 DEF ATry, Try, FCFSInv, AheadWaiting, AheadTicket, ATypeOK, TypeOK, LiveInv, TicketRange, InQ
      <3>2. CASE AT1(p)
        BY <3>2 DEF AT1, T1, FCFSInv, AheadWaiting, AheadTicket, ATypeOK, TypeOK, LiveInv, TicketRange, InQ
      <3>3. CASE AT2(p)
        BY <3>3 DEF AT2, T2, FCFSInv, AheadWaiting, AheadTicket, ATypeOK, TypeOK, LiveInv, TicketRange, InQ
      <3>4. CASE AT3(p)
        BY <3>4 DEF AT3, T3, FCFSInv, AheadWaiting, AheadTicket, ATypeOK, TypeOK, LiveInv, TicketRange, InQ
      <3>5. CASE AT4(p)
        BY <3>5 DEF AT4, T4, FCFSInv, AheadWaiting, AheadTicket, ATypeOK, TypeOK, LiveInv, TicketRange, InQ
      <3>6. CASE AT5(p)
        BY <3>6 DEF AT5, T5, FCFSInv, AheadWaiting, AheadTicket, ATypeOK, TypeOK, LiveInv, TicketRange, InQ
      <3>7. CASE AT5Fail(p)
        BY <3>7 DEF AT5Fail, vars, FCFSInv, AheadWaiting, AheadTicket, ATypeOK, TypeOK, LiveInv, TicketRange, InQ
      <3>8. CASE AE1(p)
        BY <3>8 DEF AE1, E1, FCFSInv, AheadWaiting, AheadTicket, ATypeOK, TypeOK, LiveInv, TicketRange, InQ
      <3>9. CASE AE2(p)
        BY <3>9 DEF AE2, E2, FCFSInv, AheadWaiting, AheadTicket, ATypeOK, TypeOK, LiveInv, TicketRange, InQ
      <3>10. CASE AE3(p)
        BY <3>10 DEF AE3, E3, ghostvars, FCFSInv, AheadWaiting, AheadTicket, ATypeOK, TypeOK, LiveInv, TicketRange, InQ
      <3> QED
        BY <2>1, <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9, <3>10
        DEF ALineActs
    <2>2. CASE UNCHANGED varsA
      BY <2>2 DEF varsA, vars, ghostvars, FCFSInv, AheadWaiting, AheadTicket
    <2> QED
      BY <2>1, <2>2 DEF ANext
  <1> QED
    BY <1>1, <1>2, ASpecTypeOK, ASpecLiveInv, PTL DEF ASpec

THEOREM FirstComeFirstServed == ASpec => []FCFS
  <1>1. FCFSInv /\ LiveInv /\ Inv /\ ATypeOK => FCFS
    <2> SUFFICES ASSUME FCFSInv, LiveInv, Inv, ATypeOK,
                        NEW q \in ProcSet, pc[q] = "E1",
                        NEW x \in ProcSet, x \in ahead[q]
                 PROVE  FALSE
      BY DEF FCFS, ATypeOK
    <2>1. pc[x] \in {"T4", "T5"} /\ ticket[x] < ticket[q]
      BY DEF FCFSInv, AheadWaiting, AheadTicket
    <2>2. serving <= ticket[x]
      BY <2>1 DEF LiveInv, TicketRange, InQ
    <2>3. ticket[q] = serving
      BY DEF Inv, CSHead, LiveInv, HeadTicket
    <2> QED
      BY <2>1, <2>2, <2>3 DEF ATypeOK
  <1> QED
    BY <1>1, ASpecFCFSInv, ASpecLiveInv, ASpecTypeOK, ASpecImpliesSpec, SpecInv, PTL

CCCap(l)  == CASE l = "T1" -> 0 [] l = "T2" -> 1 [] l = "T3" -> 2 [] l = "T4" -> 3
               [] l = "T5" -> 5 [] l = "E1" -> 6 [] l = "E2" -> 7 [] OTHER -> 8
DSMCap(l) == CASE l = "T1" -> 0 [] l = "T2" -> 1 [] l = "T3" -> 1 [] l = "T4" -> 2
               [] l = "T5" -> 3 [] l = "E1" -> 3 [] l = "E2" -> 4 [] OTHER -> 5

RMRInv == \A p \in ProcSet :
            /\ rmrCC[p] <= CCCap(pc[p])
            /\ pc[p] = "T5" => rmrCC[p] <= 4 \/ goCached[p] \/ goVal[p]
            /\ rmrDSM[p] <= DSMCap(pc[p])

RMRBound == \A p \in ProcSet : rmrCC[p] <= 8 /\ rmrDSM[p] <= 5

LEMMA ASpecRMRInv == ASpec => []RMRInv
  <1>1. AInit => RMRInv
    BY DEF AInit, Init, RMRInv, CCCap, DSMCap
  <1>2. RMRInv /\ ATypeOK /\ [ANext]_varsA => RMRInv'
    <2> SUFFICES ASSUME RMRInv, ATypeOK, [ANext]_varsA
                 PROVE  RMRInv'
      OBVIOUS
    <2>1. ASSUME NEW p \in ProcSet,
                 NEW LineAct \in ALineActs(p),
                 LineAct
          PROVE  RMRInv'
      <3>1. CASE ATry(p)
        BY <3>1, ConstAssump DEF ATry, Try, RMRInv, CCCap, DSMCap, ATypeOK, TypeOK
      <3>2. CASE AT1(p)
        BY <3>2, ConstAssump DEF AT1, T1, RMRInv, CCCap, DSMCap, ATypeOK, TypeOK
      <3>3. CASE AT2(p)
        BY <3>3, ConstAssump DEF AT2, T2, RMRInv, CCCap, DSMCap, ATypeOK, TypeOK
      <3>4. CASE AT3(p)
        BY <3>4, ConstAssump DEF AT3, T3, RMRInv, CCCap, DSMCap, ATypeOK, TypeOK
      <3>5. CASE AT4(p)
        BY <3>5, ConstAssump DEF AT4, T4, RMRInv, CCCap, DSMCap, ATypeOK, TypeOK
      <3>6. CASE AT5(p)
        BY <3>6, ConstAssump DEF AT5, T5, RMRInv, CCCap, DSMCap, ATypeOK, TypeOK
      <3>7. CASE AT5Fail(p)
        BY <3>7, ConstAssump DEF AT5Fail, vars, RMRInv, CCCap, DSMCap, ATypeOK, TypeOK
      <3>8. CASE AE1(p)
        BY <3>8, ConstAssump DEF AE1, E1, RMRInv, CCCap, DSMCap, ATypeOK, TypeOK
      <3>9. CASE AE2(p)
        BY <3>9, ConstAssump DEF AE2, E2, RMRInv, CCCap, DSMCap, ATypeOK, TypeOK
      <3>10. CASE AE3(p)
        BY <3>10, ConstAssump DEF AE3, E3, ghostvars, RMRInv, CCCap, DSMCap, ATypeOK, TypeOK
      <3> QED
        BY <2>1, <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9, <3>10
        DEF ALineActs
    <2>2. CASE UNCHANGED varsA
      BY <2>2 DEF varsA, vars, ghostvars, RMRInv, CCCap, DSMCap
    <2> QED
      BY <2>1, <2>2 DEF ANext
  <1> QED
    BY <1>1, <1>2, ASpecTypeOK, PTL DEF ASpec

THEOREM RMRBounded == ASpec => []RMRBound
  <1>1. RMRInv /\ ATypeOK => RMRBound
    BY DEF RMRInv, RMRBound, CCCap, DSMCap, ATypeOK, TypeOK, Lines
  <1> QED
    BY <1>1, ASpecRMRInv, ASpecTypeOK, PTL


=============================================================================
