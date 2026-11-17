----------------------------- MODULE UFSProofAssignment -----------------------------
EXTENDS UFSfromUF, TLAPS
INSTANCE MCTracking

VARIABLE P
vars == <<implvars, arg, ret, pc>>
varsP == <<vars, P>>

(* Invocation action for process p *)
InvocAct(p) == 
  /\ pc[p] = "RM"
  /\ \E op \in OpNames :
      /\ pc' = [pc EXCEPT ![p] = OpToFirstLine(op)]
      /\ \E newarg \in ArgsOf(op) : arg' = [arg EXCEPT ![p] = newarg]
  /\ UNCHANGED <<implvars, ret>>

(* Intermediate-line action for process p *)
InterAct(p) == \E LineAct \in InterLines(p) : LineAct

(* Return action for process p *)
ReturnAct(p) == \E LineAct \in ReturnLines(p) : LineAct

(* Initial state *)
Init == 
  /\ ImplInit
  /\ pc = [p \in ProcSet |-> "RM"]
  /\ arg \in [ProcSet -> ArgDomain]
  /\ ret \in [ProcSet -> RetDomain]

(* Next-state relation *)
Next == \E p \in ProcSet : 
  \/ InvocAct(p)
  \/ InterAct(p)
  \/ ReturnAct(p)

(* Full specification *)
Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* The initial state of the augmented algorithm.                           *)
(***************************************************************************)
AInit == 
  /\ Init
  /\ P = {[state |-> InitState,
           op    |-> [p \in ProcSet |-> "BOT"],
           arg   |-> [p \in ProcSet |-> "BOT"],
           res   |-> [p \in ProcSet |-> "BOT"]]}

(***************************************************************************)
(* The next action of the augmented algorithm.                             *)
(***************************************************************************)
(* The next action of the augmented algorithm is defined as follows:       *)
(* 1. If a process p invokes an operation, then the meta-configuration     *)
(*    tracking variable P is updated to include the invocation,            *)
(*    and allows subsequent evolving.                                      *)
(* 2. If a process p executes an intermediate line, then the meta-         *)
(*    configuration tracking variable P is updated via evolving.           *)
(*    (i.e. the linearization of all possible sequences of processes)      *)
(* 3. If a process p returns a value, then the meta-configuration tracking *)
(*    variable P, post-evolving, is filtered to include only those configs *)
(*    that have p returning the value to-be-returned (which is the         *)
(*    value in the ret register in the next state).                        *)
(***************************************************************************)
ANext == \E p \in ProcSet : 
  \/ /\ InvocAct(p)
     /\ P' = Evolve(Invoke(P, p, PCtoOp(pc'[p]), arg'[p]))
  \/ /\ InterAct(p)
     /\ P' = Evolve(P)
  \/ /\ ReturnAct(p)
     /\ P' = Filter(Evolve(P), p, ret'[p])

(***************************************************************************)
(* The spec of the augmented algorithm.                                    *)
(***************************************************************************)
ASpec == AInit /\ [][ANext]_varsP

(***************************************************************************)
(* Theorem: ASpec implies Spec.                                            *)
(***************************************************************************)
THEOREM ASpecImpliesSpec == ASpec => Spec
  <1>1. AInit => Init
    BY DEF AInit
  <1>2. [ANext]_varsP => [Next]_vars
    BY DEF ANext, Next, varsP
  <1> QED 
    BY <1>1, <1>2, PTL DEF ASpec, Spec

-----------------------------------------------------------------------------
(***************************************************************************)
(* ASSUMPTIONS                                                             *)
(***************************************************************************)
ASSUME NisNat == (N \in Nat) /\ (N > 0)

-----------------------------------------------------------------------------
(***************************************************************************)
(* INVARIANTS                                                              *)
(***************************************************************************)

TypeOK == 
    /\ part \in StateDomain
    /\ u \in [ProcSet -> NodeSet]
    /\ v \in [ProcSet -> NodeSet]
    /\ w \in [ProcSet -> NodeSet]
    /\ arg \in [ProcSet -> ArgDomain]
    /\ ret \in [ProcSet -> RetDomain]
    /\ pc \in [ProcSet -> LineIDs]
    /\ \A p \in ProcSet: pc[p] \in {"U1", "UR"} => arg[p] \in NodeSet \X NodeSet
    /\ \A p \in ProcSet: pc[p] \in {"F1", "FR"} => arg[p] \in NodeSet
    /\ \A p \in ProcSet: pc[p] \in {"S1", "S2", "S3", "SR"} => arg[p] \in NodeSet \X NodeSet

LEMMA SpecTypeOK == Spec => []TypeOK
  <1>1. Init => TypeOK
    <2> USE DEF Init, TypeOK
    <2> SUFFICES ASSUME Init
                 PROVE TypeOK
      OBVIOUS
    <2> QED 
      BY DEF ImplInit, StateDomain, ArgDomain, RetDomain, LineIDs
  <1>2. TypeOK /\ [Next]_vars => TypeOK'
    <2> SUFFICES ASSUME TypeOK /\ [Next]_vars
                 PROVE  TypeOK'
      OBVIOUS
    <2>1. ASSUME NEW p \in ProcSet,
                 InvocAct(p)
          PROVE  TypeOK'
      <3> USE <2>1 DEF TypeOK, InvocAct
      <3> QED
        BY DEF implvars, ArgDomain, RetDomain, LineIDs, OpToFirstLine, OpNames, ArgsOf
    <2>2. ASSUME NEW p \in ProcSet,
                 NEW LineAct \in InterLines(p),
                 LineAct
          PROVE  TypeOK'
      <3> USE DEF TypeOK
      <3>1. CASE U1(p)
        <4> USE <3>1 DEF U1
        <4> QED
          BY DEF StateDomain, UFUniteShared, RetDomain, RetsOf, OpNames, LineIDs, ArgsOf, OpNames, OpToFirstLine
      <3>2. CASE F1(p)
        <4> USE <3>2 DEF F1
        <4> QED
          BY DEF StateDomain, RetDomain, RetsOf, OpNames, LineIDs, ArgsOf,OpToFirstLine
      <3>3. CASE S1(p)
        <4> USE <3>3 DEF S1
        <4> QED
          BY DEF StateDomain, LineIDs, ArgsOf, OpNames, OpToFirstLine 
      <3>4. CASE S2(p)
        <4> USE <3>4 DEF S2
        <4>1. part' \in StateDomain
          OBVIOUS
        <4>2. u' \in [ProcSet -> NodeSet]
          OBVIOUS
        <4>3. v' \in [ProcSet -> NodeSet]
          BY DEF StateDomain
        <4>4. w' \in [ProcSet -> NodeSet]
          OBVIOUS
        <4>5. arg' \in [ProcSet -> ArgDomain]
          OBVIOUS
        <4>6. ret' \in [ProcSet -> RetDomain]
          BY NisNat DEF RetDomain, RetsOf, OpNames, StateDomain, ArgDomain, ArgsOf, NodeSet
        <4>7. pc' \in [ProcSet -> LineIDs]
          BY DEF LineIDs
        <4>8. \A p \in ProcSet: pc'[p] \in {"U1", "UR"} => arg'[p] \in NodeSet \X NodeSet
          BY DEF ArgsOf, OpNames, OpToFirstLine
        <4>9. \A p \in ProcSet: pc'[p] \in {"F1", "FR"} => arg'[p] \in NodeSet
          BY DEF ArgsOf, OpNames, OpToFirstLine
        <4>10. \A p \in ProcSet: pc'[p] \in {"S1", "S2", "S3", "SR"} => arg'[p] \in NodeSet \X NodeSet
          BY DEF ArgsOf, OpNames, OpToFirstLine
        <4> QED
          BY <4>1, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, <4>10
      <3>5. CASE S3(p)
        <4> USE <3>5 DEF S3
        <4>1. part' \in StateDomain
          OBVIOUS
        <4>2. u' \in [ProcSet -> NodeSet]
          OBVIOUS
        <4>3. v' \in [ProcSet -> NodeSet]
          OBVIOUS
        <4>4. w' \in [ProcSet -> NodeSet]
          BY DEF StateDomain
        <4>5. arg' \in [ProcSet -> ArgDomain]
          OBVIOUS
        <4>6. ret' \in [ProcSet -> RetDomain]
          BY NisNat DEF RetDomain, RetsOf, OpNames, StateDomain, ArgDomain, ArgsOf, NodeSet
        <4>7. pc' \in [ProcSet -> LineIDs]
          BY DEF LineIDs
        <4>8. \A p \in ProcSet: pc'[p] \in {"U1", "UR"} => arg'[p] \in NodeSet \X NodeSet
          BY DEF ArgsOf, OpNames, OpToFirstLine
        <4>9. \A p \in ProcSet: pc'[p] \in {"F1", "FR"} => arg'[p] \in NodeSet
          BY DEF ArgsOf, OpNames, OpToFirstLine
        <4>10. \A p \in ProcSet: pc'[p] \in {"S1", "S2", "S3", "SR"} => arg'[p] \in NodeSet \X NodeSet
          BY DEF ArgsOf, OpNames, OpToFirstLine
        <4> QED
          BY <4>1, <4>2, <4>3, <4>4, <4>5, <4>6, <4>7, <4>8, <4>9, <4>10
      <3> QED 
        BY <2>2, <3>1, <3>2, <3>3, <3>4, <3>5 DEF InterLines
    <2>3. ASSUME NEW p \in ProcSet,
                 NEW LineAct \in ReturnLines(p),
                 LineAct
          PROVE  TypeOK'
      <3> USE DEF TypeOK
      <3>1. CASE UR(p)
        <4> USE <3>1 DEF UR
        <4> QED
          BY DEF LineIDs, ArgsOf, OpNames, OpToFirstLine
      <3>2. CASE FR(p)
        <4> USE <3>2 DEF FR
        <4> QED
          BY DEF LineIDs, ArgsOf, OpNames, OpToFirstLine
      <3>3. CASE SR(p)
        <4> USE <3>3 DEF SR
        <4> QED
          BY DEF LineIDs, ArgsOf, OpNames, OpToFirstLine
      <3> QED
        BY <2>3, <3>1, <3>2, <3>3 DEF ReturnLines
    <2>4. CASE UNCHANGED vars
      BY <2>4 DEF vars, implvars, TypeOK
    <2> QED
      BY <2>1, <2>2, <2>3, <2>4 DEF InterAct, Next, ReturnAct
  <1> QED
    BY <1>1, <1>2, PTL DEF Spec




Inv == \A p \in ProcSet : pc[p] \in {"S2", "S3", "SR"} => part[u[p]] = part[arg[p][1]] /\ part[v[p]] = part[arg[p][2]]

LEMMA SpecInv == Spec => []Inv
  <1>1. Init /\ TypeOK => Inv
    <2> SUFFICES ASSUME Init, TypeOK
                 PROVE Inv
      OBVIOUS
    <2> QED
      BY DEF Init, Inv
  <1>2. Inv /\ TypeOK /\ [Next /\ TypeOK']_vars => Inv'
    <2> SUFFICES ASSUME Inv /\ TypeOK /\ [Next /\ TypeOK']_vars
                 PROVE  Inv'
      OBVIOUS
    <2>1. ASSUME NEW p \in ProcSet,
                 InvocAct(p)
          PROVE  Inv'
      BY <2>1 DEF InvocAct, Inv, TypeOK, StateDomain, implvars, OpNames, OpToFirstLine
    <2>2. ASSUME NEW p \in ProcSet,
                 NEW LineAct \in InterLines(p),
                 LineAct, TypeOK'
          PROVE  Inv'
      <3> USE DEF Inv
      <3>1. CASE U1(p)
        <4> USE <3>1 DEF U1, TypeOK
        <4> TypeOK'
          BY <2>2
        <4> SUFFICES ASSUME NEW q \in ProcSet, pc'[q] \in {"S2", "S3", "SR"}
                     PROVE part'[u[q]] = part'[arg[q][1]] /\ part'[v[q]] = part'[arg[q][2]]
          OBVIOUS
        <4> QED
          BY DEF StateDomain, UFUniteShared
      <3>2. CASE F1(p)
        BY <3>2 DEF F1, Inv, TypeOK, StateDomain
      <3>3. CASE S1(p)
        <4> USE <3>3 DEF S1, TypeOK
        <4> SUFFICES ASSUME NEW q \in ProcSet, pc'[q] \in {"S2", "S3", "SR"}
                     PROVE part[u'[q]] = part[arg[q][1]] /\ part[v'[q]] = part[arg[q][2]]
          OBVIOUS
        <4>1. part' = part
          OBVIOUS
        <4>2. arg' = arg
          OBVIOUS
        <4> CASE q = p
          <5>1. part[u'[q]] = part[arg[q][1]]
            <6>1. u'[q] = part[arg[q][1]]
              BY DEF StateDomain
            <6>2. part[part[arg[q][1]]] = part[arg[q][1]]
              BY <6>1 DEF StateDomain
            <6> QED
              BY <6>1, <6>2
          <5>2. part[v'[q]] = part[arg[q][2]]
            <6>1. v'[q] = arg[q][2]
              OBVIOUS
            <6> QED
              BY <6>1 DEF StateDomain
          <5> QED 
            BY <5>1, <5>2
        <4> CASE q # p
          <5>1. u'[q] = u[q]
            OBVIOUS
          <5>2. v'[q] = v[q]
            OBVIOUS
          <5> QED
            BY <5>1, <5>2 DEF StateDomain
        <4> QED
          OBVIOUS
      <3>4. CASE S2(p)
        <4> USE <3>4 DEF S2, TypeOK
        <4> SUFFICES ASSUME NEW q \in ProcSet, pc'[q] \in {"S2", "S3", "SR"}
                     PROVE part[u[q]] = part[arg[q][1]] /\ part[v'[q]] = part[arg[q][2]]
          OBVIOUS
        <4> CASE q = p
          <5>1. u'[q] = u[q]
            OBVIOUS
          <5>2. part[v'[q]] = part[v[q]]
            BY DEF StateDomain
          <5> QED 
            BY <5>1, <5>2 DEF StateDomain
        <4> CASE q # p
          <5>1. u'[q] = u[q]
            OBVIOUS
          <5>2. v'[q] = v[q]
            OBVIOUS
          <5> QED
            BY <5>1, <5>2 DEF StateDomain
        <4> QED
          OBVIOUS
      <3>5. CASE S3(p)
        <4> USE <3>5 DEF S3, TypeOK
        <4> SUFFICES ASSUME NEW q \in ProcSet, pc'[q] \in {"S2", "S3", "SR"}
                     PROVE part[u[q]] = part[arg[q][1]] /\ part[v'[q]] = part[arg[q][2]]
          OBVIOUS
        <4> CASE q = p
          OBVIOUS
        <4> CASE q # p
          <5>1. u'[q] = u[q]
            OBVIOUS
          <5>2. v'[q] = v[q]
            OBVIOUS
          <5> QED
            BY <5>1, <5>2 DEF StateDomain
        <4> QED
          OBVIOUS
      <3> QED
        BY <2>2, <3>1, <3>2, <3>3, <3>4, <3>5 DEF InterLines
    <2>3. ASSUME NEW p \in ProcSet,
                 NEW LineAct \in ReturnLines(p),
                 LineAct
          PROVE  Inv'
      <3>1. CASE UR(p)
        BY <3>1 DEF UR, Inv, TypeOK, StateDomain
      <3>2. CASE FR(p)
        BY <3>2 DEF FR, Inv, TypeOK, StateDomain
      <3>3. CASE SR(p)
        BY <3>3 DEF SR, Inv, TypeOK, StateDomain
      <3> QED 
        BY <2>3, <3>1, <3>2, <3>3 DEF ReturnLines
    <2>4. CASE UNCHANGED vars
      BY <2>4 DEF vars, implvars, Inv
    <2> QED
      BY <2>1, <2>2, <2>3, <2>4 DEF InterAct, Next, ReturnAct
  <1> QED
    BY <1>1, <1>2, PTL, SpecTypeOK DEF Spec
-----------------------------------------------------------------------------
(***************************************************************************)
(* Plausibility set definition                                             *)
(***************************************************************************)


(* TODO: Add conditions specifying the state and the linearization points. *)
Q == {c \in ConfigDomain : 
        /\ \A q \in ProcSet : c.op[q] = PCtoOp(pc[q])
        /\ \A q \in ProcSet :
            c.arg[q] = (IF pc[q] = "RM" THEN "BOT" ELSE arg[q])
        /\ c.state = part

        /\ \A p \in ProcSet: pc[p] = "RM" => c.res[p] = "BOT"

        /\ \A p \in ProcSet: pc[p] = "F1" => c.res[p] = "BOT"
        /\ \A p \in ProcSet: pc[p] = "FR" => c.res[p] = ret[p]
        
        /\ \A p \in ProcSet: pc[p] = "U1" => c.res[p] = "BOT"
        /\ \A p \in ProcSet: pc[p] = "UR" => c.res[p] = ret[p]

        /\ \A p \in ProcSet: pc[p] = "S1" => c.res[p] = "BOT"
        /\ \A p \in ProcSet: pc[p] = "S2" => c.res[p] = "BOT"
        /\ \A p \in ProcSet: pc[p] = "S3" => (c.res[p] = "BOT" \/ (part[u[p]] = u[p] /\ c.res[p] = FALSE))
        /\ \A p \in ProcSet: pc[p] = "SR" => c.res[p] = ret[p]
    }


-----------------------------------------------------------------------------
(***************************************************************************)
(* Plausibility set theorem 1: Q is non-empty is an invariant of ASpec.    *)
(***************************************************************************)

LEMMA SpecImpliesQNE == (TypeOK /\ Inv) => Q # {}
  <1> SUFFICES ASSUME TypeOK, Inv
               PROVE  Q # {}
    OBVIOUS
  <1>1. DEFINE c == [state |-> part, 
                    op |-> [p \in ProcSet |-> PCtoOp(pc[p])],
                    arg |-> [p \in ProcSet |-> IF pc[p] = "RM" THEN "BOT" ELSE arg[p]],
                    res |-> [p \in ProcSet |-> IF pc[p] \in {"FR", "UR", "SR"} THEN ret[p] ELSE "BOT"]
                    ]
  <1>2. c \in ConfigDomain
    BY DEF c, ConfigDomain, OpDomain, ArgDomain, ResDomain, RetDomain, OpNames, TypeOK, PCtoOp, LineIDs 
  <1>3. c \in Q
    BY <1>2 DEF c, Q
  <1>4. QED
    BY <1>3
    

THEOREM PlausSetThm1 == ASpec => [](Q # {})
  <1> SUFFICES Spec => [](Q # {})
    BY ASpecImpliesSpec
  <1> SUFFICES Spec => []TypeOK /\ []Inv
    BY PTL, SpecImpliesQNE
  <1> QED
    BY SpecTypeOK, SpecInv
-----------------------------------------------------------------------------
(***************************************************************************)
(* Plausibility set lemma 2.1: Q is initally the same as the singleton P.  *)
(***************************************************************************)
THEOREM PlausSetInitLemma == AInit => Q = P
  <1> SUFFICES ASSUME AInit
               PROVE  Q = P
    OBVIOUS
  <1>1. P = {[state |-> InitState,
              op    |-> [p \in ProcSet |-> "BOT"],
              arg   |-> [p \in ProcSet |-> "BOT"],
              res   |-> [p \in ProcSet |-> "BOT"]]}
    BY DEF AInit

  <1>2. Q = {[state |-> InitState,
              op    |-> [p \in ProcSet |-> "BOT"],
              arg   |-> [p \in ProcSet |-> "BOT"],
              res   |-> [p \in ProcSet |-> "BOT"]]}
    

    <2>1. Q \in SUBSET ConfigDomain
        BY DEF Q
    <2>2. Q # {}
        BY SpecImpliesQNE DEF AInit, Init, TypeOK, ImplInit, Inv, StateDomain, LineIDs
    <2> SUFFICES \A c \in Q : 
            c = [state |-> InitState,
                op    |-> [p \in ProcSet |-> "BOT"],
                arg   |-> [p \in ProcSet |-> "BOT"],
                res   |-> [p \in ProcSet |-> "BOT"]]
        BY <2>2 DEF AInit
    <2> SUFFICES ASSUME NEW c \in ConfigDomain,
                        c \in Q
                PROVE  /\ c.state = InitState
                        /\ c.op = [p \in ProcSet |-> "BOT"]
                        /\ c.arg = [p \in ProcSet |-> "BOT"]
                        /\ c.res = [p \in ProcSet |-> "BOT"]
        BY <2>1 DEF ConfigDomain
    <2>3. c.state = InitState
        BY DEF AInit, Init, ImplInit, Q, InitState
    <2>4. c.op = [p \in ProcSet |-> "BOT"]
        BY DEF Q, PCtoOp, AInit, Init, ConfigDomain
    <2>5. c.arg = [p \in ProcSet |-> "BOT"]
        BY DEF Q, AInit, Init, ConfigDomain
    <2>6. c.res = [p \in ProcSet |-> "BOT"]
        BY DEF Q, ConfigDomain, AInit, Init 

    <2> QED 
        BY <2>3, <2>4, <2>5, <2>6

  <1> QED
    BY <1>1, <1>2
-----------------------------------------------------------------------------
(***************************************************************************)
(* Plausibility set lemma 2.2: If an invocation action takes place, then   *)
(* the new plausibility set Q' is a subset of the evolution of             *)
(* Invoke(Q, p, PCtoOp(pc'[p]), arg'[p]).                                  *)
(***************************************************************************)
(* Note that PCtoOp(pc'[p]) is the operation being invoked by p, and       *)
(* arg'[p] is the argument that was picked for the invocation.             *)
(***************************************************************************)
InvocProperty == 
  \A p \in ProcSet : InvocAct(p) => (Q' \in SUBSET Evolve(Invoke(Q, p, PCtoOp(pc'[p]), arg'[p])))

THEOREM InvocLemma == ASpec => [][InvocProperty]_varsP
  <1> SUFFICES ASSUME []TypeOK
               PROVE  ASpec => [][InvocProperty]_varsP
    BY ASpecImpliesSpec, SpecTypeOK
  <1>1. TypeOK
    BY PTL
  <1> SUFFICES ASSUME ANext
               PROVE  InvocProperty
    BY PTL DEF ASpec
  <1> SUFFICES ASSUME NEW p \in ProcSet,
                      InvocAct(p)
               PROVE  Q' \in SUBSET Evolve(Invoke(Q, p, PCtoOp(pc'[p]), arg'[p]))
    BY DEF InvocProperty
  <1> SUFFICES ASSUME NEW c \in ConfigDomain,
                      c \in Q'
               PROVE  c \in Evolve(Invoke(Q, p, PCtoOp(pc'[p]), arg'[p]))
    BY Zenon DEF Q
  <1> USE DEF InvocAct
  <1>2. Q \in SUBSET ConfigDomain
    BY DEF Q
  <1>3. c.op[p] = PCtoOp(pc'[p])
    BY DEF Q
  <1>4. c.arg[p] = arg'[p]
    <2> SUFFICES pc'[p] # "RM"
      BY DEF Q
    <2> QED
      BY <1>1 DEF OpToFirstLine, OpNames, TypeOK
  <1>5. c.res[p] = "BOT"
    <2> SUFFICES pc'[p] = "U1" \/ pc'[p] = "F1" \/ pc'[p] = "S1"
        BY DEF Q
    <2> QED
      BY <1>1 DEF Q, OpToFirstLine, OpNames, TypeOK
  <1> DEFINE c_prev == [c EXCEPT !.op = [c.op EXCEPT ![p] = "BOT"],
                                 !.arg = [c.arg EXCEPT ![p] = "BOT"]]
  <1> SUFFICES c_prev \in Q
    BY <1>2, <1>3, <1>4, <1>5, InvokeAndEvolveFromUninvoked
  <1>6. c_prev.op[p] = "BOT"
    BY DEF c_prev, ConfigDomain
  <1>7. c_prev.arg[p] = "BOT"
    BY DEF  c_prev, ConfigDomain
  <1>8. c_prev.res[p] = "BOT"
    BY <1>5 DEF c_prev, ConfigDomain
  <1>9. c_prev.state = part 
    BY DEF c_prev, Q, implvars, ConfigDomain
  <1>10. c_prev \in Q
    <2>1. /\ UNCHANGED <<part, u, ret>> 
          /\ \A q \in ProcSet: q # p => 
                /\ pc'[q] = pc[q] 
                /\ arg'[q] = arg[q] 
          /\ pc[p] = "RM"
        BY <1>1 DEF implvars, TypeOK
    
    <2>2. /\ c_prev.res = c.res
          /\ \A q \in ProcSet : q # p =>
               /\ c_prev.op[q] = c.op[q]
               /\ c_prev.arg[q] = c.arg[q]
      BY DEF c_prev, ConfigDomain
    
    <2>3. c_prev \in ConfigDomain
      BY DEF c_prev, ConfigDomain, OpDomain, ArgDomain
 
    <2>4. ASSUME NEW q \in ProcSet 
          PROVE /\ c.op[q] = PCtoOp(pc'[q])
                /\ c.arg[q] = (IF pc'[q] = "RM" THEN "BOT" ELSE arg'[q])
        BY DEF Q

    <2>5. ASSUME NEW q \in ProcSet
          PROVE /\ c_prev.op[q] = PCtoOp(pc[q])
                /\ c_prev.arg[q] = (IF pc[q] = "RM" THEN "BOT" ELSE arg[q])
        <3>1. CASE q = p
            BY <3>1, <2>1, <1>6, <1>7 DEF PCtoOp
        <3>2. CASE q # p
            BY <3>2, <2>1, <2>2, <2>4 
        <3> QED
            BY <3>1, <3>2
    
    <2>6. ASSUME NEW q \in ProcSet
          PROVE  /\ pc[q] \in {"RM","F1","U1","S1","S2"} => c_prev.res[q] = "BOT"
                 /\ pc[q] \in {"FR","UR","SR"} => c_prev.res[q] = ret[q]
                 /\ pc[q] = "S3" => (c_prev.res[q] = "BOT" \/ (part[u[q]] = u[q] /\ c_prev.res[q] = FALSE))
      <3>1. CASE q = p
        BY <3>1, <2>1, <1>8
      <3>2. CASE q # p
        BY <3>2, <2>1, <2>2 DEF Q
      <3> QED BY <3>1, <3>2

    <2> QED
      BY <2>3, <2>5, <2>6, <1>9 DEF Q
    \* <2> QED 
    \*     BY <2>1, <2>2, <1>6, <1>7, <1>8, <1>9 DEF c_prev, ConfigDomain, Q, PCtoOp, OpDomain, ArgDomain, ResDomain
  <1> QED
    BY <1>10

-----------------------------------------------------------------------------
(***************************************************************************)
(* Plausibility set lemma 2.3: If an intermediate-line action takes place, *)
(* then the new plausibility set Q' is a subset of the evolution of Q.     *)
(***************************************************************************)
InterProperty == \A p \in ProcSet : InterAct(p) => (Q' \in SUBSET Evolve(Q))

\* a helper for the conditions Q places on process q's entries in configuration c

QAt (c, q) == 
    /\ c.op[q] = PCtoOp(pc[q])
    /\ c.arg[q] = (IF pc[q] = "RM" THEN "BOT" ELSE arg[q]) 
    /\ pc[q] \in {"F1", "S1", "S2", "U1", "RM"} => c.res[q] = "BOT"
    /\ pc[q] \in {"FR", "SR", "UR"} => c.res[q] = ret[q]
    /\ pc[q] = "S3" => (c.res[q] = "BOT" \/ (part[u[q]] = u[q] /\ c.res[q] = FALSE))

THEOREM InterLemma == ASpec => [][InterProperty]_varsP
  <1> SUFFICES ASSUME []TypeOK, []Inv
               PROVE  ASpec => [][InterProperty]_varsP
    BY ASpecImpliesSpec, SpecTypeOK, SpecInv
  <1> SUFFICES ASSUME ANext
               PROVE  InterProperty
    BY PTL DEF ASpec
  <1> SUFFICES ASSUME NEW p \in ProcSet,
                      InterAct(p)
               PROVE  Q' \in SUBSET Evolve(Q)
    BY DEF InterProperty
  <1>0. TypeOK /\ Inv /\ TypeOK' /\ Inv'
    BY PTL

  <1>1. ASSUME U1(p),
                NEW c \in ConfigDomain, 
                c \in Q'
        PROVE c \in Evolve(Q)
    <2> USE <1>1 DEF U1
    <2> DEFINE c_prev == [c EXCEPT !.state = part, !.res = [c.res EXCEPT ![p] = "BOT"]]
    <2> SUFFICES /\ c_prev \in Q 
                 /\ Delta(c_prev, p, c)
        BY SingleDeltaEvolve DEF Q
    <2>1. c_prev \in Q
        <3>1. /\ c_prev.state = part 
              /\ c_prev.op = c.op
              /\ c_prev.arg = c.arg
              /\ c_prev.res[p] = "BOT"
              /\ \A q \in ProcSet: q # p => c_prev.res[q] = c.res[q]  
            BY DEF c_prev, ConfigDomain
        <3>2. c.state = part' /\ \A q \in ProcSet: QAt(c, q)'
            BY DEF Q, QAt

        <3>3. \A q \in ProcSet: part'[u[q]] = u[q] => part[u[q]] = u[q]
            BY <1>0 DEF U1, UFUniteShared, TypeOK, StateDomain

        <3>4. ASSUME NEW q \in ProcSet, q # p 
            PROVE QAt(c_prev, q)
            BY <3>4, <3>1, <3>2, <3>3, <1>0 DEF QAt, TypeOK 
        
        <3>5. QAt(c_prev, p)
            BY <3>1, <3>2, <1>0 DEF QAt, PCtoOp, TypeOK

        <3>6. c_prev \in ConfigDomain
            BY <1>0 DEF c_prev, ConfigDomain, ResDomain, TypeOK

        <3> QED 
            BY <3>1, <3>4, <3>5, <3>6 DEF Q, QAt

    <2>2. Delta(c_prev, p, c)
        BY <2>1, <1>0 DEF Delta, c_prev, ArgsOf, Q, U1, PCtoOp, TypeOK, UFSUnite, UFUniteShared, ConfigDomain
    <2> QED
        BY <2>1, <2>2

  <1>2. ASSUME F1(p),
                NEW c \in ConfigDomain, 
                c \in Q'
        PROVE c \in Evolve(Q)
    <2> USE <1>2 DEF F1
    <2> DEFINE c_prev == [c EXCEPT !.res = [c.res EXCEPT ![p] = "BOT"]]
    <2> SUFFICES /\ c_prev \in Q 
                 /\ Delta(c_prev, p, c)
        BY SingleDeltaEvolve DEF Q
    <2>1. c_prev \in Q
        <3>1. /\ c_prev.state = c.state 
              /\ c_prev.op = c.op
              /\ c_prev.arg = c.arg
              /\ c_prev.res[p] = "BOT"
              /\ \A q \in ProcSet: q # p => c_prev.res[q] = c.res[q]
            BY DEF c_prev, ConfigDomain

        <3>2. c.state = part' /\ \A q \in ProcSet: QAt(c, q)'
            BY DEF Q, QAt

        <3>3. ASSUME NEW q \in ProcSet, q # p 
            PROVE QAt(c_prev, q)
            BY <3>3, <3>1, <3>2, <3>3, <1>0 DEF QAt, TypeOK 
        
        <3>4. QAt(c_prev, p)
            BY <3>1, <3>2, <1>0 DEF QAt, PCtoOp, TypeOK

        <3>5. c_prev \in ConfigDomain
            BY DEF c_prev, ConfigDomain, ResDomain

        <3> QED 
            BY <3>1, <3>2, <3>3, <3>4, <3>5 DEF Q, QAt

    <2>2. Delta(c_prev, p, c)
        BY <2>1 ,<1>0 DEF Delta, c_prev, ArgsOf, Q, F1, PCtoOp, TypeOK, ConfigDomain
    <2> QED
        BY <2>1, <2>2

  <1>3. ASSUME S1(p),
                NEW c \in ConfigDomain, 
                c \in Q'
        PROVE c \in Evolve(Q)
    <2> USE <1>3 DEF S1
    <2>1. /\ pc'[p] = "S2"
          /\ \A q \in ProcSet : q # p =>
               /\ pc'[q] = pc[q]
               /\ u'[q] = u[q]
      BY <1>0 DEF S1, TypeOK

    <2>2. c \in Q
        <3>1. c.state = part' /\ \A q \in ProcSet: QAt(c, q)' 
            BY DEF Q, QAt
        <3>2. QAt(c, p) 
            BY <3>1, <2>1, <1>0 DEF QAt, PCtoOp, TypeOK
        <3>3. ASSUME NEW q \in ProcSet, q # p 
            PROVE QAt(c,q)
            BY <3>3, <3>1, <2>1, <1>0 DEF QAt, TypeOK
        <3> QED 
            BY <3>1, <3>2, <3>3 DEF Q, QAt
    <2> QED
        BY <2>2, EmptySeqEvolve DEF Q

  <1>4. ASSUME S2(p),
                NEW c \in ConfigDomain, 
                c \in Q'
        PROVE c \in Evolve(Q)
    <2> USE <1>4 DEF S2
    <2> DEFINE c_prev == [c EXCEPT !.res = [c.res EXCEPT ![p] = "BOT"]]
    <2>1. c_prev \in Q
        <3>1. /\ c_prev.state = c.state 
              /\ c_prev.op = c.op
              /\ c_prev.arg = c.arg
              /\ c_prev.res[p] = "BOT"
              /\ \A q \in ProcSet: q # p => c_prev.res[q] = c.res[q]
            BY DEF c_prev, ConfigDomain
        <3>2. c.state = part' /\ \A q \in ProcSet: QAt(c, q)'
            BY DEF Q, QAt
        <3>3. ASSUME NEW q \in ProcSet, q # p PROVE QAt(c_prev, q)
            BY <3>3, <3>1, <3>2, <1>0 DEF QAt, TypeOK
        <3>4. pc'[p] \in {"SR", "S3"}
            BY <1>0 DEF TypeOK
        <3>5. QAt(c_prev, p)
            BY <3>1, <3>2, <3>4, <1>0 DEF QAt, PCtoOp, TypeOK
        <3>6. c_prev \in ConfigDomain
            BY DEF c_prev, ConfigDomain, ResDomain
        <3> QED
            BY <3>1, <3>2, <3>3, <3>5, <3>6 DEF Q, QAt
    <2>2. CASE c.res[p] = "BOT" 
        <3>1. c_prev = c 
            BY <2>2 DEF c_prev, ConfigDomain
        <3> QED
            BY <2>1, <3>1, EmptySeqEvolve DEF Q
    <2>3. CASE c.res[p] # "BOT"
        <3>1 Delta(c_prev, p, c)
            BY <2>1, <2>3, <1>0 DEF Delta, c_prev, ConfigDomain, ArgsOf, Q, S2, PCtoOp, TypeOK, Inv, StateDomain
        <3> QED
            BY <2>1, <3>1, SingleDeltaEvolve DEF Q
    <2> QED
        BY <2>1, <2>2, <2>3

  <1>5. ASSUME S3(p),
                NEW c \in ConfigDomain, 
                c \in Q'
        PROVE c \in Evolve(Q)
    <2> USE <1>5 DEF S3
    \* <2>1. /\ pc[p] = "S3"
    \*       /\ UNCHANGED <<part, u, arg>>
    \*       /\ \A q \in ProcSet : q # p =>
    \*            /\ pc'[q] = pc[q]
    \*            /\ ret'[q] = ret[q]
    \*       /\ (pc'[p] = "S1" \/ (pc'[p] = "SR" /\ ret'[p] = FALSE /\ part[u[p]] = u[p]))
    \*       BY <1>0 DEF TypeOK
    <2>1. c \in Q 
        <3>1. c.state = part' /\ \A q \in ProcSet: QAt(c, q)'
        BY DEF Q, QAt
        <3>2. \/ pc'[p] = "S1" /\ ret' = ret
              \/ pc'[p] = "SR" /\ ret'[p] = FALSE /\ part[u[p]] = u[p]
            BY <1>0 DEF TypeOK
        <3>3. QAt(c, p)
            BY <3>1, <3>2, <1>0 DEF QAt, PCtoOp, TypeOK
        <3>4. ASSUME NEW q \in ProcSet, q # p PROVE QAt(c, q)
            BY <3>4, <3>1, <1>0 DEF QAt, TypeOK
        <3> QED
            BY <3>1, <3>3, <3>4 DEF Q, QAt
    <2> QED
        BY <2>1, EmptySeqEvolve DEF Q
  <1> QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5 DEF InterAct, InterLines, Q

-----------------------------------------------------------------------------
(***************************************************************************)
(* Plausibility set lemma 2.4: If an intermediate-line action takes place, *)
(* then the new plausibility set Q' is a subset of the filtering of the    *)
(* evolution of Q, where the filtering is done for process p and the value *)
(* ret'[p] (which is the value to be returned by p).                       *)
(***************************************************************************)
ReturnProperty ==
  \A p \in ProcSet : ReturnAct(p) => (Q' \in SUBSET Filter(Evolve(Q), p, ret'[p]))

THEOREM ReturnLemma == ASpec => [][ReturnProperty]_varsP
  <1> SUFFICES ASSUME []TypeOK, []Inv
               PROVE  ASpec => [][ReturnProperty]_varsP
    BY ASpecImpliesSpec, SpecTypeOK, SpecInv
  <1> SUFFICES ASSUME ANext
               PROVE  ReturnProperty
    BY PTL DEF ASpec
  <1> SUFFICES ASSUME NEW p \in ProcSet,
                      ReturnAct(p)
               PROVE  Q' \in SUBSET Filter(Evolve(Q), p, ret'[p])
    BY DEF ReturnProperty
  <1>1. ASSUME UR(p),
               NEW c \in ConfigDomain,
               c \in Q'
        PROVE  c \in Filter(Evolve(Q), p, ret'[p])
    <2> USE <1>1 DEF UR
    <2>1. TypeOK
      BY PTL
    <2>2. /\ pc[p] = "UR" 
          /\ pc'[p] = "RM"
          /\ \A q \in ProcSet: q # p => pc'[q] = pc[q]
        BY <2>1 DEF TypeOK

    <2>3. c.state = part' /\ \A q \in ProcSet: QAt(c, q)' 
        BY DEF Q, QAt
    <2>4. c.op[p] = "BOT" /\ c.arg[p] = "BOT" /\ c.res[p] = "BOT"
          BY <2>2, <2>3 DEF QAt, PCtoOp
    <2> DEFINE c_prev == [c EXCEPT !.op = [c.op EXCEPT ![p] = "Unite"], 
                                   !.arg = [c.arg EXCEPT ![p] = arg[p]],
                                   !.res = [c.res EXCEPT ![p] = ret'[p]]]

    <2>5. c_prev \in Q
        <3>1. c_prev \in ConfigDomain
            BY <2>1 DEF c_prev, ConfigDomain, OpDomain, ResDomain, ArgDomain, RetDomain, TypeOK, OpNames
        <3>2. /\ c_prev.state = c.state
              /\ c_prev.op[p] = "Unite"
              /\ c_prev.arg[p] = arg[p]
              /\ c_prev.res[p] = ret'[p]
              /\ \A q \in ProcSet: q # p =>
                    /\ c_prev.op[q] = c.op[q]
                    /\ c_prev.arg[q] = c.arg[q]
                    /\ c_prev.res[q] = c.res[q]
            BY DEF c_prev, ConfigDomain
        <3>3. QAt(c_prev, p)
            BY <3>2 DEF QAt, PCtoOp
        <3>4. ASSUME NEW q \in ProcSet, q # p PROVE QAt(c_prev, q)
            BY <3>4, <3>2, <2>2, <2>3 DEF QAt 
        <3> QED 
            BY <3>1, <3>2, <3>3, <3>4, <2>3 DEF Q, QAt  
    <2> QED
        BY <2>4, <2>5, EvolveAndFilterFromUnfiltered DEF Q, c_prev

  <1>2. ASSUME FR(p),
               NEW c \in ConfigDomain,
               c \in Q'
        PROVE  c \in Filter(Evolve(Q), p, ret'[p])
    <2> USE <1>2 DEF FR
    <2>1. TypeOK
      BY PTL
    
    <2>2. /\ pc[p] = "FR" 
          /\ pc'[p] = "RM"
          /\ \A q \in ProcSet: q # p => pc'[q] = pc[q]
        BY <2>1 DEF TypeOK

    <2>3. c.state = part' /\ \A q \in ProcSet: QAt(c, q)' 
        BY DEF Q, QAt
    <2>4. c.op[p] = "BOT" /\ c.arg[p] = "BOT" /\ c.res[p] = "BOT"
          BY <2>2, <2>3 DEF QAt, PCtoOp
    <2> DEFINE c_prev == [c EXCEPT !.op = [c.op EXCEPT ![p] = "Find"], 
                                   !.arg = [c.arg EXCEPT ![p] = arg[p]],
                                   !.res = [c.res EXCEPT ![p] = ret'[p]]]

    <2>5. c_prev \in Q
        <3>1. c_prev \in ConfigDomain
            BY <2>1 DEF c_prev, ConfigDomain, OpDomain, ResDomain, ArgDomain, RetDomain, TypeOK, OpNames
        <3>2. /\ c_prev.state = c.state
              /\ c_prev.op[p] = "Find"
              /\ c_prev.arg[p] = arg[p]
              /\ c_prev.res[p] = ret'[p]
              /\ \A q \in ProcSet: q # p =>
                    /\ c_prev.op[q] = c.op[q]
                    /\ c_prev.arg[q] = c.arg[q]
                    /\ c_prev.res[q] = c.res[q]
            BY DEF c_prev, ConfigDomain
        <3>3. QAt(c_prev, p)
            BY <3>2 DEF QAt, PCtoOp
        <3>4. ASSUME NEW q \in ProcSet, q # p PROVE QAt(c_prev, q)
            BY <3>4, <3>2, <2>2, <2>3 DEF QAt 
        <3> QED 
            BY <3>1, <3>2, <3>3, <3>4, <2>3 DEF Q, QAt  
    <2> QED
        BY <2>4, <2>5, EvolveAndFilterFromUnfiltered DEF Q, c_prev

  <1>3. ASSUME SR(p),
               NEW c \in ConfigDomain,
               c \in Q'
        PROVE  c \in Filter(Evolve(Q), p, ret'[p])
    <2> USE <1>3 DEF SR
    <2>1. TypeOK
      BY PTL
    <2>2. /\ pc[p] = "SR" 
          /\ pc'[p] = "RM"
          /\ \A q \in ProcSet: q # p => pc'[q] = pc[q]
        BY <2>1 DEF TypeOK

    <2>3. c.state = part' /\ \A q \in ProcSet: QAt(c, q)' 
        BY DEF Q, QAt
    <2>4. c.op[p] = "BOT" /\ c.arg[p] = "BOT" /\ c.res[p] = "BOT"
          BY <2>2, <2>3 DEF QAt, PCtoOp
    <2> DEFINE c_prev == [c EXCEPT !.op = [c.op EXCEPT ![p] = "SameSet"], 
                                   !.arg = [c.arg EXCEPT ![p] = arg[p]],
                                   !.res = [c.res EXCEPT ![p] = ret'[p]]]

    <2>5. c_prev \in Q
        <3>1. c_prev \in ConfigDomain
            BY <2>1 DEF c_prev, ConfigDomain, OpDomain, ResDomain, ArgDomain, RetDomain, TypeOK, OpNames
        <3>2. /\ c_prev.state = c.state
              /\ c_prev.op[p] = "SameSet"
              /\ c_prev.arg[p] = arg[p]
              /\ c_prev.res[p] = ret'[p]
              /\ \A q \in ProcSet: q # p =>
                    /\ c_prev.op[q] = c.op[q]
                    /\ c_prev.arg[q] = c.arg[q]
                    /\ c_prev.res[q] = c.res[q]
            BY DEF c_prev, ConfigDomain
        <3>3. QAt(c_prev, p)
            BY <3>2 DEF QAt, PCtoOp
        <3>4. ASSUME NEW q \in ProcSet, q # p PROVE QAt(c_prev, q)
            BY <3>4, <3>2, <2>2, <2>3 DEF QAt 
        <3> QED 
            BY <3>1, <3>2, <3>3, <3>4, <2>3 DEF Q, QAt  
    <2> QED
        BY <2>4, <2>5, EvolveAndFilterFromUnfiltered DEF Q, c_prev
  <1> QED
    BY <1>1, <1>2, <1>3 DEF ReturnAct, ReturnLines, Q
-----------------------------------------------------------------------------
(***************************************************************************)
(* Plausibility set lemma 2.5: If no variable changes, Q remains the same. *)
(***************************************************************************)
THEOREM UnchangedLemma == UNCHANGED varsP => Q' = Q
  BY DEF varsP, vars, implvars, Q

-----------------------------------------------------------------------------
(***************************************************************************)
(* Plausibility set theorem 2: Q is a subset of P is an invariant of ASpec.*)
(***************************************************************************)
(* This theorem follows automatically from the five lemmas above.          *)
(***************************************************************************)
THEOREM PlausSetThm2 == ASpec => [](Q \in SUBSET P)
  <1> SUFFICES ASSUME [][InvocProperty]_varsP,
                      [][InterProperty]_varsP,
                      [][ReturnProperty]_varsP
               PROVE  ASpec => [](Q \in SUBSET P)
    BY InvocLemma, InterLemma, ReturnLemma
  <1>1. AInit => Q \in SUBSET P 
    BY PlausSetInitLemma
  <1>2. (Q \in SUBSET P) /\ [ANext]_varsP => (Q \in SUBSET P)'
    <2>1. ASSUME Q \in SUBSET P,
                 NEW p \in ProcSet, 
                 InvocAct(p),
                 ~(UNCHANGED varsP),
                 P' = Evolve(Invoke(P, p, PCtoOp(pc'[p]), arg'[p]))
          PROVE  (Q \in SUBSET P)'
      <3>1. [InvocProperty]_varsP 
        BY PTL
      <3>2. Invoke(Q, p, PCtoOp(pc'[p]), arg'[p]) \in SUBSET Invoke(P, p, PCtoOp(pc'[p]), arg'[p]) 
        BY <2>1, InvokeForSubset
      <3> SUFFICES Q' \in SUBSET Evolve(Invoke(P, p, PCtoOp(pc'[p]), arg'[p])) 
        BY <2>1
      <3> SUFFICES Q' \in SUBSET Evolve(Invoke(Q, p, PCtoOp(pc'[p]), arg'[p])) 
        BY <3>2, EvolveForSubset
      <3> QED 
        BY <2>1, <3>1 DEF InvocProperty
    <2>2. ASSUME Q \in SUBSET P,
                 NEW p \in ProcSet, 
                 InterAct(p),
                 ~(UNCHANGED varsP),
                 P' = Evolve(P)
          PROVE  (Q \in SUBSET P)'
      <3>1. [InterProperty]_varsP 
        BY PTL
      <3> SUFFICES Q' \in SUBSET Evolve(P) 
        BY <2>2
      <3> SUFFICES Q' \in SUBSET Evolve(Q) 
        BY <2>2, Zenon, EvolveForSubset
      <3> QED 
        BY <2>2, <3>1 DEF InterProperty
    <2>3. ASSUME Q \in SUBSET P,
                 NEW p \in ProcSet, 
                 ReturnAct(p),
                 ~(UNCHANGED varsP),
                 P' = Filter(Evolve(P), p, ret'[p])
          PROVE  (Q \in SUBSET P)'
      <3>1. [ReturnProperty]_varsP
        BY PTL
      <3>2. Evolve(Q) \in SUBSET Evolve(P)
        BY <2>3, EvolveForSubset
      <3> SUFFICES Q' \in SUBSET Filter(Evolve(P), p, ret'[p])
        BY <2>3
      <3> SUFFICES Q' \in SUBSET Filter(Evolve(Q), p, ret'[p])
        BY <3>2, FilterForSubset
      <3> QED
        BY <2>3, <3>1 DEF ReturnProperty
    <2>4. ASSUME Q \in SUBSET P,
                 UNCHANGED varsP
          PROVE  (Q \in SUBSET P)'
      BY UnchangedLemma, <2>4 DEF varsP
    <2> QED
      BY <2>1, <2>2, <2>3, <2>4 DEF ANext
  <1> QED
    BY <1>1, <1>2, PTL DEF ASpec

-----------------------------------------------------------------------------
(***************************************************************************)
(* META-CONFIGURATION TRACKING LINEARIZABILITY INVARIANT                   *)
(***************************************************************************)
THEOREM Linearizability == ASpec => [](P # {})
  <1> SUFFICES ASSUME [](Q # {}), [](Q \in SUBSET P)
               PROVE  ASpec => [](P # {})
    BY ASpecImpliesSpec, PlausSetThm1, PlausSetThm2
  <1>1. AInit => P # {}
    <2>1. Q # {} /\ Q \in SUBSET P BY PTL
    <2> QED BY <2>1
  <1>2. [ANext]_varsP => (P # {})'
    <2>1. (Q # {})' /\ (Q \in SUBSET P)' BY PTL
    <2> QED BY <2>1
  <1> QED
    BY <1>1, <1>2, PTL DEF ASpec

=============================================================================
