------------------------------ MODULE MCS ------------------------------
(***************************************************************************)
(* The MCS queue lock for DSM and CC machines:                             *)
(* Variables and initialization:                                           *)
(*   A node is a structure that can store a single pointer or nil.         *)
(*   For each process p in Pi, there are variables:                        *)
(*     mynode_pi : a unique node pointer                                   *)
(*     mypred_pi : an arbitrarily initialized node pointer                 *)
(*     go_pi     : a unique boolean pointer                                *)
(*     nxtgo_pi  : an arbitrarily initialized boolean pointer              *)
(*     TAIL is a pointer to a node, initially a special anchor node        *)
(* with *TAIL = true.                                                      *)
(*                                                                         *)
(* Try(p):                                                                 *)
(*   T1:  *mynode_p <- nil                                                 *)
(*   T2:  *go_p <- false                                                   *)
(*   T3:  mypred_p <- FAS(TAIL, mynode_p)                                  *)
(*   T4:  if FAS( *mypred_p, go_p) = nil then                              *)
(*   T5:      await *go_p                                                  *)
(*                                                                         *)
(* Exit(p):                                                                *)
(*   E1:  nxtgo_p <- FAS( *mynode_p, nonnil).                              *)
(*          -- nonnil can be any value not equal to nil, e.g., go_p        *)
(*   E2:  if nxtgo_p # nil then *nxtgo_p  <- true                          *)
(*   E3:  mynode_p <- mypred_p                                             *)
(***************************************************************************)

EXTENDS Naturals

CONSTANTS ProcSet, Anchor, NIL, NONNIL

ASSUME ConstAssump ==
  /\ Anchor \notin ProcSet
  /\ NIL \notin ProcSet
  /\ NONNIL \notin ProcSet
  /\ NIL # NONNIL

Nodes   == ProcSet \cup {Anchor}
MemVals == ProcSet \cup {NIL, NONNIL}  

VARIABLES mem,      \* mem[n]   : contents of node n
          goVal,   
          tail,     
          mynode,  
          mypred,
          nxtgo,
          pc

vars == <<mem, goVal, tail, mynode, mypred, nxtgo, pc>> 

Lines == {"RM", "T1", "T2", "T3", "T4", "T5", "E1", "E2", "E3"}

Init ==
  /\ mem \in [Nodes -> MemVals]
  /\ mem[Anchor] = NONNIL
  /\ goVal \in [ProcSet -> BOOLEAN]
  /\ tail = Anchor
  /\ mynode = [p \in ProcSet |-> p]
  /\ mypred \in [ProcSet -> Nodes]
  /\ nxtgo \in [ProcSet -> MemVals]
  /\ pc = [p \in ProcSet |-> "RM"]


Try(p) ==
  /\ pc[p] = "RM"
  /\ pc' = [pc EXCEPT ![p] = "T1"]
  /\ UNCHANGED <<mem, goVal, tail, mynode, mypred, nxtgo>>


T1(p) ==
  /\ pc[p] = "T1"
  /\ mem' = [mem EXCEPT ![mynode[p]] = NIL]
  /\ pc' = [pc EXCEPT ![p] = "T2"]
  /\ UNCHANGED <<goVal, tail, mynode, mypred, nxtgo>>


T2(p) ==
  /\ pc[p] = "T2"
  /\ goVal' = [goVal EXCEPT ![p] = FALSE]
  /\ pc' = [pc EXCEPT ![p] = "T3"]
  /\ UNCHANGED <<mem, tail, mynode, mypred, nxtgo>>


T3(p) ==
  /\ pc[p] = "T3"
  /\ mypred' = [mypred EXCEPT ![p] = tail]
  /\ tail' = mynode[p]
  /\ pc' = [pc EXCEPT ![p] = "T4"]
  /\ UNCHANGED <<mem, goVal, mynode, nxtgo>>


T4(p) ==
  /\ pc[p] = "T4"
  /\ mem' = [mem EXCEPT ![mypred[p]] = p]
  /\ pc' = [pc EXCEPT ![p] = IF mem[mypred[p]] = NIL THEN "T5" ELSE "E1"]
  /\ UNCHANGED <<goVal, tail, mynode, mypred, nxtgo>>


T5(p) ==
  /\ pc[p] = "T5"
  /\ goVal[p]
  /\ pc' = [pc EXCEPT ![p] = "E1"]
  /\ UNCHANGED <<mem, goVal, tail, mynode, mypred, nxtgo>>


E1(p) ==
  /\ pc[p] = "E1"
  /\ nxtgo' = [nxtgo EXCEPT ![p] = mem[mynode[p]]]
  /\ mem' = [mem EXCEPT ![mynode[p]] = NONNIL]
  /\ pc' = [pc EXCEPT ![p] = "E2"]
  /\ UNCHANGED <<goVal, tail, mynode, mypred>>


E2(p) ==
  /\ pc[p] = "E2"
  /\ goVal' = IF nxtgo[p] # NIL THEN [goVal EXCEPT ![nxtgo[p]] = TRUE] ELSE goVal
  /\ pc' = [pc EXCEPT ![p] = "E3"]
  /\ UNCHANGED <<mem, tail, mynode, mypred, nxtgo>>


E3(p) ==
  /\ pc[p] = "E3"
  /\ mynode' = [mynode EXCEPT ![p] = mypred[p]]
  /\ pc' = [pc EXCEPT ![p] = "RM"]
  /\ UNCHANGED <<mem, goVal, tail, mypred, nxtgo>>

(* Line actions for process p *)
LineActs(p) == {Try(p), T1(p), T2(p), T3(p), T4(p), T5(p), E1(p), E2(p), E3(p)}

Next == \E p \in ProcSet :
          \/ Try(p) \/ T1(p) \/ T2(p) \/ T3(p) \/ T4(p) \/ T5(p) \/ E1(p) \/ E2(p) \/ E3(p)

Spec == Init /\ [][Next]_vars

Mutex == \A p, q \in ProcSet : pc[p] = "E1" /\ pc[q] = "E1" => p = q


Fair(A) == <>[](ENABLED <<A>>_vars) => []<><<A>>_vars

Fairness == \A p \in ProcSet :
              /\ Fair(T1(p)) /\ Fair(T2(p)) /\ Fair(T3(p))
              /\ Fair(T4(p)) /\ Fair(T5(p)) /\ Fair(E1(p)) 
              /\ Fair(E2(p)) /\ Fair(E3(p))

FairSpec == Spec /\ Fairness

StarvationFree == \A p \in ProcSet : [](pc[p] = "T1" => <>(pc[p] = "E1"))
=============================================================================
