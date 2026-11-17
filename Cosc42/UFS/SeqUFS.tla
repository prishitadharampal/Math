---------------------------- MODULE SeqUFS ----------------------------
(***************************************************************************)
(* This module defines the UFS object type, in a way that is               *)
(* compatible with meta-configuration tracking.                            *)
(***************************************************************************)
(* Author: Evan Lucca                                                      *)
(* Last updated: 2026-08-30                                                *)
(***************************************************************************)
EXTENDS Integers

CONSTANTS 
  ProcSet,  (* Symbolic set of processes *)
  N         (* Number of elements *)

NodeSet == 1..N
(***************************************************************************)
(* Operations and arguments                                                *)
(***************************************************************************)
OpNames == {"Unite", "Find", "SameSet"}
                
ArgsOf(op) ==
  CASE op = "Unite"  -> NodeSet \X NodeSet
    [] op = "Find" -> NodeSet 
    [] op = "SameSet" -> NodeSet \X NodeSet
    
RetsOf(op) ==
  CASE op = "Unite"  -> {"ACK"}
    [] op = "Find" -> NodeSet
    [] op = "SameSet" -> BOOLEAN 

(***************************************************************************)
(* State domain and initial state                                          *)
(***************************************************************************)
StateDomain == {A \in [NodeSet -> NodeSet]: \A i \in NodeSet: A[A[i]] = A[i]}
InitState == [i \in NodeSet |-> i]

(***************************************************************************)
(* Transition relation                                                     *)
(***************************************************************************)
(* Delta(c, p, d) is true if process p's operation changes configuration c *)
(* to configuration d.                                                     *)
(***************************************************************************)
UFSUnite(old, a, b, new) == /\ old \in StateDomain /\ new \in StateDomain
                            /\ a \in NodeSet /\ b \in NodeSet
                            /\ \/ new = [i \in NodeSet |-> IF old[i] = old[a] THEN old[b] ELSE old[i]]
                               \/ new = [i \in NodeSet |-> IF old[i] = old[b] THEN old[a] ELSE old[i]]

Delta(c, p, d) == 
  CASE (c.op[p] = "Unite")
    -> /\ c.arg[p] \in ArgsOf("Unite")
       /\ c.res[p] = "BOT"
       /\ UFSUnite(c.state, c.arg[p][1], c.arg[p][2], d.state)
       /\ d.op     = c.op
       /\ d.arg    = c.arg
       /\ d.res    = [c.res EXCEPT ![p] = "ACK"]
    [] (c.op[p] = "Find")
    -> /\ c.arg[p] \in ArgsOf("Find")
       /\ c.res[p] = "BOT"
       /\ d.state  = c.state
       /\ d.op     = c.op
       /\ d.arg    = c.arg
       /\ d.res    = [c.res EXCEPT ![p] = c.state[c.arg[p]]]
    [] (c.op[p] = "SameSet")
    -> /\ c.arg[p] \in ArgsOf("SameSet")
       /\ c.res[p] = "BOT"
       /\ d.state  = c.state
       /\ d.op     = c.op
       /\ d.arg    = c.arg
       /\ d.res    = [c.res EXCEPT ![p] = (c.state[c.arg[p][1]] = c.state[c.arg[p][2]])]
    [] OTHER 
    -> FALSE

=============================================================================