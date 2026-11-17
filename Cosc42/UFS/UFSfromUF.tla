----------------------- MODULE UFSfromUF -----------------------

\* Shared Memory Object: Union-find object, represented as idempotent function
\* ALGORITHM:

\*         Find_p(c):
\*     F1:    ret = part(c)
\*     FR:    Return ret

\*         Unite_p(c, d):
\*     U1:    ret = Unite(c, d)
\*     UR:    return ret


\*         SameSet_p(c, d):
\*     S1:     u = c; v = d; u = Find(u) 
\*     S2:     v = Find(v); if u = v then ret = True; goto SR
\*     S3:     w = Find(u)
\*             if u = w then ret = False; goto SR else goto S1
\*     SR:     return ret

\* part is an idempotent function


(***************************************************************************)
(* This module defines the RWCas implementation of the read-write          *)
(* register type.                                                          *)
(***************************************************************************)
(* Author: Ugur Y. Yavuz (Boston University)                               *)
(* Last updated: 2025-07-24                                                *)
(***************************************************************************)

EXTENDS SeqUFS

(***************************************************************************)
(* RWCas implementation                                                    *)
(***************************************************************************)
VARIABLES part, u, v, w, arg, ret, pc
implvars == <<part, u, v, w>>

\* Applies the shared-memory update to the UnionFind object when Unite(x, y) is called. 
UFUniteShared(x, y)      ==  /\ part \in StateDomain /\ x \in NodeSet /\ y \in NodeSet
                             /\ \/ part' = [i \in NodeSet |-> IF part[i] = part[x] THEN part[y] ELSE part[i]]
                                \/ part' = [i \in NodeSet |-> IF part[i] = part[y] THEN part[x] ELSE part[i]]
          

F1(p) == /\ pc[p] = "F1"
         /\ pc' = [pc EXCEPT ![p] = "FR"]
         /\ ret' = [ret EXCEPT ![p] = part[arg[p]]]
         /\ UNCHANGED <<part, u, v, w, arg>>
         
FR(p) == /\ pc[p] = "FR"
         /\ pc' = [pc EXCEPT ![p] = "RM"]
         /\ UNCHANGED <<part, u, v, w, arg, ret>>
         
U1(p) == /\ pc[p] = "U1"
         /\ pc' = [pc EXCEPT ![p] = "UR"]
         /\ UFUniteShared(arg[p][1], arg[p][2]) 
         /\ ret' = [ret EXCEPT ![p] = "ACK"]
         /\ UNCHANGED <<u, v, w, arg>>

UR(p) == /\ pc[p] = "UR"
         /\ pc' = [pc EXCEPT ![p] = "RM"]
         /\ UNCHANGED <<part, u, v, w, arg, ret>>

S1(p) == /\ pc[p] = "S1"
         /\ pc' = [pc EXCEPT ![p] = "S2"]
         /\ u' = [u EXCEPT ![p] = part[arg[p][1]]]
         /\ v' = [v EXCEPT ![p] = arg[p][2]]
         /\ UNCHANGED <<part, w, arg, ret>>

S2(p) == /\ pc[p] = "S2"
         /\ v' = [v EXCEPT ![p] = part[v[p]]]
         /\ IF u'[p] = v'[p]
                THEN    /\ ret' = [ret EXCEPT ![p] = TRUE]
                        /\ pc' = [pc EXCEPT ![p] = "SR"]
                ELSE    /\ ret' = ret
                        /\ pc' = [pc EXCEPT ![p] = "S3"]
         /\ UNCHANGED <<part, u, w, arg>>

S3(p) == /\ pc[p] = "S3"
         /\ w' = [w EXCEPT ![p] = part[u[p]]]
         /\ IF u'[p] = w'[p]
                THEN    /\ ret' = [ret EXCEPT ![p] = FALSE]
                        /\ pc' = [pc EXCEPT ![p] = "SR"]
                ELSE    /\ ret' = ret
                        /\ pc' = [pc EXCEPT ![p] = "S1"]
         /\ UNCHANGED <<part, u, v, arg>>

SR(p) == /\ pc[p] = "SR"
         /\ pc' = [pc EXCEPT ![p] = "RM"]
         /\ UNCHANGED <<part, u, v, w, arg, ret>>

ImplInit == /\ part = [i \in NodeSet |-> i]
            /\ u \in [ProcSet -> NodeSet]
            /\ v \in [ProcSet -> NodeSet]
            /\ w \in [ProcSet -> NodeSet]
-----------------------------------------------------------------------------
(***************************************************************************)
(* Correspondence between operations and line identifiers                  *)
(***************************************************************************)

(* First line of each operation *)
OpToFirstLine(op) == 
  CASE op = "Unite"  -> "U1"
    [] op = "Find" -> "F1"
    [] op = "SameSet" -> "S1"

(* Program counter to operation mapping *)
PCtoOp(pcp) == 
  CASE pcp \in {"U1", "UR"} -> "Unite"
    [] pcp \in {"F1", "FR"} -> "Find"
    [] pcp \in {"S1", "S2", "S3", "SR"} -> "SameSet"
    [] pcp = "RM" -> "BOT"

(* Line identifiers *)
LineIDs == {"RM", "U1", "UR", "F1", "FR", "S1", "S2", "S3", "SR"}

(* Intermediate line actions for given process *)
InterLines(p) == {U1(p), F1(p), S1(p), S2(p), S3(p)}

(* Return line actions for given process *)
ReturnLines(p) == {UR(p), FR(p), SR(p)}

        

=============================================================================
\* Modification History
\* Last modified Thu Jan 15 10:42:49 EST 2026 by elucca
\* Created Tue Dec 30 12:53:36 EST 2025 by elucca
