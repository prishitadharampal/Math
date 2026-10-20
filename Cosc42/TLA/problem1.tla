---- MODULE problem1 ----
EXTENDS TLC, Integers

VARIABLES interested, pc, turn 

processes == {0, 1}

TypeOK == 
    /\ interested \in [processes-> BOOLEAN]
    /\ turn \in processes
    /\ pc \in [processes -> {"T1", "T2", "T3A", "T3B", "E1"}]

Init == 
    /\ interested = [i \in processes |-> FALSE]
    /\ turn \in processes
    /\ pc = [p \in processes |-> "T1"]

T1(p) == 
    /\ pc[p] = "T1"
    /\ pc' = [pc EXCEPT ![p] = "T2"]
    /\ interested' = [interested EXCEPT ![p] = TRUE]
    /\ UNCHANGED turn

T2(p) == 
    /\ pc[p] = "T2"
    /\ pc' = [pc EXCEPT ![p] = "T3A"]
    /\ turn' = 1-p
    /\ UNCHANGED interested

T3A(p) == 
    /\ pc[p] = "T3A" 
    /\ pc' = [pc EXCEPT ![p] = 
        IF turn = p THEN "E1" 
        ELSE "T3B"]
    /\ UNCHANGED <<turn, interested>>

T3B(p) == 
    /\ pc[p] = "T3B" 
    /\ pc' = [pc EXCEPT ![p] = 
        IF interested[1-p] THEN "T3A" 
        ELSE "E1"]
    /\ UNCHANGED <<turn, interested>>

E1(p) == 
    /\ pc[p] = "E1" 
    /\ pc' = [pc EXCEPT ![p] = "T1"]
    /\ interested' = [interested EXCEPT ![p] = FALSE]
    /\ UNCHANGED turn


Mutex == 
    ~(pc[1] = "E1" /\ pc[0] = "E1")

Next == 
    \E p \in processes: 
        \/ T1(p)
        \/ T2(p)
        \/ T3A(p)
        \/ T3B(p)
        \/ E1(p)

====