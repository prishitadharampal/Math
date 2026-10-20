---- MODULE problem3 ----
EXTENDS TLC, FiniteSets, Integers

VARIABLES  boatman, left, right

Items == {"tiger", "goat", "hay"}

Init == 
    /\ boatman = "left"
    /\ left = Items
    /\ right = {}

TypeOK == 
    /\ boatman \in {"left", "right"}
    /\ left \in SUBSET Items
    /\ right \in SUBSET Items

BanksOK == 
    /\ left \cap right = {}
    /\ left \cup right = Items

Dangerous(bank) == 
    \/ {"tiger", "goat"} \subseteq bank
    \/ {"hay", "goat"} \subseteq bank

SafeBank(bank, side) == 
    ~(Dangerous(bank) /\ boatman /= side)

Safe == 
    /\ SafeBank(left, "left")
    /\ SafeBank(right, "right")

Cross(start, start_side, end, end_side, cargo) == 
    /\ boatman = start_side
    /\ boatman' = end_side
    /\ cargo \subseteq start 
    /\ Cardinality(cargo) =< 1
    /\ start' = start \ cargo 
    /\ end' = end \cup cargo 
    /\ Safe' 

Next == 
    \/ \E cargo \in SUBSET left: 
        Cross(left, "left", right, "right", cargo)
    \/ \E cargo \in SUBSET right: 
        Cross(right, "right", left, "left", cargo)

Goal == 
    /\ boatman = "right"
    /\ right = Items
    /\ left = {}

NotGoal == ~Goal
====