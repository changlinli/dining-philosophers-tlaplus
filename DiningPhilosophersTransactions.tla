------------------- MODULE DiningPhilosophersTransactions -------------------

EXTENDS FiniteSets, Integers

CONSTANT NumOfPhilosophers

VARIABLES philosopherStates, philosopherToForks

vars == <<philosopherStates, philosopherToForks>>

Philosophers == 1..NumOfPhilosophers

Forks == 1..NumOfPhilosophers

NextFork(fork) == IF fork < NumOfPhilosophers THEN fork + 1 ELSE (fork + 1) % NumOfPhilosophers

PhilosophersHoldingFork(fork) == { p \in Philosophers : fork \in philosopherToForks[p] }

Range(f) == { f[x] : x \in DOMAIN f }

ForkIsAvailable(fork) == fork \notin UNION Range(philosopherToForks)

TypeOK ==
    /\ Cardinality(Forks) = NumOfPhilosophers
    /\ philosopherStates \in [Philosophers -> {"thinking", "waitingForFork", "eating"}]
    /\ \A p \in Philosophers :
        \/ philosopherToForks[p] = {}
        \/ philosopherToForks[p] = {p}
        \/ philosopherToForks[p] = {NextFork(p)}
        \/ philosopherToForks[p] = {p, NextFork(p)}
    /\ \A f \in Forks : Cardinality(PhilosophersHoldingFork(f)) <= 1
    /\ \A f \in Forks : ForkIsAvailable(f) => PhilosophersHoldingFork(f) = {}
    /\ \A p \in Philosophers :
        /\ philosopherStates[p] = "thinking" => philosopherToForks[p] = {}
        /\ philosopherStates[p] = "waitingForFork" => philosopherToForks[p] = {}
        /\ philosopherStates[p] = "eating" => Cardinality(philosopherToForks[p]) = 2
        
Init ==
    /\ philosopherStates = [p \in Philosophers |-> "thinking"]
    /\ philosopherToForks = [f \in Philosophers |-> {}]

WaitForFork(p) ==
    /\ philosopherStates[p] = "thinking"
    /\ philosopherStates' = [philosopherStates EXCEPT ![p] = "waitingForFork"]
    /\ UNCHANGED philosopherToForks
    
PickupForks(p) ==
    /\ philosopherStates[p] = ""
        
PickUpFirstFork(p) ==
    /\ philosopherStates[p] = "waitingForFirstFork"
    /\
        \/ IF ForkIsAvailable(p) THEN
            philosopherToForks' = [philosopherToForks EXCEPT ![p] = {p}] ELSE
            FALSE
        \/ IF ForkIsAvailable(NextFork(p)) THEN
            philosopherToForks' = [philosopherToForks EXCEPT ![p] = {NextFork(p)}] ELSE
            FALSE
    /\ philosopherStates' = [philosopherStates EXCEPT ![p] = "waitingForSecondFork"]
        
PickUpSecondFork(p) ==
    /\ philosopherStates[p] = "waitingForSecondFork"
    /\
        \/ IF ForkIsAvailable(p) THEN
            philosopherToForks' = [philosopherToForks EXCEPT ![p] = philosopherToForks[p] \union {p}] ELSE
            FALSE
        \/ IF ForkIsAvailable(NextFork(p)) THEN
            philosopherToForks' = [philosopherToForks EXCEPT ![p] = philosopherToForks[p] \union {NextFork(p)}] ELSE
            FALSE
    /\ philosopherStates' = [philosopherStates EXCEPT ![p] = "eating"]

SetDownFirstFork(p) ==
    /\ philosopherStates[p] = "eating"
    /\ \E f \in philosopherToForks[p] : 
        philosopherToForks' = [philosopherToForks EXCEPT ![p] = philosopherToForks[p] \ {f}]
    /\ philosopherStates' = [philosopherStates EXCEPT ![p] = "setDownFirstFork"]

SetDownSecondFork(p) ==
    /\ philosopherStates[p] = "setDownFirstFork"
    /\ philosopherToForks' = [philosopherToForks EXCEPT ![p] = {}]
    /\ philosopherStates' = [philosopherStates EXCEPT ![p] = "thinking"]
    
Next == \E p \in Philosophers :
    \/ WaitForFork(p)
    \/ PickUpFirstFork(p)
    \/ PickUpSecondFork(p)
    \/ SetDownFirstFork(p)
    \/ SetDownSecondFork(p)

=============================================================================
\* Modification History
\* Last modified Tue Aug 13 15:24:31 EDT 2019 by changlin
\* Created Tue Aug 13 14:37:49 EDT 2019 by changlin
